local gdl = {}

--[[

   Generalized Distributive Law

   A factor maps from the cartesian product of several "variables" (with finite
   cardinality) to values. Factors can be called as functions with variable
   assignments in the order given in the domain. Factors contain the following
   sub-tables:

   - domain: an array of tuples {name, {value1, value2}} for each variable
   - raw: an array with the raw values

   The operations on factors are defined for commutative semirings, here
   just called semirings for shortness.
   
--]]

----------------------
-- Helper Functions --
----------------------

local index2arguments = function(domain, index)
   local values = {}
   local remain = index-1
   for i, variable in ipairs(domain) do
      local var_values = variable[2]
      local card = #var_values
      local pos = remain % card
      remain = (remain-pos) / card
      values[i] = var_values[pos+1]
   end
   return values
end

local findindex = function(array, entry)
   for i, v in ipairs(array) do if v == entry then return i end end
   return 0
end

-- the metatable for factors
local factor_mt = {
   __call = function(self, ...)
      local assign = {...}
      if #arg ~= #self then error("not enough arguments") end
      local pos = 1 -- absolute position
      local running_card = 1
      for j,variable in ipairs(self.domain) do
         local val = assign[j]
         local values = variable[2]
         local card = #values
         local var_pos = 0
         for i=1,card do if values[i] == val then var_pos = i; break end end
         if var_pos == 0 then error("argument not found") end
         pos = pos + ((var_pos-1) * running_card)
         running_card = running_card * card
      end
      return self.raw[pos]
   end,
   __tostring = function(self)
      local out = {}
      local var_names = '('
      for _,var in ipairs(self.domain) do var_names = var_names .. tostring(var[1]) .. ', ' end
      out[#out+1] = string.sub(var_names, 1, -3) .. ')'
      for i=1,#self.raw do
         local values = index2arguments(self.domain, i)
         local vs = '\n('
         for _,v in ipairs(values) do vs = vs .. tostring(v) .. ', ' end
         out[#out+1] = string.sub(vs, 1, -3) .. ') -> ' .. tostring(self.raw[i])
      end
      return table.concat(out)
   end
}

-----------------------
-- Factor Operations --
-----------------------

-- Returns a new semiring. Invmul can be left as nil. But then, the factor cannot be normalized.
gdl.semiring = function(add, zero, mul, one, invmul)
   return {add = add, zero = zero, mul = mul, one = one, invmul = invmul}
end

-- Create a factor from the given function and application domain
gdl.create_factor = function(func, domain)
   local size = 1
   for _, var in ipairs(domain) do size = size * #var[2] end
   local raw = {}
   for i = 1,size do raw[i] = func(unpack(index2arguments(domain, i))) end
   local f = { domain = domain, raw = raw }
   setmetatable(f, factor_mt)
   return f
end

-- Create a factor with the 1-element at every position
gdl.create_unity_factor = function(ring, domain)
   local size = 1
   for _,var in ipairs(domain) do size = size * #var[2] end
   local raw = {}
   for i = 1,size do raw[i] = ring.one end
   local u = {domain = domain, raw = raw}
   setmetatable(u, factor_mt)
   return u
end

-- Marginalize out the dimensions not in the retain array
gdl.marginalize = function(ring, f, retain)
   local size = 1
   local domain = {} -- the new domain
   local varcount = 0
   local cards = {}
   local strides = {} -- strides of the retained domains in the original raw array
   local running_stride = 1
   local pattern = {0} -- pattern for summation
   local pattern_size = 1

   -- compute the pattern and the strides
   for k,var in ipairs(f.domain) do
      local var_name = var[1]
      local var_values = var[2]
      local var_card = #var_values
      if findindex(retain, var_name) ~= 0 then
         -- keep the variable
         varcount = varcount + 1
         domain[varcount] = {var_name, var_values}
         cards[varcount] = var_card
         strides[varcount] = running_stride
         size = size * var_card
      else
         -- marginalize the var_ension out
         local ps = pattern_size
         for j=1,ps do
            for i=2,var_card do
               pattern_size = pattern_size + 1
               pattern[pattern_size] = pattern[j] + (running_stride * (i - 1))
            end
         end
      end
      running_stride = running_stride * var_card
   end

   -- marginalize the content via summation
   local raw = {}
   local fraw = f.raw
   local dimension_indices = {0}
   for i=2,varcount do dimension_indices[i] = 1 end
   local begin = 1 - strides[1] -- the index where we begin to sum up the pattern
   for i=1,size do
      for k,di in ipairs(dimension_indices) do
         local card = cards[k]
         if di < card then
            dimension_indices[k] = di+1
            begin = begin + strides[k]
            break
         else
            dimension_indices[k] = 1
            begin = begin - (strides[k] * (card-1))
         end
      end
      local v = fraw[begin] -- pattern[1] is always zero
      for j=2,pattern_size do
         v = ring.add(v, fraw[begin+pattern[j]])
      end
      raw[i] = v
   end

   local m = {domain = domain, raw = raw}
   setmetatable(m, factor_mt)
   return m
end

-- Join the given factors (any number)
gdl.join = function(ring, ...)
   local factors = {...}
   local factors_size = #factors

   -- join the domains
   local size = 1
   local domain = {}
   local cards = {}
   local varnames = {}
   local domain_size = 0
   for i,factor in ipairs(factors) do
      for _,var in ipairs(factor.domain) do
         local varname = var[1]
         if findindex(varnames, varname) == 0 then
            local varcard = #var[2]
            domain_size = domain_size + 1
            domain[domain_size] = var
            varnames[domain_size] = varname
            cards[domain_size] = varcard
            size = size * varcard
         end
      end
   end
   
   -- compute the strides to map from the global index into the local one
   local strides_size = factors_size * domain_size
   local strides = {}
   for i=1,strides_size do strides[i] = 0 end
   for j,factor in ipairs(factors) do
      local current_stride = 1
      for _,variable in ipairs(factor.domain) do
         local varname = variable[1]
         local varvalues = variable[2]
         local varindex = findindex(varnames, varname) - 1
         strides[(varindex * factors_size) + j] = current_stride
         current_stride = current_stride * #varvalues
      end
   end
   
   -- join the content
   local raw = {}
   local one = ring.one
   local factor_indices = {} -- indices in the raw arrays of the factors
   local var_indices = {0} -- indices in the dimensions of the joint domain
   for i=1,factors_size do factor_indices[i] = 1 - strides[i] end
   for i=2,domain_size do var_indices[i] = 1 end
   for i=1,size do
      for k,di in ipairs(var_indices) do
         local stride_index = (k-1) * factors_size
         local card = cards[k]
         if di < card then
            var_indices[k] = di+1
            for j=1,factors_size do
               factor_indices[j] = factor_indices[j] + strides[stride_index + j]
            end
            break
         else
            var_indices[k] = 1
            for j=1,factors_size do
               factor_indices[j] = factor_indices[j] - (strides[stride_index + j] * (card-1))
            end
         end
      end
      local v = one
      for j,fi in ipairs(factor_indices) do
         v = ring.mul(v, factors[j].raw[fi])
      end
      raw[i] = v
   end
   
   local j = {domain = domain, raw = raw}
   setmetatable(j, factor_mt)
   return j
end

-- Normalizes the factor inline. If kappa is not set, we normalize by the sum of all values
gdl.normalize = function(ring, f, kappa)
   local size = 1
   for _, variable in ipairs(f.domain) do size = size * #variable[2] end
   local raw = f.raw
   if kappa == nil then
      kappa = raw[1]
      for i=2,size do kappa = ring.add(kappa, raw[i]) end
   end
   for i=1,size do raw[i] = ring.invmul(raw[i], kappa) end
end

-- Returns a smaller factor where the variables with the given assignment are
-- removed. If normalize is true, the resulting factor is normalized. The
-- assignments are the variable length argument with the format {variable, assignment}.
gdl.eliminate = function(ring, f, normalize, ...)
   -- compute the new domain and the strides in the original domain
   local assign = {...}
   local domain = {}
   local variables = 0
   local cards = {}
   local size = 1
   local running_stride = 1
   local strides = {}
   local pos = 1 -- the position of the first element we keep
   for _, dim in ipairs(f.domain) do
      local found = false
      local dimcard = #dim[2]
      for _, assign in ipairs(assign) do
         if assign[1] == dim[1] then
            found = true
            local value = assign[2]
            for i,v in ipairs(dim[2]) do
               if v == value then
                  pos = pos + ((i-1) * running_stride)
                  break
               end
            end
            break
         end
      end
      if not found then
         size = size * dimcard
         variables = variables + 1
         domain[variables] = dim
         cards[variables] = dimcard
         strides[variables] = running_stride
      end
      running_stride = running_stride * dimcard
   end

   -- copy the matching entries
   local fraw = f.raw
   local raw = {}
   local variable_pos = {0}
   pos = pos - strides[1]
   for i=2,variables do variable_pos[i] = 1 end
   for i=1,size do
      for k,di in ipairs(variable_pos) do
         local card = cards[k]
         if di < card then
            variable_pos[k] = di+1
            pos = pos + strides[k]
            break
         else
            variable_pos[k] = 1
            pos = pos - (strides[k] * (card-1))
         end
      end
      raw[i] = fraw[pos]
   end

   r = {domain = domain, raw = raw}
   setmetatable(r, factor_mt)
   if normalize then
      gdl.normalize(ring, r)
   end
   return r
end

return gdl
