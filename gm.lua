local gm = {}

--[[

   Graphical Models for Lua

   A factor (in some settings the conditional probability table) maps variables
   from a finite domain (possibly the cartesian product of several "dimensions")
   to values. Factors can be called with values from their domain as if they
   were functions. They contain the following sub-tables:

   - domain: an array of tuples {name, values} of the domain dimensions
   - raw: an array with the raw values

   The operations on function-tables are defined for commutative semirings, here
   just called semirings for shortness.
   
--]]

local index2values = function(domain, index)
   local values = {}
   local remain = index-1
   for i, dimension in ipairs(domain) do
      local dimvalues = dimension[2]
      local dimsize = #dimvalues
      local pos = remain % dimsize
      remain = (remain-pos) / dimsize
      values[i] = dimvalues[pos+1]
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
      if #arg ~= #self then error("not enough arguments") end
      local pos = 1 -- absolute position
      local rd = 1 -- running dimension size
      for j,dim in pairs(self.domain) do
         local a = (...)[j]
         local dpos = 0
         for i=1,#dim do if dim[i] == a then dpos = i; break end end
         if dpos == 0 then error("argument not found") end
         pos = pos + ((dpos-1) * rd)
         rd = rd * #dim
      end
      return self.raw[pos]
   end,
   __tostring = function(self)
      local out = {}
      local dimnames = '('
      for _,dim in ipairs(self.domain) do dimnames = dimnames .. tostring(dim[1]) .. ', ' end
      out[#out+1] = string.sub(dimnames, 1, -3) .. ')\n'
      for i=1,#self.raw do
         local values = index2values(self.domain, i)
         local vs = '('
         for _,v in ipairs(values) do vs = vs .. tostring(v) .. ', ' end
         out[#out+1] = string.sub(vs, 1, -3) .. ') -> ' .. tostring(self.raw[i]) .. '\n'
      end
      return table.concat(out)
   end
}

-- start of the exported functions --

gm.semiring = function(add, zero, mul, one, invmul)
   return {add = add, zero = zero, mul = mul, one = one, invmul = invmul}
end

gm.create_factor = function(func, domain)
   local size = 1
   for _, dimension in pairs(domain) do size = size * #dimension[2] end
   local raw = {}
   for i = 1,size do raw[i] = func(unpack(index2values(domain, i))) end
   local f = { domain = domain, raw = raw }
   setmetatable(f, factor_mt)
   return f
end
   
gm.unity = function(ring, domain)
   local u, size = {domain = domain}, 1
   for _,v in ipairs(domain) do size = size * #v end
   u.raw = {}
   for i = 1,size do u.raw[i] = ring.one end
   setmetatable(u, factor_mt)
   return u
end

-- marginalize out the dimensions not in retain
gm.marginalize = function(ring, f, retain)
   local size = 1
   local domain = {} -- the new domain
   local domain_size = 0
   local dimcards = {}
   local strides = {} -- strides of the retained domains in the original raw array
   local running_stride = 1
   local pattern = {0} -- pattern for summation
   local pattern_size = 1

   -- compute the pattern and the strides
   for k,dim in ipairs(f.domain) do
      local dimname = dim[1]
      local dimvalues = dim[2]
      local dimcard = #dimvalues
      if findindex(retain, dimname) ~= 0 then
         -- keep the dimension
         domain_size = domain_size + 1
         domain[domain_size] = {dimname, dimvalues}
         dimcards[domain_size] = dimcard
         strides[domain_size] = running_stride
         size = size * dimcard
      else
         -- marginalize the dimension out
         local ps = pattern_size
         for j=1,ps do
            for i=2,dimcard do
               pattern_size = pattern_size + 1
               pattern[pattern_size] = pattern[j] + (running_stride * (i - 1))
            end
         end
      end
      running_stride = running_stride * dimcard
   end

   -- marginalize the content via summation
   local raw = {}
   local fraw = f.raw
   local dimension_indices = {0}
   for i=2,domain_size do dimension_indices[i] = 1 end
   local begin = 1 - strides[1] -- the index where we begin to sum up the pattern
   for i=1,size do
      for k,di in ipairs(dimension_indices) do
         local card = dimcards[k]
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

gm.join = function(ring, ...)
   local factors = {...}
   local factors_size = #factors

   -- join the domains
   local size = 1
   local domain = {}
   local dimcards = {}
   local dimnames = {}
   local domain_size = 0
   for i,factor in ipairs(factors) do
      for _,dim in ipairs(factor.domain) do
         local dimname = dim[1]
         if findindex(dimnames, dimname) == 0 then
            local dimcard = #dim[2]
            domain_size = domain_size + 1
            domain[domain_size] = dim
            dimnames[domain_size] = dimname
            dimcards[domain_size] = dimcard
            size = size * dimcard
         end
      end
   end
   
   -- compute the strides to map from the global index into the local one
   local strides_size = factors_size * domain_size
   local strides = {}
   for i=1,strides_size do strides[i] = 0 end
   for j,factor in ipairs(factors) do
      local current_stride = 1
      for _,dimension in ipairs(factor.domain) do
         local dimname = dimension[1]
         local dimvalues = dimension[2]
         local dimensionindex = findindex(dimnames, dimname) - 1
         strides[(dimensionindex * factors_size) + j] = current_stride
         current_stride = current_stride * #dimvalues
      end
   end
   
   -- join the content
   raw = {}
   local one = ring.one
   local factor_indices = {} -- indices in the raw arrays of the factors
   local dimension_indices = {0} -- indices in the dimensions of the joint domain
   for i=1,factors_size do factor_indices[i] = 1 - strides[i] end
   for i=2,domain_size do dimension_indices[i] = 1 end
   for i=1,size do
      for k,di in ipairs(dimension_indices) do
         local stride_index = (k-1) * factors_size
         local card = dimcards[k]
         if di < card then
            dimension_indices[k] = di+1
            for j=1,factors_size do
               factor_indices[j] = factor_indices[j] + strides[stride_index + j]
            end
            break
         else
            dimension_indices[k] = 1
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

-- gm.normalize = function(ring, f)

-- end

-- gm.reduce = function(ring, f, assignments)

-- end

return gm
