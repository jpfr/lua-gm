gdl = require("gdl")
local add = function(a, b) return a + b end
local mul = function(a, b) return a * b end
local invmul = function(a, b) return a / b end
local sr = gdl.semiring(add, 0.0, mul, 1.0, invmul)

domain = {{"a", {1, 2, 3}}, {"b", {1, 2, 3}}}
domain2 = {{"b", {1, 2, 3}}, {"c", {1, 2, 3}}}
domain3 = {{"c", {1, 2, 3}}, {"d", {1, 2, 3}}}
function f(a,b) return a*b end

f1 = gdl.create_factor(f, domain)
f2 = gdl.create_factor(f, domain2)
f3 = gdl.create_factor(f, domain3)
j = gdl.join(sr, f1, f2)
print(j)
print(j(1,1,1))
m = gdl.marginalize(sr, j, {"c", "b"})
print(m)
x = gdl.eliminate(sr, m, false, {"b", 2})
print(x)
