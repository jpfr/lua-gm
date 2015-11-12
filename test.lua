gm = require("gm")
local add = function(a, b) return a + b end
local mul = function(a, b) return a * b end
local sr = gm.semiring(add, 0, mul, 1)

domain = {{"a", {1, 2, 3}}, {"b", {1, 2, 3}}}
domain2 = {{"b", {1, 2, 3}}, {"c", {1, 2, 3}}}
domain3 = {{"c", {1, 2, 3}}, {"d", {1, 2, 3}}}
function f(a,b) return a*b end

f1 = gm.create_factor(f, domain)
f2 = gm.create_factor(f, domain2)
f3 = gm.create_factor(f, domain3)
j = gm.join(sr, f1, f2)
print(j)
m = gm.marginalize(sr, j, {"c", "b"})
print(m)
