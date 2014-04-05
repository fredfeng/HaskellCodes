module HW6test where

import HW6parse

main = do
  print (parseExp "2 + 23 * (3 + 2) / 2")
  print (parseExp "let x = 3 in x * x")
  print (parseExp "let f = fun(x) x in f(3)")
  print (parseExp "let T = fun(x) fun(y) x in let F = fun(x) fun(y) y in T F")
  print (parseExp "let y = 2 in let f = fun(n) n * y in f y + 3")
  