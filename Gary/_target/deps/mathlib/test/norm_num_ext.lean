/-
Copyright (c) 2021 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.gcd
import data.nat.prime
import algebra.squarefree

/-!
# Tests for `norm_num` extensions
-/

-- coverage tests
example : nat.coprime 1 2 := by norm_num
example : nat.coprime 2 1 := by norm_num
example : ¬ nat.coprime 0 0 := by norm_num
example : ¬ nat.coprime 0 3 := by norm_num
example : ¬ nat.coprime 2 0 := by norm_num
example : nat.coprime 2 3 := by norm_num
example : ¬ nat.coprime 2 4 := by norm_num

example : nat.gcd 1 2 = 1 := by norm_num
example : nat.gcd 2 1 = 1 := by norm_num
example : nat.gcd 0 0 = 0 := by norm_num
example : nat.gcd 0 3 = 3 := by norm_num
example : nat.gcd 2 0 = 2 := by norm_num
example : nat.gcd 2 3 = 1 := by norm_num
example : nat.gcd 2 4 = 2 := by norm_num

example : nat.lcm 1 2 = 2 := by norm_num
example : nat.lcm 2 1 = 2 := by norm_num
example : nat.lcm 0 0 = 0 := by norm_num
example : nat.lcm 0 3 = 0 := by norm_num
example : nat.lcm 2 0 = 0 := by norm_num
example : nat.lcm 2 3 = 6 := by norm_num
example : nat.lcm 2 4 = 4 := by norm_num

example : int.gcd 2 3 = 1 := by norm_num
example : int.gcd (-2) 3 = 1 := by norm_num
example : int.gcd 2 (-3) = 1 := by norm_num
example : int.gcd (-2) (-3) = 1 := by norm_num

example : int.lcm 2 3 = 6 := by norm_num
example : int.lcm (-2) 3 = 6 := by norm_num
example : int.lcm 2 (-3) = 6 := by norm_num
example : int.lcm (-2) (-3) = 6 := by norm_num

example : ¬ nat.prime 0 := by norm_num
example : ¬ nat.prime 1 := by norm_num
example : nat.prime 2 := by norm_num
example : nat.prime 3 := by norm_num
example : ¬ nat.prime 4 := by norm_num
example : nat.prime 5 := by norm_num
example : nat.prime 109 := by norm_num
example : nat.prime 1277 := by norm_num
example : ¬ nat.prime 1000000000000000000000000000000000000000000000000 := by norm_num

example : nat.min_fac 0 = 2 := by norm_num
example : nat.min_fac 1 = 1 := by norm_num
example : nat.min_fac 2 = 2 := by norm_num
example : nat.min_fac 3 = 3 := by norm_num
example : nat.min_fac 4 = 2 := by norm_num
example : nat.min_fac 121 = 11 := by norm_num
example : nat.min_fac 221 = 13 := by norm_num

example : nat.factors 0 = [] := by norm_num
example : nat.factors 1 = [] := by norm_num
example : nat.factors 2 = [2] := by norm_num
example : nat.factors 3 = [3] := by norm_num
example : nat.factors 4 = [2, 2] := by norm_num
example : nat.factors 12 = [2, 2, 3] := by norm_num
example : nat.factors 221 = [13, 17] := by norm_num

-- randomized tests
example : nat.gcd 35 29 = 1 := by norm_num
example : int.gcd 35 29 = 1 := by norm_num
example : nat.lcm 35 29 = 1015 := by norm_num
example : int.gcd 35 29 = 1 := by norm_num
example : nat.coprime 35 29 := by norm_num

example : nat.gcd 80 2 = 2 := by norm_num
example : int.gcd 80 2 = 2 := by norm_num
example : nat.lcm 80 2 = 80 := by norm_num
example : int.gcd 80 2 = 2 := by norm_num
example : ¬ nat.coprime 80 2 := by norm_num

example : nat.gcd 19 17 = 1 := by norm_num
example : int.gcd 19 17 = 1 := by norm_num
example : nat.lcm 19 17 = 323 := by norm_num
example : int.gcd 19 17 = 1 := by norm_num
example : nat.coprime 19 17 := by norm_num

example : nat.gcd 11 18 = 1 := by norm_num
example : int.gcd 11 18 = 1 := by norm_num
example : nat.lcm 11 18 = 198 := by norm_num
example : int.gcd 11 18 = 1 := by norm_num
example : nat.coprime 11 18 := by norm_num

example : nat.gcd 23 73 = 1 := by norm_num
example : int.gcd 23 73 = 1 := by norm_num
example : nat.lcm 23 73 = 1679 := by norm_num
example : int.gcd 23 73 = 1 := by norm_num
example : nat.coprime 23 73 := by norm_num

example : nat.gcd 73 68 = 1 := by norm_num
example : int.gcd 73 68 = 1 := by norm_num
example : nat.lcm 73 68 = 4964 := by norm_num
example : int.gcd 73 68 = 1 := by norm_num
example : nat.coprime 73 68 := by norm_num

example : nat.gcd 28 16 = 4 := by norm_num
example : int.gcd 28 16 = 4 := by norm_num
example : nat.lcm 28 16 = 112 := by norm_num
example : int.gcd 28 16 = 4 := by norm_num
example : ¬ nat.coprime 28 16 := by norm_num

example : nat.gcd 44 98 = 2 := by norm_num
example : int.gcd 44 98 = 2 := by norm_num
example : nat.lcm 44 98 = 2156 := by norm_num
example : int.gcd 44 98 = 2 := by norm_num
example : ¬ nat.coprime 44 98 := by norm_num

example : nat.gcd 21 79 = 1 := by norm_num
example : int.gcd 21 79 = 1 := by norm_num
example : nat.lcm 21 79 = 1659 := by norm_num
example : int.gcd 21 79 = 1 := by norm_num
example : nat.coprime 21 79 := by norm_num

example : nat.gcd 93 34 = 1 := by norm_num
example : int.gcd 93 34 = 1 := by norm_num
example : nat.lcm 93 34 = 3162 := by norm_num
example : int.gcd 93 34 = 1 := by norm_num
example : nat.coprime 93 34 := by norm_num

example : ¬ nat.prime 912 := by norm_num
example : nat.min_fac 912 = 2 := by norm_num
example : nat.factors 912 = [2, 2, 2, 2, 3, 19] := by norm_num

example : ¬ nat.prime 681 := by norm_num
example : nat.min_fac 681 = 3 := by norm_num
example : nat.factors 681 = [3, 227] := by norm_num

example : ¬ nat.prime 728 := by norm_num
example : nat.min_fac 728 = 2 := by norm_num
example : nat.factors 728 = [2, 2, 2, 7, 13] := by norm_num

example : ¬ nat.prime 248 := by norm_num
example : nat.min_fac 248 = 2 := by norm_num
example : nat.factors 248 = [2, 2, 2, 31] := by norm_num

example : ¬ nat.prime 682 := by norm_num
example : nat.min_fac 682 = 2 := by norm_num
example : nat.factors 682 = [2, 11, 31] := by norm_num

example : ¬ nat.prime 115 := by norm_num
example : nat.min_fac 115 = 5 := by norm_num
example : nat.factors 115 = [5, 23] := by norm_num

example : ¬ nat.prime 824 := by norm_num
example : nat.min_fac 824 = 2 := by norm_num
example : nat.factors 824 = [2, 2, 2, 103] := by norm_num

example : ¬ nat.prime 942 := by norm_num
example : nat.min_fac 942 = 2 := by norm_num
example : nat.factors 942 = [2, 3, 157] := by norm_num

example : ¬ nat.prime 34 := by norm_num
example : nat.min_fac 34 = 2 := by norm_num
example : nat.factors 34 = [2, 17] := by norm_num

example : ¬ nat.prime 754 := by norm_num
example : nat.min_fac 754 = 2 := by norm_num
example : nat.factors 754 = [2, 13, 29] := by norm_num

example : ¬ nat.prime 663 := by norm_num
example : nat.min_fac 663 = 3 := by norm_num
example : nat.factors 663 = [3, 13, 17] := by norm_num

example : ¬ nat.prime 923 := by norm_num
example : nat.min_fac 923 = 13 := by norm_num
example : nat.factors 923 = [13, 71] := by norm_num

example : ¬ nat.prime 77 := by norm_num
example : nat.min_fac 77 = 7 := by norm_num
example : nat.factors 77 = [7, 11] := by norm_num

example : ¬ nat.prime 162 := by norm_num
example : nat.min_fac 162 = 2 := by norm_num
example : nat.factors 162 = [2, 3, 3, 3, 3] := by norm_num

example : ¬ nat.prime 669 := by norm_num
example : nat.min_fac 669 = 3 := by norm_num
example : nat.factors 669 = [3, 223] := by norm_num

example : ¬ nat.prime 476 := by norm_num
example : nat.min_fac 476 = 2 := by norm_num
example : nat.factors 476 = [2, 2, 7, 17] := by norm_num

example : nat.prime 251 := by norm_num
example : nat.min_fac 251 = 251 := by norm_num
example : nat.factors 251 = [251] := by norm_num

example : ¬ nat.prime 129 := by norm_num
example : nat.min_fac 129 = 3 := by norm_num
example : nat.factors 129 = [3, 43] := by norm_num

example : ¬ nat.prime 471 := by norm_num
example : nat.min_fac 471 = 3 := by norm_num
example : nat.factors 471 = [3, 157] := by norm_num

example : ¬ nat.prime 851 := by norm_num
example : nat.min_fac 851 = 23 := by norm_num
example : nat.factors 851 = [23, 37] := by norm_num

example : ¬ squarefree 0 := by norm_num
example : squarefree 1 := by norm_num
example : squarefree 2 := by norm_num
example : squarefree 3 := by norm_num
example : ¬ squarefree 4 := by norm_num
example : squarefree 5 := by norm_num
example : squarefree 6 := by norm_num
example : squarefree 7 := by norm_num
example : ¬ squarefree 8 := by norm_num
example : ¬ squarefree 9 := by norm_num
example : squarefree 10 := by norm_num
example : squarefree (2*3*5*17) := by norm_num
example : ¬ squarefree (2*3*5*5*17) := by norm_num
example : squarefree 251 := by norm_num
