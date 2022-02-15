import data.list
open list
variable α: Type*
example (xs ys: list α): 
  length (reverse (xs ++ ys)) = length xs + length ys :=
by simp [add_comm]