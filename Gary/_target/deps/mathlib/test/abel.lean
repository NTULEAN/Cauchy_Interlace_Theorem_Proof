import tactic.abel
variables {α : Type*} {a b : α}

example [add_comm_monoid α] : a + (b + a) = a + a + b := by abel
example [add_comm_group α] : (a + b) - ((b + a) + a) = -a := by abel
example [add_comm_group α] (x : α) : x - 0 = x := by abel
example [add_comm_monoid α] (x : α) : (3 : ℕ) • a = a + (2 : ℕ) • a := by abel
example [add_comm_group α] : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
example [add_comm_group α] (a b : α) : a-2•b = a -2•b := by abel
example [add_comm_group α] (a : α) : 0 + a = a := by abel1
example [add_comm_group α] (n : ℕ) (a : α) : n • a = n • a := by abel1
example [add_comm_group α] (n : ℕ) (a : α) : 0 + n • a = n • a := by abel1

-- `abel!` should see through terms that are definitionally equal,
def id' (x : α) := x
example [add_comm_group α] : a + b - b - id' a = 0 :=
begin
  success_if_fail { abel; done },
  abel!
end
