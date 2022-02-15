/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import algebra.order.group
import algebra.order.sub
import data.set.intervals.basic

/-!
# Ordered rings and semirings

This file develops the basics of ordered (semi)rings.

Each typeclass here comprises
* an algebraic class (`semiring`, `comm_semiring`, `ring`, `comm_ring`)
* an order class (`partial_order`, `linear_order`)
* assumptions on how both interact ((strict) monotonicity, canonicity)

For short,
* "`+` respects `≤`" means "monotonicity of addition"
* "`*` respects `<`" means "strict monotonicity of multiplication by a positive number".

## Typeclasses

* `ordered_semiring`: Semiring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_semiring`: Commutative semiring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `ordered_ring`: Ring with a partial order such that `+` respects `≤` and `*` respects `<`.
* `ordered_comm_ring`: Commutative ring with a partial order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_semiring`: Semiring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `linear_ordered_ring`: Ring with a linear order such that `+` respects `≤` and `*` respects `<`.
* `linear_ordered_comm_ring`: Commutative ring with a linear order such that `+` respects `≤` and
  `*` respects `<`.
* `canonically_ordered_comm_semiring`: Commutative semiring with a partial order such that `+`
  respects `≤`, `*` respects `<`, and `a ≤ b ↔ ∃ c, b = a + c`.

and some typeclasses to define ordered rings by specifying their nonegative elements:
* `nonneg_ring`: To define `ordered_ring`s.
* `linear_nonneg_ring`: To define `linear_ordered_ring`s.

## Hierarchy

The hardest part of proving order lemmas might be to figure out the correct generality and its
corresponding typeclass. Here's an attempt at demystifying it. For each typeclass, we list its
immediate predecessors and what conditions are added to each of them.

* `ordered_semiring`
  - `ordered_cancel_add_comm_monoid` & multiplication & `*` respects `<`
  - `semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_semiring`
  - `ordered_semiring` & commutativity of multiplication
  - `comm_semiring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_ring`
  - `ordered_semiring` & additive inverses
  - `ordered_add_comm_group` & multiplication & `*` respects `<`
  - `ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `ordered_comm_ring`
  - `ordered_ring` & commutativity of multiplication
  - `ordered_comm_semiring` & additive inverses
  - `comm_ring` & partial order structure & `+` respects `≤` & `*` respects `<`
* `linear_ordered_semiring`
  - `ordered_semiring` & totality of the order & nontriviality
  - `linear_ordered_add_comm_monoid` & multiplication & nontriviality & `*` respects `<`
* `linear_ordered_ring`
  - `ordered_ring` & totality of the order & nontriviality
  - `linear_ordered_semiring` & additive inverses
  - `linear_ordered_add_comm_group` & multiplication & `*` respects `<`
  - `domain` & linear order structure
* `linear_ordered_comm_ring`
  - `ordered_comm_ring` & totality of the order & nontriviality
  - `linear_ordered_ring` & commutativity of multiplication
  - `is_domain` & linear order structure
* `canonically_ordered_comm_semiring`
  - `canonically_ordered_add_monoid` & multiplication & `*` respects `<` & no zero divisors
  - `comm_semiring` & `a ≤ b ↔ ∃ c, b = a + c` & no zero divisors

## TODO

We're still missing some typeclasses, like
* `linear_ordered_comm_semiring`
* `canonically_ordered_semiring`
They have yet to come up in practice.
-/

set_option old_structure_cmd true

universe u
variable {α : Type u}

lemma add_one_le_two_mul [preorder α] [semiring α] [covariant_class α α (+) (≤)]
  {a : α} (a1 : 1 ≤ a) :
  a + 1 ≤ 2 * a :=
calc  a + 1 ≤ a + a : add_le_add_left a1 a
        ... = 2 * a : (two_mul _).symm

/-- An `ordered_semiring α` is a semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class ordered_semiring (α : Type u) extends semiring α, ordered_cancel_add_comm_monoid α :=
(zero_le_one : 0 ≤ (1 : α))
(mul_lt_mul_of_pos_left :  ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right : ∀ a b c : α, a < b → 0 < c → a * c < b * c)

section ordered_semiring
variables [ordered_semiring α] {a b c d : α}

@[simp] lemma zero_le_one : 0 ≤ (1:α) :=
ordered_semiring.zero_le_one

lemma zero_le_two : 0 ≤ (2:α) :=
add_nonneg zero_le_one zero_le_one

lemma one_le_two : 1 ≤ (2:α) :=
calc (1:α) = 0 + 1 : (zero_add _).symm
       ... ≤ 1 + 1 : add_le_add_right zero_le_one _

section nontrivial

variables [nontrivial α]

@[simp] lemma zero_lt_one : 0 < (1 : α) :=
lt_of_le_of_ne zero_le_one zero_ne_one

lemma zero_lt_two : 0 < (2:α) := add_pos zero_lt_one zero_lt_one

@[field_simps] lemma two_ne_zero : (2:α) ≠ 0 :=
ne.symm (ne_of_lt zero_lt_two)

lemma one_lt_two : 1 < (2:α) :=
calc (2:α) = 1+1 : one_add_one_eq_two
     ...   > 1+0 : add_lt_add_left zero_lt_one _
     ...   = 1   : add_zero 1

lemma zero_lt_three : 0 < (3:α) := add_pos zero_lt_two zero_lt_one

lemma zero_lt_four : 0 < (4:α) := add_pos zero_lt_two zero_lt_two

alias zero_lt_one ← one_pos
alias zero_lt_two ← two_pos
alias zero_lt_three ← three_pos
alias zero_lt_four ← four_pos

end nontrivial

lemma mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
ordered_semiring.mul_lt_mul_of_pos_left a b c h₁ h₂

lemma mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
ordered_semiring.mul_lt_mul_of_pos_right a b c h₁ h₂

-- See Note [decidable namespace]
protected lemma decidable.mul_le_mul_of_nonneg_left [@decidable_rel α (≤)]
  (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
begin
  by_cases ba : b ≤ a, { simp [ba.antisymm h₁] },
  by_cases c0 : c ≤ 0, { simp [c0.antisymm h₂] },
  exact (mul_lt_mul_of_pos_left (h₁.lt_of_not_le ba) (h₂.lt_of_not_le c0)).le,
end

lemma mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b :=
by classical; exact decidable.mul_le_mul_of_nonneg_left

-- See Note [decidable namespace]
protected lemma decidable.mul_le_mul_of_nonneg_right [@decidable_rel α (≤)]
  (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
begin
  by_cases ba : b ≤ a, { simp [ba.antisymm h₁] },
  by_cases c0 : c ≤ 0, { simp [c0.antisymm h₂] },
  exact (mul_lt_mul_of_pos_right (h₁.lt_of_not_le ba) (h₂.lt_of_not_le c0)).le,
end

lemma mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c :=
by classical; exact decidable.mul_le_mul_of_nonneg_right

-- TODO: there are four variations, depending on which variables we assume to be nonneg
-- See Note [decidable namespace]
protected lemma decidable.mul_le_mul [@decidable_rel α (≤)]
  (hac : a ≤ c) (hbd : b ≤ d) (nn_b : 0 ≤ b) (nn_c : 0 ≤ c) : a * b ≤ c * d :=
calc
  a * b ≤ c * b : decidable.mul_le_mul_of_nonneg_right hac nn_b
    ... ≤ c * d : decidable.mul_le_mul_of_nonneg_left hbd nn_c

lemma mul_le_mul : a ≤ c → b ≤ d → 0 ≤ b → 0 ≤ c → a * b ≤ c * d :=
by classical; exact decidable.mul_le_mul

-- See Note [decidable namespace]
protected lemma decidable.mul_nonneg_le_one_le {α : Type*} [ordered_semiring α]
  [@decidable_rel α (≤)] {a b c : α}
  (h₁ : 0 ≤ c) (h₂ : a ≤ c) (h₃ : 0 ≤ b) (h₄ : b ≤ 1) : a * b ≤ c :=
by simpa only [mul_one] using decidable.mul_le_mul h₂ h₄ h₃ h₁

lemma mul_nonneg_le_one_le {α : Type*} [ordered_semiring α] {a b c : α} :
  0 ≤ c → a ≤ c → 0 ≤ b → b ≤ 1 → a * b ≤ c :=
by classical; exact decidable.mul_nonneg_le_one_le

-- See Note [decidable namespace]
protected lemma decidable.mul_nonneg [@decidable_rel α (≤)]
  (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
have h : 0 * b ≤ a * b, from decidable.mul_le_mul_of_nonneg_right ha hb,
by rwa [zero_mul] at h

lemma mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b := by classical; exact decidable.mul_nonneg

-- See Note [decidable namespace]
protected lemma decidable.mul_nonpos_of_nonneg_of_nonpos [@decidable_rel α (≤)]
  (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 :=
have h : a * b ≤ a * 0, from decidable.mul_le_mul_of_nonneg_left hb ha,
by rwa mul_zero at h

lemma mul_nonpos_of_nonneg_of_nonpos : 0 ≤ a → b ≤ 0 → a * b ≤ 0 :=
 by classical; exact decidable.mul_nonpos_of_nonneg_of_nonpos

-- See Note [decidable namespace]
protected lemma decidable.mul_nonpos_of_nonpos_of_nonneg [@decidable_rel α (≤)]
  (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 :=
have h : a * b ≤ 0 * b, from decidable.mul_le_mul_of_nonneg_right ha hb,
by rwa zero_mul at h

lemma mul_nonpos_of_nonpos_of_nonneg : a ≤ 0 → 0 ≤ b → a * b ≤ 0 :=
by classical; exact decidable.mul_nonpos_of_nonpos_of_nonneg

-- See Note [decidable namespace]
protected lemma decidable.mul_lt_mul [@decidable_rel α (≤)]
  (hac : a < c) (hbd : b ≤ d) (pos_b : 0 < b) (nn_c : 0 ≤ c) : a * b < c * d :=
calc
  a * b < c * b : mul_lt_mul_of_pos_right hac pos_b
    ... ≤ c * d : decidable.mul_le_mul_of_nonneg_left hbd nn_c

lemma mul_lt_mul : a < c → b ≤ d → 0 < b → 0 ≤ c → a * b < c * d :=
by classical; exact decidable.mul_lt_mul

-- See Note [decidable namespace]
protected lemma decidable.mul_lt_mul' [@decidable_rel α (≤)]
  (h1 : a ≤ c) (h2 : b < d) (h3 : 0 ≤ b) (h4 : 0 < c) : a * b < c * d :=
calc
   a * b ≤ c * b : decidable.mul_le_mul_of_nonneg_right h1 h3
     ... < c * d : mul_lt_mul_of_pos_left h2 h4

lemma mul_lt_mul' : a ≤ c → b < d → 0 ≤ b → 0 < c → a * b < c * d :=
by classical; exact decidable.mul_lt_mul'

lemma mul_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
have h : 0 * b < a * b, from mul_lt_mul_of_pos_right ha hb,
by rwa zero_mul at h

lemma mul_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a * b < 0 :=
have h : a * b < a * 0, from mul_lt_mul_of_pos_left hb ha,
by rwa mul_zero at h

lemma mul_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a * b < 0 :=
have h : a * b < 0 * b, from mul_lt_mul_of_pos_right ha hb,
by rwa zero_mul at  h

-- See Note [decidable namespace]
protected lemma decidable.mul_self_lt_mul_self [@decidable_rel α (≤)]
  (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
decidable.mul_lt_mul' h2.le h2 h1 $ h1.trans_lt h2

lemma mul_self_lt_mul_self (h1 : 0 ≤ a) (h2 : a < b) : a * a < b * b :=
mul_lt_mul' h2.le h2 h1 $ h1.trans_lt h2

-- See Note [decidable namespace]
protected lemma decidable.strict_mono_on_mul_self [@decidable_rel α (≤)] :
  strict_mono_on (λ x : α, x * x) (set.Ici 0) :=
λ x hx y hy hxy, decidable.mul_self_lt_mul_self hx hxy

lemma strict_mono_on_mul_self : strict_mono_on (λ x : α, x * x) (set.Ici 0) :=
λ x hx y hy hxy, mul_self_lt_mul_self hx hxy

-- See Note [decidable namespace]
protected lemma decidable.mul_self_le_mul_self [@decidable_rel α (≤)]
  (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
decidable.mul_le_mul h2 h2 h1 $ h1.trans h2

lemma mul_self_le_mul_self (h1 : 0 ≤ a) (h2 : a ≤ b) : a * a ≤ b * b :=
mul_le_mul h2 h2 h1 $ h1.trans h2

-- See Note [decidable namespace]
protected lemma decidable.mul_lt_mul'' [@decidable_rel α (≤)]
  (h1 : a < c) (h2 : b < d) (h3 : 0 ≤ a) (h4 : 0 ≤ b) : a * b < c * d :=
h4.lt_or_eq_dec.elim
  (λ b0, decidable.mul_lt_mul h1 h2.le b0 $ h3.trans h1.le)
  (λ b0, by rw [← b0, mul_zero]; exact
    mul_pos (h3.trans_lt h1) (h4.trans_lt h2))

lemma mul_lt_mul'' : a < c → b < d → 0 ≤ a → 0 ≤ b → a * b < c * d :=
by classical; exact decidable.mul_lt_mul''

-- See Note [decidable namespace]
protected lemma decidable.le_mul_of_one_le_right [@decidable_rel α (≤)]
  (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ b * a :=
suffices b * 1 ≤ b * a, by rwa mul_one at this,
decidable.mul_le_mul_of_nonneg_left h hb

lemma le_mul_of_one_le_right : 0 ≤ b → 1 ≤ a → b ≤ b * a :=
by classical; exact decidable.le_mul_of_one_le_right

-- See Note [decidable namespace]
protected lemma decidable.le_mul_of_one_le_left [@decidable_rel α (≤)]
  (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b :=
suffices 1 * b ≤ a * b, by rwa one_mul at this,
decidable.mul_le_mul_of_nonneg_right h hb

lemma le_mul_of_one_le_left : 0 ≤ b → 1 ≤ a → b ≤ a * b :=
by classical; exact decidable.le_mul_of_one_le_left

-- See Note [decidable namespace]
protected lemma decidable.lt_mul_of_one_lt_right [@decidable_rel α (≤)]
  (hb : 0 < b) (h : 1 < a) : b < b * a :=
suffices b * 1 < b * a, by rwa mul_one at this,
decidable.mul_lt_mul' le_rfl h zero_le_one hb

lemma lt_mul_of_one_lt_right : 0 < b → 1 < a → b < b * a :=
by classical; exact decidable.lt_mul_of_one_lt_right

-- See Note [decidable namespace]
protected lemma decidable.lt_mul_of_one_lt_left [@decidable_rel α (≤)]
  (hb : 0 < b) (h : 1 < a) : b < a * b :=
suffices 1 * b < a * b, by rwa one_mul at this,
decidable.mul_lt_mul h le_rfl hb (zero_le_one.trans h.le)

lemma lt_mul_of_one_lt_left : 0 < b → 1 < a → b < a * b :=
by classical; exact decidable.lt_mul_of_one_lt_left

-- See Note [decidable namespace]
protected lemma decidable.add_le_mul_two_add [@decidable_rel α (≤)] {a b : α}
  (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
calc a + (2 + b) ≤ a + (a + a * b) :
      add_le_add_left (add_le_add a2 (decidable.le_mul_of_one_le_left b0 (one_le_two.trans a2))) a
             ... ≤ a * (2 + b) : by rw [mul_add, mul_two, add_assoc]

lemma add_le_mul_two_add {a b : α} : 2 ≤ a → 0 ≤ b → a + (2 + b) ≤ a * (2 + b) :=
by classical; exact decidable.add_le_mul_two_add

-- See Note [decidable namespace]
protected lemma decidable.one_le_mul_of_one_le_of_one_le [@decidable_rel α (≤)]
  {a b : α} (a1 : 1 ≤ a) (b1 : 1 ≤ b) : (1 : α) ≤ a * b :=
(mul_one (1 : α)).symm.le.trans (decidable.mul_le_mul a1 b1 zero_le_one (zero_le_one.trans a1))

lemma one_le_mul_of_one_le_of_one_le {a b : α} : 1 ≤ a → 1 ≤ b → (1 : α) ≤ a * b :=
by classical; exact decidable.one_le_mul_of_one_le_of_one_le

/-- Pullback an `ordered_semiring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.ordered_semiring {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_semiring β :=
{ zero_le_one := show f 0 ≤ f 1, by simp only [zero, one, zero_le_one],
  mul_lt_mul_of_pos_left := λ  a b c ab c0, show f (c * a) < f (c * b),
    begin
      rw [mul, mul],
      refine mul_lt_mul_of_pos_left ab _,
      rwa ← zero,
    end,
  mul_lt_mul_of_pos_right := λ a b c ab c0, show f (a * c) < f (b * c),
    begin
      rw [mul, mul],
      refine mul_lt_mul_of_pos_right ab _,
      rwa ← zero,
    end,
  ..hf.ordered_cancel_add_comm_monoid f zero add,
  ..hf.semiring f zero one add mul }

section
variable [nontrivial α]

lemma bit1_pos (h : 0 ≤ a) : 0 < bit1 a :=
lt_add_of_le_of_pos (add_nonneg h h) zero_lt_one

lemma lt_add_one (a : α) : a < a + 1 :=
lt_add_of_le_of_pos le_rfl zero_lt_one

lemma lt_one_add (a : α) : a < 1 + a :=
by { rw [add_comm], apply lt_add_one }

end

lemma bit1_pos' (h : 0 < a) : 0 < bit1 a :=
begin
  nontriviality,
  exact bit1_pos h.le,
end

-- See Note [decidable namespace]
protected lemma decidable.one_lt_mul [@decidable_rel α (≤)]
  (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
begin
  nontriviality,
  exact (one_mul (1 : α)) ▸ decidable.mul_lt_mul' ha hb zero_le_one (zero_lt_one.trans_le ha)
end

lemma one_lt_mul : 1 ≤ a → 1 < b → 1 < a * b :=
by classical; exact decidable.one_lt_mul

-- See Note [decidable namespace]
protected lemma decidable.mul_le_one [@decidable_rel α (≤)]
  (ha : a ≤ 1) (hb' : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
begin rw ← one_mul (1 : α), apply decidable.mul_le_mul; {assumption <|> apply zero_le_one} end

lemma mul_le_one : a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1 :=
by classical; exact decidable.mul_le_one

-- See Note [decidable namespace]
protected lemma decidable.one_lt_mul_of_le_of_lt [@decidable_rel α (≤)]
  (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
begin
  nontriviality,
  calc 1 = 1 * 1 : by rw one_mul
     ... < a * b : decidable.mul_lt_mul' ha hb zero_le_one (zero_lt_one.trans_le ha)
end

lemma one_lt_mul_of_le_of_lt : 1 ≤ a → 1 < b → 1 < a * b :=
by classical; exact decidable.one_lt_mul_of_le_of_lt

-- See Note [decidable namespace]
protected lemma decidable.one_lt_mul_of_lt_of_le [@decidable_rel α (≤)]
  (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
begin
  nontriviality,
  calc 1 = 1 * 1 : by rw one_mul
    ... < a * b : decidable.mul_lt_mul ha hb zero_lt_one $ zero_le_one.trans ha.le
end

lemma one_lt_mul_of_lt_of_le : 1 < a → 1 ≤ b → 1 < a * b :=
by classical; exact decidable.one_lt_mul_of_lt_of_le

-- See Note [decidable namespace]
protected lemma decidable.mul_le_of_le_one_right [@decidable_rel α (≤)]
  (ha : 0 ≤ a) (hb1 : b ≤ 1) : a * b ≤ a :=
calc a * b ≤ a * 1 : decidable.mul_le_mul_of_nonneg_left hb1 ha
... = a : mul_one a

lemma mul_le_of_le_one_right : 0 ≤ a → b ≤ 1 → a * b ≤ a :=
by classical; exact decidable.mul_le_of_le_one_right

-- See Note [decidable namespace]
protected lemma decidable.mul_le_of_le_one_left [@decidable_rel α (≤)]
  (hb : 0 ≤ b) (ha1 : a ≤ 1) : a * b ≤ b :=
calc a * b ≤ 1 * b : decidable.mul_le_mul ha1 le_rfl hb zero_le_one
... = b : one_mul b

lemma mul_le_of_le_one_left : 0 ≤ b → a ≤ 1 → a * b ≤ b :=
by classical; exact decidable.mul_le_of_le_one_left

-- See Note [decidable namespace]
protected lemma decidable.mul_lt_one_of_nonneg_of_lt_one_left [@decidable_rel α (≤)]
  (ha0 : 0 ≤ a) (ha : a < 1) (hb : b ≤ 1) : a * b < 1 :=
calc a * b ≤ a : decidable.mul_le_of_le_one_right ha0 hb
... < 1 : ha

lemma mul_lt_one_of_nonneg_of_lt_one_left : 0 ≤ a → a < 1 → b ≤ 1 → a * b < 1 :=
by classical; exact decidable.mul_lt_one_of_nonneg_of_lt_one_left

-- See Note [decidable namespace]
protected lemma decidable.mul_lt_one_of_nonneg_of_lt_one_right [@decidable_rel α (≤)]
  (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb : b < 1) : a * b < 1 :=
calc a * b ≤ b : decidable.mul_le_of_le_one_left hb0 ha
... < 1 : hb

lemma mul_lt_one_of_nonneg_of_lt_one_right : a ≤ 1 → 0 ≤ b → b < 1 → a * b < 1 :=
by classical; exact decidable.mul_lt_one_of_nonneg_of_lt_one_right

end ordered_semiring

section ordered_comm_semiring

/-- An `ordered_comm_semiring α` is a commutative semiring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class ordered_comm_semiring (α : Type u) extends ordered_semiring α, comm_semiring α

/-- Pullback an `ordered_comm_semiring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.ordered_comm_semiring [ordered_comm_semiring α] {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_comm_semiring β :=
{ ..hf.comm_semiring f zero one add mul,
  ..hf.ordered_semiring f zero one add mul }

end ordered_comm_semiring

/--
A `linear_ordered_semiring α` is a nontrivial semiring `α` with a linear order
such that addition is monotone and multiplication by a positive number is strictly monotone.
-/
-- It's not entirely clear we should assume `nontrivial` at this point;
-- it would be reasonable to explore changing this,
-- but be warned that the instances involving `domain` may cause
-- typeclass search loops.
@[protect_proj]
class linear_ordered_semiring (α : Type u)
  extends ordered_semiring α, linear_ordered_add_comm_monoid α, nontrivial α

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a b c d : α}

-- `norm_num` expects the lemma stating `0 < 1` to have a single typeclass argument
-- (see `norm_num.prove_pos_nat`).
-- Rather than working out how to relax that assumption,
-- we provide a synonym for `zero_lt_one` (which needs both `ordered_semiring α` and `nontrivial α`)
-- with only a `linear_ordered_semiring` typeclass argument.
lemma zero_lt_one' : 0 < (1 : α) := zero_lt_one

lemma lt_of_mul_lt_mul_left (h : c * a < c * b) (hc : 0 ≤ c) : a < b :=
by haveI := @linear_order.decidable_le α _; exact lt_of_not_ge
  (assume h1 : b ≤ a,
   have h2 : c * b ≤ c * a, from decidable.mul_le_mul_of_nonneg_left h1 hc,
   h2.not_lt h)

lemma lt_of_mul_lt_mul_right (h : a * c < b * c) (hc : 0 ≤ c) : a < b :=
by haveI := @linear_order.decidable_le α _; exact lt_of_not_ge
  (assume h1 : b ≤ a,
   have h2 : b * c ≤ a * c, from decidable.mul_le_mul_of_nonneg_right h1 hc,
   h2.not_lt h)

lemma le_of_mul_le_mul_left (h : c * a ≤ c * b) (hc : 0 < c) : a ≤ b :=
le_of_not_gt
  (assume h1 : b < a,
   have h2 : c * b < c * a, from mul_lt_mul_of_pos_left h1 hc,
   h2.not_le h)

lemma le_of_mul_le_mul_right (h : a * c ≤ b * c) (hc : 0 < c) : a ≤ b :=
le_of_not_gt
  (assume h1 : b < a,
   have h2 : b * c < a * c, from mul_lt_mul_of_pos_right h1 hc,
   h2.not_le h)

lemma pos_and_pos_or_neg_and_neg_of_mul_pos (hab : 0 < a * b) :
  (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) :=
begin
  haveI := @linear_order.decidable_le α _,
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  { refine or.inl ⟨ha, lt_imp_lt_of_le_imp_le (λ hb, _) hab⟩,
    exact decidable.mul_nonpos_of_nonneg_of_nonpos ha.le hb },
  { rw [zero_mul] at hab, exact hab.false.elim },
  { refine or.inr ⟨ha, lt_imp_lt_of_le_imp_le (λ hb, _) hab⟩,
    exact decidable.mul_nonpos_of_nonpos_of_nonneg ha.le hb }
end

lemma nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg (hab : 0 ≤ a * b) :
    (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0) :=
begin
  haveI := @linear_order.decidable_le α _,
  refine decidable.or_iff_not_and_not.2 _,
  simp only [not_and, not_le], intros ab nab, apply not_lt_of_le hab _,
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  exacts [mul_neg_of_pos_of_neg ha (ab ha.le), ((ab le_rfl).asymm (nab le_rfl)).elim,
    mul_neg_of_neg_of_pos ha (nab ha.le)]
end

lemma pos_of_mul_pos_left (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_right $ λ h, h.1.not_le ha).2

lemma pos_of_mul_pos_right (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_right $ λ h, h.2.not_le hb).1

lemma pos_iff_pos_of_mul_pos (hab : 0 < a * b) : 0 < a ↔ 0 < b :=
⟨pos_of_mul_pos_left hab ∘ le_of_lt, pos_of_mul_pos_right hab ∘ le_of_lt⟩

lemma neg_of_mul_pos_left (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.1.not_le ha).2

lemma neg_of_mul_pos_right (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left $ λ h, h.2.not_le ha).1

lemma neg_iff_neg_of_mul_pos (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
⟨neg_of_mul_pos_left hab ∘ le_of_lt, neg_of_mul_pos_right hab ∘ le_of_lt⟩

lemma nonneg_of_mul_nonneg_left (h : 0 ≤ a * b) (h1 : 0 < a) : 0 ≤ b :=
le_of_not_gt (assume h2 : b < 0, (mul_neg_of_pos_of_neg h1 h2).not_le h)

lemma nonneg_of_mul_nonneg_right (h : 0 ≤ a * b) (h1 : 0 < b) : 0 ≤ a :=
le_of_not_gt (assume h2 : a < 0, (mul_neg_of_neg_of_pos h2 h1).not_le h)

lemma neg_of_mul_neg_left (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
by haveI := @linear_order.decidable_le α _; exact
lt_of_not_ge (assume h2 : b ≥ 0, (decidable.mul_nonneg h1 h2).not_lt h)

lemma neg_of_mul_neg_right (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
by haveI := @linear_order.decidable_le α _; exact
lt_of_not_ge (assume h2 : a ≥ 0, (decidable.mul_nonneg h2 h1).not_lt h)

lemma nonpos_of_mul_nonpos_left (h : a * b ≤ 0) (h1 : 0 < a) : b ≤ 0 :=
le_of_not_gt (assume h2 : b > 0, (mul_pos h1 h2).not_le h)

lemma nonpos_of_mul_nonpos_right (h : a * b ≤ 0) (h1 : 0 < b) : a ≤ 0 :=
le_of_not_gt (assume h2 : a > 0, (mul_pos h2 h1).not_le h)

@[simp] lemma mul_le_mul_left (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b :=
by haveI := @linear_order.decidable_le α _; exact
⟨λ h', le_of_mul_le_mul_left h' h, λ h', decidable.mul_le_mul_of_nonneg_left h' h.le⟩

@[simp] lemma mul_le_mul_right (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b :=
by haveI := @linear_order.decidable_le α _; exact
⟨λ h', le_of_mul_le_mul_right h' h, λ h', decidable.mul_le_mul_of_nonneg_right h' h.le⟩

@[simp] lemma mul_lt_mul_left (h : 0 < c) : c * a < c * b ↔ a < b :=
by haveI := @linear_order.decidable_le α _; exact
⟨lt_imp_lt_of_le_imp_le $ λ h', decidable.mul_le_mul_of_nonneg_left h' h.le,
 λ h', mul_lt_mul_of_pos_left h' h⟩

@[simp] lemma mul_lt_mul_right (h : 0 < c) : a * c < b * c ↔ a < b :=
by haveI := @linear_order.decidable_le α _; exact
⟨lt_imp_lt_of_le_imp_le $ λ h', decidable.mul_le_mul_of_nonneg_right h' h.le,
 λ h', mul_lt_mul_of_pos_right h' h⟩

@[simp] lemma zero_le_mul_left (h : 0 < c) : 0 ≤ c * b ↔ 0 ≤ b :=
by { convert mul_le_mul_left h, simp }

@[simp] lemma zero_le_mul_right (h : 0 < c) : 0 ≤ b * c ↔ 0 ≤ b :=
by { convert mul_le_mul_right h, simp }

@[simp] lemma zero_lt_mul_left (h : 0 < c) : 0 < c * b ↔ 0 < b :=
by { convert mul_lt_mul_left h, simp }

@[simp] lemma zero_lt_mul_right (h : 0 < c) : 0 < b * c ↔ 0 < b :=
by { convert mul_lt_mul_right h, simp }

lemma add_le_mul_of_left_le_right (a2 : 2 ≤ a) (ab : a ≤ b) : a + b ≤ a * b :=
have 0 < b, from
calc 0 < 2 : zero_lt_two
   ... ≤ a : a2
   ... ≤ b : ab,
calc a + b ≤ b + b : add_le_add_right ab b
       ... = 2 * b : (two_mul b).symm
       ... ≤ a * b : (mul_le_mul_right this).mpr a2

lemma add_le_mul_of_right_le_left (b2 : 2 ≤ b) (ba : b ≤ a) : a + b ≤ a * b :=
have 0 < a, from
calc 0 < 2 : zero_lt_two
   ... ≤ b : b2
   ... ≤ a : ba,
calc a + b ≤ a + a : add_le_add_left ba a
       ... = a * 2 : (mul_two a).symm
       ... ≤ a * b : (mul_le_mul_left this).mpr b2

lemma add_le_mul (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
if hab : a ≤ b then add_le_mul_of_left_le_right a2 hab
               else add_le_mul_of_right_le_left b2 (le_of_not_le hab)

lemma add_le_mul' (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ b * a :=
(le_of_eq (add_comm _ _)).trans (add_le_mul b2 a2)

section
variables [nontrivial α]

@[simp] lemma bit0_le_bit0 : bit0 a ≤ bit0 b ↔ a ≤ b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma bit0_lt_bit0 : bit0 a < bit0 b ↔ a < b :=
by rw [bit0, bit0, ← two_mul, ← two_mul, mul_lt_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma bit1_le_bit1 : bit1 a ≤ bit1 b ↔ a ≤ b :=
(add_le_add_iff_right 1).trans bit0_le_bit0

@[simp] lemma bit1_lt_bit1 : bit1 a < bit1 b ↔ a < b :=
(add_lt_add_iff_right 1).trans bit0_lt_bit0

@[simp] lemma one_le_bit1 : (1 : α) ≤ bit1 a ↔ 0 ≤ a :=
by rw [bit1, le_add_iff_nonneg_left, bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma one_lt_bit1 : (1 : α) < bit1 a ↔ 0 < a :=
by rw [bit1, lt_add_iff_pos_left, bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma zero_le_bit0 : (0 : α) ≤ bit0 a ↔ 0 ≤ a :=
by rw [bit0, ← two_mul, zero_le_mul_left (zero_lt_two : 0 < (2:α))]

@[simp] lemma zero_lt_bit0 : (0 : α) < bit0 a ↔ 0 < a :=
by rw [bit0, ← two_mul, zero_lt_mul_left (zero_lt_two : 0 < (2:α))]

end

lemma le_mul_iff_one_le_left (hb : 0 < b) : b ≤ a * b ↔ 1 ≤ a :=
suffices 1 * b ≤ a * b ↔ 1 ≤ a, by rwa one_mul at this,
mul_le_mul_right hb

lemma lt_mul_iff_one_lt_left (hb : 0 < b) : b < a * b ↔ 1 < a :=
suffices 1 * b < a * b ↔ 1 < a, by rwa one_mul at this,
mul_lt_mul_right hb

lemma le_mul_iff_one_le_right (hb : 0 < b) : b ≤ b * a ↔ 1 ≤ a :=
suffices b * 1 ≤ b * a ↔ 1 ≤ a, by rwa mul_one at this,
mul_le_mul_left hb

lemma lt_mul_iff_one_lt_right (hb : 0 < b) : b < b * a ↔ 1 < a :=
suffices b * 1 < b * a ↔ 1 < a, by rwa mul_one at this,
mul_lt_mul_left hb

theorem mul_nonneg_iff_right_nonneg_of_pos (ha : 0 < a) : 0 ≤ a * b ↔ 0 ≤ b :=
by haveI := @linear_order.decidable_le α _; exact
⟨λ h, nonneg_of_mul_nonneg_left h ha, λ h, decidable.mul_nonneg ha.le h⟩

theorem mul_nonneg_iff_left_nonneg_of_pos (hb : 0 < b) : 0 ≤ a * b ↔ 0 ≤ a :=
by haveI := @linear_order.decidable_le α _; exact
⟨λ h, nonneg_of_mul_nonneg_right h hb, λ h, decidable.mul_nonneg h hb.le⟩

lemma mul_le_iff_le_one_left (hb : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
⟨ λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_left hb).2 h.not_lt),
  λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_left hb).1 h.not_lt) ⟩

lemma mul_lt_iff_lt_one_left (hb : 0 < b) : a * b < b ↔ a < 1 :=
lt_iff_lt_of_le_iff_le $ le_mul_iff_one_le_left hb

lemma mul_le_iff_le_one_right (hb : 0 < b) : b * a ≤ b ↔ a ≤ 1 :=
⟨ λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_right hb).2 h.not_lt),
  λ h, le_of_not_lt (mt (lt_mul_iff_one_lt_right hb).1 h.not_lt) ⟩

lemma mul_lt_iff_lt_one_right (hb : 0 < b) : b * a < b ↔ a < 1 :=
lt_iff_lt_of_le_iff_le $ le_mul_iff_one_le_right hb

-- TODO: `left` and `right` for these two lemmas are backwards compared to `neg_of_mul_pos`
-- lemmas.
lemma nonpos_of_mul_nonneg_left (h : 0 ≤ a * b) (hb : b < 0) : a ≤ 0 :=
le_of_not_gt (λ ha, absurd h (mul_neg_of_pos_of_neg ha hb).not_le)

lemma nonpos_of_mul_nonneg_right (h : 0 ≤ a * b) (ha : a < 0) : b ≤ 0 :=
le_of_not_gt (λ hb, absurd h (mul_neg_of_neg_of_pos ha hb).not_le)

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_semiring.to_no_max_order {α : Type*} [linear_ordered_semiring α] :
  no_max_order α :=
⟨assume a, ⟨a + 1, lt_add_of_pos_right _ zero_lt_one⟩⟩

/-- Pullback a `linear_ordered_semiring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.linear_ordered_semiring {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
  linear_ordered_semiring β :=
{ .. linear_order.lift f hf,
  .. pullback_nonzero f zero one,
  .. hf.ordered_semiring f zero one add mul }

@[simp] lemma units.inv_pos {u : αˣ} : (0 : α) < ↑u⁻¹ ↔ (0 : α) < u :=
have ∀ {u : αˣ}, (0 : α) < u → (0 : α) < ↑u⁻¹ := λ u h,
  (zero_lt_mul_left h).mp $ u.mul_inv.symm ▸ zero_lt_one,
⟨this, this⟩

@[simp] lemma units.inv_neg {u : αˣ} : ↑u⁻¹ < (0 : α) ↔ ↑u < (0 : α) :=
have ∀ {u : αˣ}, ↑u < (0 : α) → ↑u⁻¹ < (0 : α) := λ u h,
  neg_of_mul_pos_left (by exact (u.mul_inv.symm ▸ zero_lt_one)) h.le,
⟨this, this⟩

end linear_ordered_semiring

section mono
variables {β : Type*} [linear_ordered_semiring α] [preorder β] {f g : β → α} {a : α}

lemma monotone_mul_left_of_nonneg (ha : 0 ≤ a) : monotone (λ x, a*x) :=
by haveI := @linear_order.decidable_le α _; exact
assume b c b_le_c, decidable.mul_le_mul_of_nonneg_left b_le_c ha

lemma monotone_mul_right_of_nonneg (ha : 0 ≤ a) : monotone (λ x, x*a) :=
by haveI := @linear_order.decidable_le α _; exact
assume b c b_le_c, decidable.mul_le_mul_of_nonneg_right b_le_c ha

lemma monotone.mul_const (hf : monotone f) (ha : 0 ≤ a) :
  monotone (λ x, (f x) * a) :=
(monotone_mul_right_of_nonneg ha).comp hf

lemma monotone.const_mul (hf : monotone f) (ha : 0 ≤ a) :
  monotone (λ x, a * (f x)) :=
(monotone_mul_left_of_nonneg ha).comp hf

lemma monotone.mul (hf : monotone f) (hg : monotone g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
  monotone (λ x, f x * g x) :=
by haveI := @linear_order.decidable_le α _; exact
λ x y h, decidable.mul_le_mul (hf h) (hg h) (hg0 x) (hf0 y)

lemma strict_mono_mul_left_of_pos (ha : 0 < a) : strict_mono (λ x, a * x) :=
assume b c b_lt_c, (mul_lt_mul_left ha).2 b_lt_c

lemma strict_mono_mul_right_of_pos (ha : 0 < a) : strict_mono (λ x, x * a) :=
assume b c b_lt_c, (mul_lt_mul_right ha).2 b_lt_c

lemma strict_mono.mul_const (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, (f x) * a) :=
(strict_mono_mul_right_of_pos ha).comp hf

lemma strict_mono.const_mul (hf : strict_mono f) (ha : 0 < a) :
  strict_mono (λ x, a * (f x)) :=
(strict_mono_mul_left_of_pos ha).comp hf

lemma strict_mono.mul_monotone (hf : strict_mono f) (hg : monotone g) (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 < g x) :
  strict_mono (λ x, f x * g x) :=
by haveI := @linear_order.decidable_le α _; exact
λ x y h, decidable.mul_lt_mul (hf h) (hg h.le) (hg0 x) (hf0 y)

lemma monotone.mul_strict_mono (hf : monotone f) (hg : strict_mono g) (hf0 : ∀ x, 0 < f x)
  (hg0 : ∀ x, 0 ≤ g x) :
  strict_mono (λ x, f x * g x) :=
by haveI := @linear_order.decidable_le α _; exact
λ x y h, decidable.mul_lt_mul' (hf h.le) (hg h) (hg0 x) (hf0 y)

lemma strict_mono.mul (hf : strict_mono f) (hg : strict_mono g) (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
  strict_mono (λ x, f x * g x) :=
by haveI := @linear_order.decidable_le α _; exact
λ x y h, decidable.mul_lt_mul'' (hf h) (hg h) (hf0 x) (hg0 x)

end mono

section linear_ordered_semiring
variables [linear_ordered_semiring α] {a b c : α}

lemma mul_max_of_nonneg (b c : α) (ha : 0 ≤ a) : a * max b c = max (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_max

lemma mul_min_of_nonneg (b c : α) (ha : 0 ≤ a) : a * min b c = min (a * b) (a * c) :=
(monotone_mul_left_of_nonneg ha).map_min

lemma max_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : max a b * c = max (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_max

lemma min_mul_of_nonneg (a b : α) (hc : 0 ≤ c) : min a b * c = min (a * c) (b * c) :=
(monotone_mul_right_of_nonneg hc).map_min

end linear_ordered_semiring

/-- An `ordered_ring α` is a ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class ordered_ring (α : Type u) extends ring α, ordered_add_comm_group α :=
(zero_le_one : 0 ≤ (1 : α))
(mul_pos     : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)

section ordered_ring
variables [ordered_ring α] {a b c : α}

-- See Note [decidable namespace]
protected lemma decidable.ordered_ring.mul_nonneg [@decidable_rel α (≤)]
  {a b : α} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b :=
begin
  by_cases ha : a ≤ 0, { simp [le_antisymm ha h₁] },
  by_cases hb : b ≤ 0, { simp [le_antisymm hb h₂] },
  exact (le_not_le_of_lt (ordered_ring.mul_pos a b (h₁.lt_of_not_le ha) (h₂.lt_of_not_le hb))).1,
end

lemma ordered_ring.mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
by classical; exact decidable.ordered_ring.mul_nonneg

-- See Note [decidable namespace]
protected lemma decidable.ordered_ring.mul_le_mul_of_nonneg_left
  [@decidable_rel α (≤)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c * a ≤ c * b :=
begin
  rw [← sub_nonneg, ← mul_sub],
  exact decidable.ordered_ring.mul_nonneg h₂ (sub_nonneg.2 h₁),
end

lemma ordered_ring.mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b :=
by classical; exact decidable.ordered_ring.mul_le_mul_of_nonneg_left

-- See Note [decidable namespace]
protected lemma decidable.ordered_ring.mul_le_mul_of_nonneg_right
  [@decidable_rel α (≤)] (h₁ : a ≤ b) (h₂ : 0 ≤ c) : a * c ≤ b * c :=
begin
  rw [← sub_nonneg, ← sub_mul],
  exact decidable.ordered_ring.mul_nonneg (sub_nonneg.2 h₁) h₂,
end

lemma ordered_ring.mul_le_mul_of_nonneg_right : a ≤ b → 0 ≤ c → a * c ≤ b * c :=
by classical; exact decidable.ordered_ring.mul_le_mul_of_nonneg_right

lemma ordered_ring.mul_lt_mul_of_pos_left (h₁ : a < b) (h₂ : 0 < c) : c * a < c * b :=
begin
  rw [← sub_pos, ← mul_sub],
  exact ordered_ring.mul_pos _ _ h₂ (sub_pos.2 h₁),
end

lemma ordered_ring.mul_lt_mul_of_pos_right (h₁ : a < b) (h₂ : 0 < c) : a * c < b * c :=
begin
  rw [← sub_pos, ← sub_mul],
  exact ordered_ring.mul_pos _ _ (sub_pos.2 h₁) h₂,
end

@[priority 100] -- see Note [lower instance priority]
instance ordered_ring.to_ordered_semiring : ordered_semiring α :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _ _ _,
  mul_lt_mul_of_pos_left     := @ordered_ring.mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @ordered_ring.mul_lt_mul_of_pos_right α _,
  ..‹ordered_ring α› }

-- See Note [decidable namespace]
protected lemma decidable.mul_le_mul_of_nonpos_left [@decidable_rel α (≤)]
  {a b c : α} (h : b ≤ a) (hc : c ≤ 0) : c * a ≤ c * b :=
have -c ≥ 0,              from neg_nonneg_of_nonpos hc,
have -c * b ≤ -c * a,     from decidable.mul_le_mul_of_nonneg_left h this,
have -(c * b) ≤ -(c * a), by rwa [neg_mul, neg_mul] at this,
le_of_neg_le_neg this

lemma mul_le_mul_of_nonpos_left {a b c : α} : b ≤ a → c ≤ 0 → c * a ≤ c * b :=
by classical; exact decidable.mul_le_mul_of_nonpos_left

-- See Note [decidable namespace]
protected lemma decidable.mul_le_mul_of_nonpos_right [@decidable_rel α (≤)]
  {a b c : α} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c :=
have -c ≥ 0,              from neg_nonneg_of_nonpos hc,
have b * -c ≤ a * -c,     from decidable.mul_le_mul_of_nonneg_right h this,
have -(b * c) ≤ -(a * c), by rwa [mul_neg, mul_neg] at this,
le_of_neg_le_neg this

lemma mul_le_mul_of_nonpos_right {a b c : α} : b ≤ a → c ≤ 0 → a * c ≤ b * c :=
by classical; exact decidable.mul_le_mul_of_nonpos_right

-- See Note [decidable namespace]
protected lemma decidable.mul_nonneg_of_nonpos_of_nonpos [@decidable_rel α (≤)]
  {a b : α} (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b :=
have 0 * b ≤ a * b, from decidable.mul_le_mul_of_nonpos_right ha hb,
by rwa zero_mul at this

lemma mul_nonneg_of_nonpos_of_nonpos {a b : α} : a ≤ 0 → b ≤ 0 → 0 ≤ a * b :=
by classical; exact decidable.mul_nonneg_of_nonpos_of_nonpos

lemma mul_lt_mul_of_neg_left {a b c : α} (h : b < a) (hc : c < 0) : c * a < c * b :=
have -c > 0,              from neg_pos_of_neg hc,
have -c * b < -c * a,     from mul_lt_mul_of_pos_left h this,
have -(c * b) < -(c * a), by rwa [neg_mul, neg_mul] at this,
lt_of_neg_lt_neg this

lemma mul_lt_mul_of_neg_right {a b c : α} (h : b < a) (hc : c < 0) : a * c < b * c :=
have -c > 0,              from neg_pos_of_neg hc,
have b * -c < a * -c,     from mul_lt_mul_of_pos_right h this,
have -(b * c) < -(a * c), by rwa [mul_neg, mul_neg] at this,
lt_of_neg_lt_neg this

lemma mul_pos_of_neg_of_neg {a b : α} (ha : a < 0) (hb : b < 0) : 0 < a * b :=
have 0 * b < a * b, from mul_lt_mul_of_neg_right ha hb,
by rwa zero_mul at this

/-- Pullback an `ordered_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.ordered_ring {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  ordered_ring β :=
{ mul_pos := λ a b a0 b0, show f 0 < f (a * b), by { rw [zero, mul], apply mul_pos; rwa ← zero },
  ..hf.ordered_semiring f zero one add mul,
  ..hf.ring f zero one add mul neg sub }

lemma le_iff_exists_nonneg_add (a b : α) : a ≤ b ↔ ∃ c ≥ 0, b = a + c :=
⟨λ h, ⟨b - a, sub_nonneg.mpr h, by simp⟩,
  λ ⟨c, hc, h⟩, by { rw [h, le_add_iff_nonneg_right], exact hc }⟩

end ordered_ring

section ordered_comm_ring

/-- An `ordered_comm_ring α` is a commutative ring `α` with a partial order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class ordered_comm_ring (α : Type u) extends ordered_ring α, comm_ring α

@[priority 100] -- See note [lower instance priority]
instance ordered_comm_ring.to_ordered_comm_semiring {α : Type u} [ordered_comm_ring α] :
  ordered_comm_semiring α :=
{ .. (by apply_instance : ordered_semiring α),
  .. ‹ordered_comm_ring α› }

/-- Pullback an `ordered_comm_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.ordered_comm_ring [ordered_comm_ring α] {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (- x) = - f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  ordered_comm_ring β :=
{ ..hf.ordered_ring f zero one add mul neg sub,
  ..hf.comm_ring f zero one add mul neg sub }

end ordered_comm_ring

/-- A `linear_ordered_ring α` is a ring `α` with a linear order such that
addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj] class linear_ordered_ring (α : Type u)
  extends ordered_ring α, linear_order α, nontrivial α

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_linear_ordered_add_comm_group [s : linear_ordered_ring α] :
  linear_ordered_add_comm_group α :=
{ .. s }

section linear_ordered_ring
variables [linear_ordered_ring α] {a b c : α}

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.to_linear_ordered_semiring : linear_ordered_semiring α :=
{ mul_zero                   := mul_zero,
  zero_mul                   := zero_mul,
  add_left_cancel            := @add_left_cancel α _,
  le_of_add_le_add_left      := @le_of_add_le_add_left α _ _ _,
  mul_lt_mul_of_pos_left     := @mul_lt_mul_of_pos_left α _,
  mul_lt_mul_of_pos_right    := @mul_lt_mul_of_pos_right α _,
  le_total                   := linear_ordered_ring.le_total,
  ..‹linear_ordered_ring α› }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_ring.is_domain : is_domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros a b hab,
      refine decidable.or_iff_not_and_not.2 (λ h, _), revert hab,
      cases lt_or_gt_of_ne h.1 with ha ha; cases lt_or_gt_of_ne h.2 with hb hb,
      exacts [(mul_pos_of_neg_of_neg ha hb).ne.symm, (mul_neg_of_neg_of_pos ha hb).ne,
        (mul_neg_of_pos_of_neg ha hb).ne, (mul_pos ha hb).ne.symm]
    end,
  .. ‹linear_ordered_ring α› }

@[simp] lemma abs_one : |(1 : α)| = 1 := abs_of_pos zero_lt_one
@[simp] lemma abs_two : |(2 : α)| = 2 := abs_of_pos zero_lt_two

lemma abs_mul (a b : α) : |a * b| = |a| * |b| :=
begin
  haveI := @linear_order.decidable_le α _,
  rw [abs_eq (decidable.mul_nonneg (abs_nonneg a) (abs_nonneg b))],
  cases le_total a 0 with ha ha; cases le_total b 0 with hb hb;
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, eq_self_iff_true,
      neg_mul, mul_neg, neg_neg, *]
end

/-- `abs` as a `monoid_with_zero_hom`. -/
def abs_hom : α →*₀ α := ⟨abs, abs_zero, abs_one, abs_mul⟩

@[simp] lemma abs_mul_abs_self (a : α) : |a| * |a| = a * a :=
abs_by_cases (λ x, x * x = a * a) rfl (neg_mul_neg a a)

@[simp] lemma abs_mul_self (a : α) : |a * a| = a * a :=
by rw [abs_mul, abs_mul_abs_self]

lemma mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
⟨pos_and_pos_or_neg_and_neg_of_mul_pos,
  λ h, h.elim (and_imp.2 mul_pos) (and_imp.2 mul_pos_of_neg_of_neg)⟩

lemma mul_neg_iff : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b :=
by rw [← neg_pos, neg_mul_eq_mul_neg, mul_pos_iff, neg_pos, neg_lt_zero]

lemma mul_nonneg_iff : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 :=
by haveI := @linear_order.decidable_le α _; exact
⟨nonneg_and_nonneg_or_nonpos_and_nonpos_of_mul_nnonneg,
  λ h, h.elim (and_imp.2 decidable.mul_nonneg) (and_imp.2 decidable.mul_nonneg_of_nonpos_of_nonpos)⟩

/-- Out of three elements of a `linear_ordered_ring`, two must have the same sign. -/
lemma mul_nonneg_of_three (a b c : α) :
  0 ≤ a * b ∨ 0 ≤ b * c ∨ 0 ≤ c * a :=
by iterate 3 { rw mul_nonneg_iff };
  have := le_total 0 a; have := le_total 0 b; have := le_total 0 c; itauto

lemma mul_nonpos_iff : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b :=
by rw [← neg_nonneg, neg_mul_eq_mul_neg, mul_nonneg_iff, neg_nonneg, neg_nonpos]

lemma mul_self_nonneg (a : α) : 0 ≤ a * a :=
abs_mul_self a ▸ abs_nonneg _

@[simp] lemma neg_le_self_iff : -a ≤ a ↔ 0 ≤ a :=
by simp [neg_le_iff_add_nonneg, ← two_mul, mul_nonneg_iff, zero_le_one, (@zero_lt_two α _ _).not_le]

@[simp] lemma neg_lt_self_iff : -a < a ↔ 0 < a :=
by simp [neg_lt_iff_pos_add, ← two_mul, mul_pos_iff, zero_lt_one, (@zero_lt_two α _ _).not_lt]

@[simp] lemma le_neg_self_iff : a ≤ -a ↔ a ≤ 0 :=
calc a ≤ -a ↔ -(-a) ≤ -a : by rw neg_neg
... ↔ 0 ≤ -a : neg_le_self_iff
... ↔ a ≤ 0 : neg_nonneg

@[simp] lemma lt_neg_self_iff : a < -a ↔ a < 0 :=
calc a < -a ↔ -(-a) < -a : by rw neg_neg
... ↔ 0 < -a : neg_lt_self_iff
... ↔ a < 0 : neg_pos

@[simp] lemma abs_eq_self : |a| = a ↔ 0 ≤ a := by simp [abs_eq_max_neg]

@[simp] lemma abs_eq_neg_self : |a| = -a ↔ a ≤ 0 := by simp [abs_eq_max_neg]

/-- For an element `a` of a linear ordered ring, either `abs a = a` and `0 ≤ a`,
    or `abs a = -a` and `a < 0`.
    Use cases on this lemma to automate linarith in inequalities -/
lemma abs_cases (a : α) : (|a| = a ∧ 0 ≤ a) ∨ (|a| = -a ∧ a < 0) :=
begin
  by_cases 0 ≤ a,
  { left,
    exact ⟨abs_eq_self.mpr h, h⟩ },
  { right,
    push_neg at h,
    exact ⟨abs_eq_neg_self.mpr (le_of_lt h), h⟩ }
end

lemma gt_of_mul_lt_mul_neg_left (h : c * a < c * b) (hc : c ≤ 0) : b < a :=
have nhc : 0 ≤ -c, from neg_nonneg_of_nonpos hc,
have h2 : -(c * b) < -(c * a), from neg_lt_neg h,
have h3 : (-c) * b < (-c) * a, from calc
     (-c) * b = - (c * b)    : by rewrite neg_mul_eq_neg_mul
          ... < -(c * a)     : h2
          ... = (-c) * a     : by rewrite neg_mul_eq_neg_mul,
lt_of_mul_lt_mul_left h3 nhc

lemma neg_one_lt_zero : -1 < (0:α) := neg_lt_zero.2 zero_lt_one

lemma le_of_mul_le_of_one_le {a b c : α} (h : a * c ≤ b) (hb : 0 ≤ b) (hc : 1 ≤ c) : a ≤ b :=
by haveI := @linear_order.decidable_le α _; exact
have h' : a * c ≤ b * c, from calc
     a * c ≤ b : h
       ... = b * 1 : by rewrite mul_one
       ... ≤ b * c : decidable.mul_le_mul_of_nonneg_left hc hb,
le_of_mul_le_mul_right h' (zero_lt_one.trans_le hc)

lemma nonneg_le_nonneg_of_sq_le_sq {a b : α} (hb : 0 ≤ b) (h : a * a ≤ b * b) : a ≤ b :=
by haveI := @linear_order.decidable_le α _; exact
le_of_not_gt (λhab, (decidable.mul_self_lt_mul_self hb hab).not_le h)

lemma mul_self_le_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a ≤ b ↔ a * a ≤ b * b :=
by haveI := @linear_order.decidable_le α _; exact
⟨decidable.mul_self_le_mul_self h1, nonneg_le_nonneg_of_sq_le_sq h2⟩

lemma mul_self_lt_mul_self_iff {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a < b ↔ a * a < b * b :=
by haveI := @linear_order.decidable_le α _; exact
((@decidable.strict_mono_on_mul_self α _ _).lt_iff_lt h1 h2).symm

lemma mul_self_inj {a b : α} (h1 : 0 ≤ a) (h2 : 0 ≤ b) : a * a = b * b ↔ a = b :=
by haveI := @linear_order.decidable_le α _; exact
(@decidable.strict_mono_on_mul_self α _ _).inj_on.eq_iff h1 h2

@[simp] lemma mul_le_mul_left_of_neg {a b c : α} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a :=
by haveI := @linear_order.decidable_le α _; exact
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_left h' h,
  λ h', decidable.mul_le_mul_of_nonpos_left h' h.le⟩

@[simp] lemma mul_le_mul_right_of_neg {a b c : α} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a :=
by haveI := @linear_order.decidable_le α _; exact
⟨le_imp_le_of_lt_imp_lt $ λ h', mul_lt_mul_of_neg_right h' h,
  λ h', decidable.mul_le_mul_of_nonpos_right h' h.le⟩

@[simp] lemma mul_lt_mul_left_of_neg {a b c : α} (h : c < 0) : c * a < c * b ↔ b < a :=
lt_iff_lt_of_le_iff_le (mul_le_mul_left_of_neg h)

@[simp] lemma mul_lt_mul_right_of_neg {a b c : α} (h : c < 0) : a * c < b * c ↔ b < a :=
lt_iff_lt_of_le_iff_le (mul_le_mul_right_of_neg h)

lemma sub_one_lt (a : α) : a - 1 < a :=
sub_lt_iff_lt_add.2 (lt_add_one a)

@[simp] lemma mul_self_pos {a : α} : 0 < a * a ↔ a ≠ 0 :=
begin
  split,
  { rintro h rfl, rw mul_zero at h, exact h.false },
  { intro h,
    cases h.lt_or_lt with h h,
    exacts [mul_pos_of_neg_of_neg h h, mul_pos h h] }
end

lemma mul_self_le_mul_self_of_le_of_neg_le {x y : α} (h₁ : x ≤ y) (h₂ : -x ≤ y) : x * x ≤ y * y :=
begin
  haveI := @linear_order.decidable_le α _,
  rw [← abs_mul_abs_self x],
  exact decidable.mul_self_le_mul_self (abs_nonneg x) (abs_le.2 ⟨neg_le.2 h₂, h₁⟩)
end

lemma nonneg_of_mul_nonpos_left {a b : α} (h : a * b ≤ 0) (hb : b < 0) : 0 ≤ a :=
le_of_not_gt (λ ha, absurd h (mul_pos_of_neg_of_neg ha hb).not_le)

lemma nonneg_of_mul_nonpos_right {a b : α} (h : a * b ≤ 0) (ha : a < 0) : 0 ≤ b :=
le_of_not_gt (λ hb, absurd h (mul_pos_of_neg_of_neg ha hb).not_le)

lemma pos_of_mul_neg_left {a b : α} (h : a * b < 0) (hb : b ≤ 0) : 0 < a :=
by haveI := @linear_order.decidable_le α _; exact
lt_of_not_ge (λ ha, absurd h (decidable.mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt)

lemma pos_of_mul_neg_right {a b : α} (h : a * b < 0) (ha : a ≤ 0) : 0 < b :=
by haveI := @linear_order.decidable_le α _; exact
lt_of_not_ge (λ hb, absurd h (decidable.mul_nonneg_of_nonpos_of_nonpos ha hb).not_lt)

lemma neg_iff_pos_of_mul_neg (hab : a * b < 0) : a < 0 ↔ 0 < b :=
⟨pos_of_mul_neg_right hab ∘ le_of_lt, neg_of_mul_neg_right hab ∘ le_of_lt⟩

lemma pos_iff_neg_of_mul_neg (hab : a * b < 0) : 0 < a ↔ b < 0 :=
⟨neg_of_mul_neg_left hab ∘ le_of_lt, pos_of_mul_neg_left hab ∘ le_of_lt⟩

/-- The sum of two squares is zero iff both elements are zero. -/
lemma mul_self_add_mul_self_eq_zero {x y : α} : x * x + y * y = 0 ↔ x = 0 ∧ y = 0 :=
by rw [add_eq_zero_iff', mul_self_eq_zero, mul_self_eq_zero]; apply mul_self_nonneg

lemma eq_zero_of_mul_self_add_mul_self_eq_zero (h : a * a + b * b = 0) : a = 0 :=
(mul_self_add_mul_self_eq_zero.mp h).left

lemma abs_eq_iff_mul_self_eq : |a| = |b| ↔ a * a = b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact (mul_self_inj (abs_nonneg a) (abs_nonneg b)).symm,
end

lemma abs_lt_iff_mul_self_lt : |a| < |b| ↔ a * a < b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact mul_self_lt_mul_self_iff (abs_nonneg a) (abs_nonneg b)
end

lemma abs_le_iff_mul_self_le : |a| ≤ |b| ↔ a * a ≤ b * b :=
begin
  rw [← abs_mul_abs_self, ← abs_mul_abs_self b],
  exact mul_self_le_mul_self_iff (abs_nonneg a) (abs_nonneg b)
end

lemma abs_le_one_iff_mul_self_le_one : |a| ≤ 1 ↔ a * a ≤ 1 :=
by simpa only [abs_one, one_mul] using @abs_le_iff_mul_self_le α _ a 1

/-- Pullback a `linear_ordered_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.linear_ordered_ring {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  linear_ordered_ring β :=
{ .. linear_order.lift f hf,
  .. pullback_nonzero f zero one,
  .. hf.ordered_ring f zero one add mul neg sub }

end linear_ordered_ring

/-- A `linear_ordered_comm_ring α` is a commutative ring `α` with a linear order
such that addition is monotone and multiplication by a positive number is strictly monotone. -/
@[protect_proj]
class linear_ordered_comm_ring (α : Type u) extends linear_ordered_ring α, comm_monoid α

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_ordered_comm_ring [d : linear_ordered_comm_ring α] :
  ordered_comm_ring α :=
{ ..d }

@[priority 100] -- see Note [lower instance priority]
instance linear_ordered_comm_ring.to_linear_ordered_semiring [d : linear_ordered_comm_ring α] :
   linear_ordered_semiring α :=
{ .. d, ..linear_ordered_ring.to_linear_ordered_semiring }

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring α] {a b c d : α}

lemma max_mul_mul_le_max_mul_max (b c : α) (ha : 0 ≤ a) (hd: 0 ≤ d) :
  max (a * b) (d * c) ≤ max a c * max d b :=
by haveI := @linear_order.decidable_le α _; exact
have ba : b * a ≤ max d b * max c a, from
  decidable.mul_le_mul (le_max_right d b) (le_max_right c a) ha (le_trans hd (le_max_left d b)),
have cd : c * d ≤ max a c * max b d, from
  decidable.mul_le_mul (le_max_right a c) (le_max_right b d) hd (le_trans ha (le_max_left a c)),
max_le
  (by simpa [mul_comm, max_comm] using ba)
  (by simpa [mul_comm, max_comm] using cd)

lemma abs_sub_sq (a b : α) : |a - b| * |a - b| = a * a + b * b - (1 + 1) * a * b :=
begin
  rw abs_mul_abs_self,
  simp only [mul_add, add_comm, add_left_comm, mul_comm, sub_eq_add_neg,
    mul_one, mul_neg, neg_add_rev, neg_neg],
end

end linear_ordered_comm_ring
section
variables [ring α] [linear_order α] {a b : α}

@[simp] lemma abs_dvd (a b : α) : |a| ∣ b ↔ a ∣ b :=
by { cases abs_choice a with h h; simp only [h, neg_dvd] }

lemma abs_dvd_self (a : α) : |a| ∣ a :=
(abs_dvd a a).mpr (dvd_refl a)

@[simp] lemma dvd_abs (a b : α) : a ∣ |b| ↔ a ∣ b :=
by { cases abs_choice b with h h; simp only [h, dvd_neg] }

lemma self_dvd_abs (a : α) : a ∣ |a| :=
(dvd_abs a a).mpr (dvd_refl a)

lemma abs_dvd_abs (a b : α) : |a| ∣ |b| ↔ a ∣ b :=
(abs_dvd _ _).trans (dvd_abs _ _)

lemma even_abs {a : α} : even (|a|) ↔ even a :=
dvd_abs _ _

lemma odd_abs {a : α} : odd (abs a) ↔ odd a :=
by { cases abs_choice a with h h; simp only [h, odd_neg] }

end

section linear_ordered_comm_ring

variables [linear_ordered_comm_ring α]

/-- Pullback a `linear_ordered_comm_ring` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def function.injective.linear_ordered_comm_ring {β : Type*}
  [has_zero β] [has_one β] [has_add β] [has_mul β] [has_neg β] [has_sub β]
  (f : β → α) (hf : function.injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
  (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y) :
  linear_ordered_comm_ring β :=
{ .. linear_order.lift f hf,
  .. pullback_nonzero f zero one,
  .. hf.ordered_comm_ring f zero one add mul neg sub }

end linear_ordered_comm_ring

namespace ring

/-- A positive cone in a ring consists of a positive cone in underlying `add_comm_group`,
which contains `1` and such that the positive elements are closed under multiplication. -/
@[nolint has_inhabited_instance]
structure positive_cone (α : Type*) [ring α] extends add_comm_group.positive_cone α :=
(one_nonneg : nonneg 1)
(mul_pos : ∀ (a b), pos a → pos b → pos (a * b))

/-- Forget that a positive cone in a ring respects the multiplicative structure. -/
add_decl_doc positive_cone.to_positive_cone

/-- A positive cone in a ring induces a linear order if `1` is a positive element. -/
@[nolint has_inhabited_instance]
structure total_positive_cone (α : Type*) [ring α]
  extends positive_cone α, add_comm_group.total_positive_cone α :=
(one_pos : pos 1)

/-- Forget that a `total_positive_cone` in a ring is total. -/
add_decl_doc total_positive_cone.to_positive_cone

/-- Forget that a `total_positive_cone` in a ring respects the multiplicative structure. -/
add_decl_doc total_positive_cone.to_total_positive_cone

end ring

namespace ordered_ring

open ring

/-- Construct an `ordered_ring` by
designating a positive cone in an existing `ring`. -/
def mk_of_positive_cone {α : Type*} [ring α] (C : positive_cone α) :
  ordered_ring α :=
{ zero_le_one := by { change C.nonneg (1 - 0), convert C.one_nonneg, simp, },
  mul_pos := λ x y xp yp, begin
    change C.pos (x*y - 0),
    convert C.mul_pos x y (by { convert xp, simp, }) (by { convert yp, simp, }),
    simp,
  end,
  ..‹ring α›,
  ..ordered_add_comm_group.mk_of_positive_cone C.to_positive_cone }

end ordered_ring

namespace linear_ordered_ring

open ring

/-- Construct a `linear_ordered_ring` by
designating a positive cone in an existing `ring`. -/
def mk_of_positive_cone {α : Type*} [ring α] (C : total_positive_cone α) :
  linear_ordered_ring α :=
{ exists_pair_ne := ⟨0, 1, begin
    intro h,
    have one_pos := C.one_pos,
    rw [←h, C.pos_iff] at one_pos,
    simpa using one_pos,
  end⟩,
  ..ordered_ring.mk_of_positive_cone C.to_positive_cone,
  ..linear_ordered_add_comm_group.mk_of_positive_cone C.to_total_positive_cone, }

end linear_ordered_ring

/-- A canonically ordered commutative semiring is an ordered, commutative semiring
in which `a ≤ b` iff there exists `c` with `b = a + c`. This is satisfied by the
natural numbers, for example, but not the integers or other ordered groups. -/
@[protect_proj]
class canonically_ordered_comm_semiring (α : Type*) extends
  canonically_ordered_add_monoid α, comm_semiring α :=
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

namespace canonically_ordered_comm_semiring
variables [canonically_ordered_comm_semiring α] {a b : α}

@[priority 100] -- see Note [lower instance priority]
instance to_no_zero_divisors : no_zero_divisors α :=
⟨canonically_ordered_comm_semiring.eq_zero_or_eq_zero_of_mul_eq_zero⟩

@[priority 100] -- see Note [lower instance priority]
instance to_covariant_mul_le : covariant_class α α (*) (≤) :=
begin
  refine ⟨λ a b c h, _⟩,
  rcases le_iff_exists_add.1 h with ⟨c, rfl⟩,
  rw mul_add,
  apply self_le_add_right
end

/-- A version of `zero_lt_one : 0 < 1` for a `canonically_ordered_comm_semiring`. -/
lemma zero_lt_one [nontrivial α] : (0:α) < 1 := (zero_le 1).lt_of_ne zero_ne_one

@[simp] lemma mul_pos : 0 < a * b ↔ (0 < a) ∧ (0 < b) :=
by simp only [pos_iff_ne_zero, ne.def, mul_eq_zero, not_or_distrib]


end canonically_ordered_comm_semiring

section sub

variables [canonically_ordered_comm_semiring α] {a b c : α}
variables [has_sub α] [has_ordered_sub α]

variables [is_total α (≤)]

namespace add_le_cancellable
protected lemma mul_tsub (h : add_le_cancellable (a * c)) :
  a * (b - c) = a * b - a * c :=
begin
  cases total_of (≤) b c with hbc hcb,
  { rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)] },
  { apply h.eq_tsub_of_add_eq, rw [← mul_add, tsub_add_cancel_of_le hcb] }
end

protected lemma tsub_mul (h : add_le_cancellable (b * c)) : (a - b) * c = a * c - b * c :=
by { simp only [mul_comm _ c] at *, exact h.mul_tsub }

end add_le_cancellable

variables [contravariant_class α α (+) (≤)]

lemma mul_tsub (a b c : α) : a * (b - c) = a * b - a * c :=
contravariant.add_le_cancellable.mul_tsub

lemma tsub_mul (a b c : α) : (a - b) * c = a * c - b * c :=
contravariant.add_le_cancellable.tsub_mul

end sub

/-! ### Structures involving `*` and `0` on `with_top` and `with_bot`

The main results of this section are `with_top.canonically_ordered_comm_semiring` and
`with_bot.comm_monoid_with_zero`.
-/

namespace with_top

instance [nonempty α] : nontrivial (with_top α) :=
option.nontrivial

variable [decidable_eq α]

section has_mul

variables [has_zero α] [has_mul α]

instance : mul_zero_class (with_top α) :=
{ zero := 0,
  mul := λm n, if m = 0 ∨ n = 0 then 0 else m.bind (λa, n.bind $ λb, ↑(a * b)),
  zero_mul := assume a, if_pos $ or.inl rfl,
  mul_zero := assume a, if_pos $ or.inr rfl }

lemma mul_def {a b : with_top α} :
  a * b = if a = 0 ∨ b = 0 then 0 else a.bind (λa, b.bind $ λb, ↑(a * b)) := rfl

@[simp] lemma mul_top {a : with_top α} (h : a ≠ 0) : a * ⊤ = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul {a : with_top α} (h : a ≠ 0) : ⊤ * a = ⊤ :=
by cases a; simp [mul_def, h]; refl

@[simp] lemma top_mul_top : (⊤ * ⊤ : with_top α) = ⊤ :=
top_mul top_ne_zero

end has_mul

section mul_zero_class

variables [mul_zero_class α]

@[norm_cast] lemma coe_mul {a b : α} : (↑(a * b) : with_top α) = a * b :=
decidable.by_cases (assume : a = 0, by simp [this]) $ assume ha,
decidable.by_cases (assume : b = 0, by simp [this]) $ assume hb,
by { simp [*, mul_def], refl }

lemma mul_coe {b : α} (hb : b ≠ 0) : ∀{a : with_top α}, a * b = a.bind (λa:α, ↑(a * b))
| none     := show (if (⊤:with_top α) = 0 ∨ (b:with_top α) = 0 then 0 else ⊤ : with_top α) = ⊤,
    by simp [hb]
| (some a) := show ↑a * ↑b = ↑(a * b), from coe_mul.symm

@[simp] lemma mul_eq_top_iff {a b : with_top α} : a * b = ⊤ ↔ (a ≠ 0 ∧ b = ⊤) ∨ (a = ⊤ ∧ b ≠ 0) :=
begin
  cases a; cases b; simp only [none_eq_top, some_eq_coe],
  { simp [← coe_mul] },
  { suffices : ⊤ * (b : with_top α) = ⊤ ↔ b ≠ 0, by simpa,
    by_cases hb : b = 0; simp [hb] },
  { suffices : (a : with_top α) * ⊤ = ⊤ ↔ a ≠ 0, by simpa,
    by_cases ha : a = 0; simp [ha] },
  { simp [← coe_mul] }
end

lemma mul_lt_top [partial_order α] {a b : with_top α} (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a * b < ⊤ :=
begin
  lift a to α using ha,
  lift b to α using hb,
  simp only [← coe_mul, coe_lt_top]
end

end mul_zero_class

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊤ = ⊤` but also `= 0 * ⊤ = 0`. -/
instance [mul_zero_one_class α] [nontrivial α] : mul_zero_one_class (with_top α) :=
{ mul := (*),
  one := 1,
  zero := 0,
  one_mul := λ a, match a with
  | none     := show ((1:α) : with_top α) * ⊤ = ⊤, by simp [-with_top.coe_one]
  | (some a) := show ((1:α) : with_top α) * a = a, by simp [coe_mul.symm, -with_top.coe_one]
  end,
  mul_one := λ a, match a with
  | none     := show ⊤ * ((1:α) : with_top α) = ⊤, by simp [-with_top.coe_one]
  | (some a) := show ↑a * ((1:α) : with_top α) = a, by simp [coe_mul.symm, -with_top.coe_one]
  end,
  .. with_top.mul_zero_class }

instance [mul_zero_class α] [no_zero_divisors α] : no_zero_divisors (with_top α) :=
⟨λ a b, by cases a; cases b; dsimp [mul_def]; split_ifs;
  simp [*, none_eq_top, some_eq_coe, mul_eq_zero] at *⟩

instance [semigroup_with_zero α] [no_zero_divisors α] : semigroup_with_zero (with_top α) :=
{ mul := (*),
  zero := 0,
  mul_assoc := λ a b c, begin
    cases a,
    { by_cases hb : b = 0; by_cases hc : c = 0;
        simp [*, none_eq_top] },
    cases b,
    { by_cases ha : a = 0; by_cases hc : c = 0;
        simp [*, none_eq_top, some_eq_coe] },
    cases c,
    { by_cases ha : a = 0; by_cases hb : b = 0;
        simp [*, none_eq_top, some_eq_coe] },
    simp [some_eq_coe, coe_mul.symm, mul_assoc]
  end,
  .. with_top.mul_zero_class }

instance [monoid_with_zero α] [no_zero_divisors α] [nontrivial α] : monoid_with_zero (with_top α) :=
{ .. with_top.mul_zero_one_class, .. with_top.semigroup_with_zero }

instance [comm_monoid_with_zero α] [no_zero_divisors α] [nontrivial α] :
  comm_monoid_with_zero (with_top α) :=
{ mul := (*),
  zero := 0,
  mul_comm := λ a b, begin
    by_cases ha : a = 0, { simp [ha] },
    by_cases hb : b = 0, { simp [hb] },
    simp [ha, hb, mul_def, option.bind_comm a b, mul_comm]
  end,
  .. with_top.monoid_with_zero }

variables [canonically_ordered_comm_semiring α]

private lemma distrib' (a b c : with_top α) : (a + b) * c = a * c + b * c :=
begin
  cases c,
  { show (a + b) * ⊤ = a * ⊤ + b * ⊤,
    by_cases ha : a = 0; simp [ha] },
  { show (a + b) * c = a * c + b * c,
    by_cases hc : c = 0, { simp [hc] },
    simp [mul_coe hc], cases a; cases b,
    repeat { refl <|> exact congr_arg some (add_mul _ _ _) } }
end

/-- This instance requires `canonically_ordered_comm_semiring` as it is the smallest class
that derives from both `non_assoc_non_unital_semiring` and `canonically_ordered_add_monoid`, both
of which are required for distributivity. -/
instance [nontrivial α] : comm_semiring (with_top α) :=
{ right_distrib   := distrib',
  left_distrib    := assume a b c, by rw [mul_comm, distrib', mul_comm b, mul_comm c]; refl,
  .. with_top.add_comm_monoid, .. with_top.comm_monoid_with_zero,}

instance [nontrivial α] : canonically_ordered_comm_semiring (with_top α) :=
{ .. with_top.comm_semiring,
  .. with_top.canonically_ordered_add_monoid,
  .. with_top.no_zero_divisors, }

end with_top

namespace with_bot

instance [nonempty α] : nontrivial (with_bot α) :=
option.nontrivial

variable [decidable_eq α]

section has_mul

variables [has_zero α] [has_mul α]

instance : mul_zero_class (with_bot α) :=
with_top.mul_zero_class

lemma mul_def {a b : with_bot α} :
  a * b = if a = 0 ∨ b = 0 then 0 else a.bind (λa, b.bind $ λb, ↑(a * b)) := rfl

@[simp] lemma mul_bot {a : with_bot α} (h : a ≠ 0) : a * ⊥ = ⊥ :=
with_top.mul_top h

@[simp] lemma bot_mul {a : with_bot α} (h : a ≠ 0) : ⊥ * a = ⊥ :=
with_top.top_mul h

@[simp] lemma bot_mul_bot : (⊥ * ⊥ : with_bot α) = ⊥ :=
with_top.top_mul_top

end has_mul

section mul_zero_class

variables [mul_zero_class α]

@[norm_cast] lemma coe_mul {a b : α} : (↑(a * b) : with_bot α) = a * b :=
decidable.by_cases (assume : a = 0, by simp [this]) $ assume ha,
decidable.by_cases (assume : b = 0, by simp [this]) $ assume hb,
by { simp [*, mul_def], refl }

lemma mul_coe {b : α} (hb : b ≠ 0) {a : with_bot α} : a * b = a.bind (λa:α, ↑(a * b)) :=
with_top.mul_coe hb

@[simp] lemma mul_eq_bot_iff {a b : with_bot α} : a * b = ⊥ ↔ (a ≠ 0 ∧ b = ⊥) ∨ (a = ⊥ ∧ b ≠ 0) :=
with_top.mul_eq_top_iff

lemma bot_lt_mul [partial_order α] {a b : with_bot α} (ha : ⊥ < a) (hb : ⊥ < b) : ⊥ < a * b :=
begin
  lift a to α using ne_bot_of_gt ha,
  lift b to α using ne_bot_of_gt hb,
  simp only [← coe_mul, bot_lt_coe],
end

end mul_zero_class

/-- `nontrivial α` is needed here as otherwise we have `1 * ⊥ = ⊥` but also `= 0 * ⊥ = 0`. -/
instance [mul_zero_one_class α] [nontrivial α] : mul_zero_one_class (with_bot α) :=
with_top.mul_zero_one_class

instance [mul_zero_class α] [no_zero_divisors α] : no_zero_divisors (with_bot α) :=
with_top.no_zero_divisors

instance [semigroup_with_zero α] [no_zero_divisors α] : semigroup_with_zero (with_bot α) :=
with_top.semigroup_with_zero

instance [monoid_with_zero α] [no_zero_divisors α] [nontrivial α] : monoid_with_zero (with_bot α) :=
with_top.monoid_with_zero

instance [comm_monoid_with_zero α] [no_zero_divisors α] [nontrivial α] :
  comm_monoid_with_zero (with_bot α) :=
with_top.comm_monoid_with_zero

instance [canonically_ordered_comm_semiring α] [nontrivial α] : comm_semiring (with_bot α) :=
with_top.comm_semiring

end with_bot
