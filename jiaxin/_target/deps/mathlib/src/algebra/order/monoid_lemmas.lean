/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl, Damiano Testa
-/
import algebra.covariant_and_contravariant
import order.monotone

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.

## Remark

Almost no monoid is actually present in this file: most assumptions have been generalized to
`has_mul` or `mul_one_class`.

-/

-- TODO: If possible, uniformize lemma names, taking special care of `'`,
-- after the `ordered`-refactor is done.

open function

variables {α β : Type*}

section has_mul
variables [has_mul α]

section has_le
variables [has_le α]

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_left]
lemma mul_le_mul_left' [covariant_class α α (*) (≤)] {b c : α} (bc : b ≤ c) (a : α) :
  a * b ≤ a * c :=
covariant_class.elim _ bc

@[to_additive le_of_add_le_add_left]
lemma le_of_mul_le_mul_left' [contravariant_class α α (*) (≤)]
  {a b c : α} (bc : a * b ≤ a * c) :
  b ≤ c :=
contravariant_class.elim _ bc

/- The prime on this lemma is present only on the multiplicative version.  The unprimed version
is taken by the analogous lemma for semiring, with an extra non-negativity assumption. -/
@[to_additive add_le_add_right]
lemma mul_le_mul_right' [covariant_class α α (swap (*)) (≤)]
  {b c : α} (bc : b ≤ c) (a : α) :
  b * a ≤ c * a :=
covariant_class.elim a bc

@[to_additive le_of_add_le_add_right]
lemma le_of_mul_le_mul_right' [contravariant_class α α (swap (*)) (≤)]
  {a b c : α} (bc : b * a ≤ c * a) :
  b ≤ c :=
contravariant_class.elim a bc

@[simp, to_additive]
lemma mul_le_mul_iff_left [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b c : α} :
  a * b ≤ a * c ↔ b ≤ c :=
rel_iff_cov α α (*) (≤) a

@[simp, to_additive]
lemma mul_le_mul_iff_right
  [covariant_class α α (swap (*)) (≤)] [contravariant_class α α (swap (*)) (≤)]
  (a : α) {b c : α} :
  b * a ≤ c * a ↔ b ≤ c :=
rel_iff_cov α α (swap (*)) (≤) a

end has_le

section has_lt
variables [has_lt α]

@[simp, to_additive]
lemma mul_lt_mul_iff_left [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  (a : α) {b c : α} :
  a * b < a * c ↔ b < c :=
rel_iff_cov α α (*) (<) a

@[simp, to_additive]
lemma mul_lt_mul_iff_right
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (<)]
  (a : α) {b c : α} :
  b * a < c * a ↔ b < c :=
rel_iff_cov α α (swap (*)) (<) a

@[to_additive add_lt_add_left]
lemma mul_lt_mul_left' [covariant_class α α (*) (<)] {b c : α} (bc : b < c) (a : α) :
  a * b < a * c :=
covariant_class.elim _ bc

@[to_additive lt_of_add_lt_add_left]
lemma lt_of_mul_lt_mul_left' [contravariant_class α α (*) (<)]
  {a b c : α} (bc : a * b < a * c) :
  b < c :=
contravariant_class.elim _ bc

@[to_additive add_lt_add_right]
lemma mul_lt_mul_right' [covariant_class α α (swap (*)) (<)]
  {b c : α} (bc : b < c) (a : α) :
  b * a < c * a :=
covariant_class.elim a bc

@[to_additive lt_of_add_lt_add_right]
lemma lt_of_mul_lt_mul_right' [contravariant_class α α (swap (*)) (<)]
  {a b c : α} (bc : b * a < c * a) :
  b < c :=
contravariant_class.elim a bc

end has_lt

end has_mul

-- using one
section mul_one_class
variables [mul_one_class α]

section has_le
variables [has_le α]

@[simp, to_additive le_add_iff_nonneg_right]
lemma le_mul_iff_one_le_right'
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b : α} : a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive add_le_iff_nonpos_right]
lemma mul_le_iff_le_one_right'
  [covariant_class α α (*) (≤)] [contravariant_class α α (*) (≤)]
  (a : α) {b : α} :
  a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) (mul_le_mul_iff_left a)

@[simp, to_additive le_add_iff_nonneg_left]
lemma le_mul_iff_one_le_left'
  [covariant_class α α (swap (*)) (≤)] [contravariant_class α α (swap (*)) (≤)]
  (a : α) {b : α} :
  a ≤ b * a ↔ 1 ≤ b :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right a)

@[simp, to_additive add_le_iff_nonpos_left]
lemma mul_le_iff_le_one_left'
  [covariant_class α α (swap (*)) (≤)] [contravariant_class α α (swap (*)) (≤)]
  {a b : α} :
  a * b ≤ b ↔ a ≤ 1 :=
iff.trans (by rw one_mul) (mul_le_mul_iff_right b)

end has_le

lemma exists_square_le {α : Type*} [mul_one_class α] [linear_order α] [covariant_class α α (*) (<)]
  (a : α) : ∃ (b : α), b * b ≤ a :=
begin
  by_cases h : a < 1,
  { use a,
    have : a*a < a*1,
    exact mul_lt_mul_left' h a,
    rw mul_one at this,
    exact le_of_lt this },
  { use 1,
    push_neg at h,
    rwa mul_one }
end

section has_lt
variable [has_lt α]

@[to_additive lt_add_of_pos_right]
lemma lt_mul_of_one_lt_right'
  [covariant_class α α (*) (<)]
  (a : α) {b : α} (h : 1 < b) : a < a * b :=
calc a = a * 1 : (mul_one _).symm
   ... < a * b : mul_lt_mul_left' h a

@[simp, to_additive lt_add_iff_pos_right]
lemma lt_mul_iff_one_lt_right'
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)]
  (a : α) {b : α} :
  a < a * b ↔ 1 < b :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive add_lt_iff_neg_left]
lemma mul_lt_iff_lt_one_left'
  [covariant_class α α (*) (<)] [contravariant_class α α (*) (<)] {a b : α} :
  a * b < a ↔ b < 1 :=
iff.trans (by rw mul_one) (mul_lt_mul_iff_left a)

@[simp, to_additive lt_add_iff_pos_left]
lemma lt_mul_iff_one_lt_left'
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (<)]
  (a : α) {b : α} : a < b * a ↔ 1 < b :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right a)

@[simp, to_additive add_lt_iff_neg_right]
lemma mul_lt_iff_lt_one_right'
  [covariant_class α α (swap (*)) (<)] [contravariant_class α α (swap (*)) (<)]
  {a : α} (b : α) :
  a * b < b ↔ a < 1 :=
iff.trans (by rw one_mul) (mul_lt_mul_iff_right b)

end has_lt

section preorder
variable [preorder α]

@[to_additive]
lemma mul_le_of_le_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b ≤ c) (ha : a ≤ 1) : b * a ≤ c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... ≤ c     : hbc

alias mul_le_of_le_of_le_one ← mul_le_one'
attribute [to_additive add_nonpos] mul_le_one'

@[to_additive]
lemma lt_mul_of_lt_of_one_le [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : 1 ≤ a) : b < c * a :=
calc  b < c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive]
lemma mul_lt_of_lt_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (hbc : b < c) (ha : a ≤ 1)  : b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' ha b
        ... = b     : mul_one b
        ... < c     : hbc

@[to_additive]
lemma lt_mul_of_le_of_one_lt [covariant_class α α (*) (<)]
  {a b c : α} (hbc : b ≤ c) (ha : 1 < a) : b < c * a :=
calc  b ≤ c     : hbc
    ... = c * 1 : (mul_one c).symm
    ... < c * a : mul_lt_mul_left' ha c

@[to_additive]
lemma mul_lt_of_le_one_of_lt [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : a ≤ 1) (hb : b < c) : a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

@[to_additive]
lemma mul_le_of_le_one_of_le [covariant_class α α (swap (*)) (≤)]
  {a b c : α} (ha : a ≤ 1) (hbc : b ≤ c) :
  a * b ≤ c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma le_mul_of_one_le_of_le [covariant_class α α (swap (*)) (≤)]
  {a b c: α} (ha : 1 ≤ a) (hbc : b ≤ c) : b ≤ a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... ≤ a * c : mul_le_mul_right' ha c

/--
Assume monotonicity on the `left`. The lemma assuming `right` is `right.mul_lt_one`. -/
@[to_additive]
lemma left.mul_lt_one [covariant_class α α (*) (<)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
calc  a * b < a * 1 : mul_lt_mul_left' hb a
        ... = a     : mul_one a
        ... < 1     : ha

/--
Assume monotonicity on the `right`. The lemma assuming `left` is `left.mul_lt_one`. -/
@[to_additive]
lemma right.mul_lt_one [covariant_class α α (swap (*)) (<)]
  {a b : α} (ha : a < 1) (hb : b < 1) : a * b < 1 :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < 1     : hb

@[to_additive]
lemma mul_lt_of_le_of_lt_one
  [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  {a b c: α} (hbc : b ≤ c) (ha : a < 1) : b * a < c :=
calc  b * a ≤ c * a : mul_le_mul_right' hbc a
        ... < c * 1 : mul_lt_mul_left' ha c
        ... = c     : mul_one c

@[to_additive]
lemma mul_lt_of_lt_one_of_le [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : a < 1) (hbc : b ≤ c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... ≤ c     : hbc

@[to_additive]
lemma lt_mul_of_one_lt_of_le [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : 1 < a) (hbc : b ≤ c) : b < a * c :=
calc  b ≤ c     : hbc
    ... = 1 * c : (one_mul c).symm
    ... < a * c : mul_lt_mul_right' ha c

/-- Assumes left covariance. -/
@[to_additive]
lemma le_mul_of_le_of_le_one [covariant_class α α (*) (≤)]
  {a b c : α} (ha : c ≤ a) (hb : 1 ≤ b) : c ≤ a * b :=
calc  c ≤ a     : ha
    ... = a * 1 : (mul_one a).symm
    ... ≤ a * b : mul_le_mul_left' hb a

/-  This lemma is present to mimick the name of an existing one. -/
@[to_additive add_nonneg]
lemma one_le_mul [covariant_class α α (*) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
le_mul_of_le_of_le_one ha hb

/-- Assumes left covariance. -/
@[to_additive]
lemma lt_mul_of_lt_of_one_lt [covariant_class α α (*) (<)]
  {a b c : α} (ha : c < a) (hb : 1 < b) : c < a * b :=
calc  c < a     : ha
    ... = a * 1 : (mul_one _).symm
    ... < a * b : mul_lt_mul_left' hb a

/-- Assumes left covariance. -/
@[to_additive]
lemma left.mul_lt_one_of_lt_of_lt_one [covariant_class α α (*) (<)]
  {a b c : α} (ha : a < c) (hb : b < 1) : a * b < c :=
calc  a * b < a * 1 : mul_lt_mul_left' hb a
        ... = a     : mul_one a
        ... < c     : ha

/-- Assumes right covariance. -/
@[to_additive]
lemma right.mul_lt_one_of_lt_of_lt_one [covariant_class α α (swap (*)) (<)]
  {a b c : α} (ha : a < 1) (hb : b < c) : a * b < c :=
calc  a * b < 1 * b : mul_lt_mul_right' ha b
        ... = b     : one_mul b
        ... < c     : hb

/-- Assumes right covariance. -/
@[to_additive right.add_nonneg]
lemma right.one_le_mul [covariant_class α α (swap (*)) (≤)]
  {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
calc  1 ≤ b     : hb
    ... = 1 * b : (one_mul b).symm
    ... ≤ a * b : mul_le_mul_right' ha b

/-- Assumes right covariance. -/
@[to_additive right.add_pos]
lemma right.one_lt_mul [covariant_class α α (swap (*)) (<)]
  {b : α} (hb : 1 < b) {a: α} (ha : 1 < a) : 1 < a * b :=
calc  1 < b     : hb
    ... = 1 * b : (one_mul _).symm
    ... < a * b : mul_lt_mul_right' ha b

end preorder


@[to_additive le_add_of_nonneg_right]
lemma le_mul_of_one_le_right' [has_le α] [covariant_class α α (*) (≤)] {a b : α} (h : 1 ≤ b) :
  a ≤ a * b :=
calc  a = a * 1  : (mul_one _).symm
    ... ≤ a * b  : mul_le_mul_left' h a

@[to_additive add_le_of_nonpos_right]
lemma mul_le_of_le_one_right' [has_le α] [covariant_class α α (*) (≤)] {a b : α} (h : b ≤ 1) :
  a * b ≤ a :=
calc  a * b ≤ a * 1 : mul_le_mul_left' h a
        ... = a     : mul_one a

end mul_one_class

@[to_additive]
lemma mul_left_cancel'' [semigroup α] [partial_order α]
  [contravariant_class α α (*) (≤)] {a b c : α} (h : a * b = a * c) : b = c :=
(le_of_mul_le_mul_left' h.le).antisymm (le_of_mul_le_mul_left' h.ge)

@[to_additive]
lemma mul_right_cancel'' [semigroup α] [partial_order α]
  [contravariant_class α α (swap (*)) (≤)] {a b c : α} (h : a * b = c * b) :
  a = c :=
le_antisymm (le_of_mul_le_mul_right' h.le) (le_of_mul_le_mul_right' h.ge)

/- This is not instance, since we want to have an instance from `left_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `left_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `left_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `left_cancel_add_semigroup`
(i.e. `c + a < c + b → a < b`) is a `left_cancel add_semigroup`."]
def contravariant.to_left_cancel_semigroup [semigroup α] [partial_order α]
  [contravariant_class α α (*) (≤)] :
  left_cancel_semigroup α :=
{ mul_left_cancel := λ a b c, mul_left_cancel''
  ..‹semigroup α› }

/- This is not instance, since we want to have an instance from `right_cancel_semigroup`s
to the appropriate `covariant_class`. -/
/--  A semigroup with a partial order and satisfying `right_cancel_semigroup`
(i.e. `a * c < b * c → a < b`) is a `right_cancel semigroup`. -/
@[to_additive
"An additive semigroup with a partial order and satisfying `right_cancel_add_semigroup`
(`a + c < b + c → a < b`) is a `right_cancel add_semigroup`."]
def contravariant.to_right_cancel_semigroup [semigroup α] [partial_order α]
  [contravariant_class α α (swap (*)) (≤)] :
  right_cancel_semigroup α :=
{ mul_right_cancel := λ a b c, mul_right_cancel''
  ..‹semigroup α› }

variables {a b c d : α}

section left
variables [preorder α]

section has_mul
variables [has_mul α]

@[to_additive]
lemma mul_lt_mul_of_lt_of_lt
  [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
calc  a * c < a * d : mul_lt_mul_left' h₂ a
        ... < b * d : mul_lt_mul_right' h₁ d

section contravariant_mul_lt_left_le_right
variables [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]

@[to_additive]
lemma mul_lt_mul_of_le_of_lt
  (h₁ : a ≤ b) (h₂ : c < d) : a * c < b * d :=
(mul_le_mul_right' h₁ _).trans_lt (mul_lt_mul_left' h₂ b)

@[to_additive add_lt_add]
lemma mul_lt_mul''' (h₁ : a < b) (h₂ : c < d) : a * c < b * d :=
mul_lt_mul_of_le_of_lt h₁.le h₂

end contravariant_mul_lt_left_le_right

@[to_additive] lemma mul_eq_mul_iff_eq_and_eq {α : Type*} [semigroup α] [partial_order α]
  [contravariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  [covariant_class α α (*) (<)] [contravariant_class α α (swap (*)) (≤)]
  {a b c d : α} (hac : a ≤ c) (hbd : b ≤ d) : a * b = c * d ↔ a = c ∧ b = d :=
begin
  refine ⟨λ h, _, λ h, congr_arg2 (*) h.1 h.2⟩,
  rcases hac.eq_or_lt with rfl | hac,
  { exact ⟨rfl, mul_left_cancel'' h⟩ },
  rcases eq_or_lt_of_le hbd with rfl | hbd,
  { exact ⟨mul_right_cancel'' h, rfl⟩ },
  exact ((mul_lt_mul''' hac hbd).ne h).elim,
end

variable [covariant_class α α (*) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_left (h : a * b < c) (hle : d ≤ b) :
  a * d < c :=
(mul_le_mul_left' hle a).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_left (h : a * b ≤ c) (hle : d ≤ b) :
  a * d ≤ c :=
@act_rel_of_rel_of_act_rel _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ a _ _ _ hle h

@[to_additive]
lemma lt_mul_of_lt_mul_left (h : a < b * c) (hle : c ≤ d) :
  a < b * d :=
h.trans_le (mul_le_mul_left' hle b)

@[to_additive]
lemma le_mul_of_le_mul_left (h : a ≤ b * c) (hle : c ≤ d) :
  a ≤ b * d :=
@rel_act_of_rel_of_rel_act _ _ _ (≤) _ ⟨λ _ _ _, le_trans⟩ b _ _ _ hle h

@[to_additive]
lemma mul_lt_mul_of_lt_of_le [covariant_class α α (swap (*)) (<)]
  (h₁ : a < b) (h₂ : c ≤ d) : a * c < b * d :=
(mul_le_mul_left' h₂ _).trans_lt (mul_lt_mul_right' h₁ d)

end has_mul

/-!  Here we start using properties of one, on the left. -/
section mul_one_class
variables [mul_one_class α] [covariant_class α α (*) (≤)]

@[to_additive]
lemma lt_of_mul_lt_of_one_le_left (h : a * b < c) (hle : 1 ≤ b) : a < c :=
(le_mul_of_one_le_right' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_left (h : a * b ≤ c) (hle : 1 ≤ b) : a ≤ c :=
(le_mul_of_one_le_right' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_left (h : a < b * c) (hle : c ≤ 1) : a < b :=
h.trans_le (mul_le_of_le_one_right' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_left (h : a ≤ b * c) (hle : c ≤ 1) : a ≤ b :=
h.trans (mul_le_of_le_one_right' hle)

@[to_additive]
theorem mul_lt_of_lt_of_lt_one (bc : b < c) (a1 : a < 1) :
  b * a < c :=
calc  b * a ≤ b * 1 : mul_le_mul_left' a1.le _
        ... = b     : mul_one b
        ... < c     : bc

end mul_one_class

end left

section right

section preorder
variables [preorder α]

section has_mul
variables [has_mul α]

variable [covariant_class α α (swap (*)) (≤)]

@[to_additive]
lemma mul_lt_of_mul_lt_right (h : a * b < c) (hle : d ≤ a) :
  d * b < c :=
(mul_le_mul_right' hle b).trans_lt h

@[to_additive]
lemma mul_le_of_mul_le_right (h : a * b ≤ c) (hle : d ≤ a) :
  d * b ≤ c :=
(mul_le_mul_right' hle b).trans h

@[to_additive]
lemma lt_mul_of_lt_mul_right (h : a < b * c) (hle : b ≤ d) :
  a < d * c :=
h.trans_le (mul_le_mul_right' hle c)

@[to_additive]
lemma le_mul_of_le_mul_right (h : a ≤ b * c) (hle : b ≤ d) :
  a ≤ d * c :=
h.trans (mul_le_mul_right' hle c)

variable [covariant_class α α (*) (≤)]

@[to_additive add_le_add]
lemma mul_le_mul' (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
(mul_le_mul_left' h₂ _).trans (mul_le_mul_right' h₁ d)

@[to_additive]
lemma mul_le_mul_three {e f : α} (h₁ : a ≤ d) (h₂ : b ≤ e) (h₃ : c ≤ f) :
  a * b * c ≤ d * e * f :=
mul_le_mul' (mul_le_mul' h₁ h₂) h₃

end has_mul

/-!  Here we start using properties of one, on the right. -/
section mul_one_class
variables [mul_one_class α]

section le_right
variable [covariant_class α α (swap (*)) (≤)]

@[to_additive le_add_of_nonneg_left]
lemma le_mul_of_one_le_left' (h : 1 ≤ b) : a ≤ b * a :=
calc  a = 1 * a : (one_mul a).symm
    ... ≤ b * a : mul_le_mul_right' h a

@[to_additive add_le_of_nonpos_left]
lemma mul_le_of_le_one_left' (h : b ≤ 1) : b * a ≤ a :=
calc  b * a ≤ 1 * a : mul_le_mul_right' h a
        ... = a     : one_mul a

@[to_additive]
lemma lt_of_mul_lt_of_one_le_right (h : a * b < c) (hle : 1 ≤ a) : b < c :=
(le_mul_of_one_le_left' hle).trans_lt h

@[to_additive]
lemma le_of_mul_le_of_one_le_right (h : a * b ≤ c) (hle : 1 ≤ a) : b ≤ c :=
(le_mul_of_one_le_left' hle).trans h

@[to_additive]
lemma lt_of_lt_mul_of_le_one_right (h : a < b * c) (hle : b ≤ 1) : a < c :=
h.trans_le (mul_le_of_le_one_left' hle)

@[to_additive]
lemma le_of_le_mul_of_le_one_right (h : a ≤ b * c) (hle : b ≤ 1) : a ≤ c :=
h.trans (mul_le_of_le_one_left' hle)

theorem mul_lt_of_lt_one_of_lt (a1 : a < 1) (bc : b < c) :
  a * b < c :=
calc  a * b ≤ 1 * b : mul_le_mul_right' a1.le _
        ... = b : one_mul b
        ... < c : bc

end le_right

section lt_right

@[to_additive lt_add_of_pos_left]
lemma lt_mul_of_one_lt_left' [covariant_class α α (swap (*)) (<)]
  (a : α) {b : α} (h : 1 < b) : a < b * a :=
calc a = 1 * a : (one_mul _).symm
   ... < b * a : mul_lt_mul_right' h a

end lt_right

end mul_one_class

end preorder

end right

section preorder
variables [preorder α]

section mul_one_class
variables [mul_one_class α]

section covariant_left
variable [covariant_class α α (*) (≤)]

@[to_additive add_pos_of_pos_of_nonneg]
lemma one_lt_mul_of_lt_of_le' (ha : 1 < a) (hb : 1 ≤ b) : 1 < a * b :=
lt_of_lt_of_le ha $ le_mul_of_one_le_right' hb

@[to_additive add_pos]
lemma one_lt_mul' (ha : 1 < a) (hb : 1 < b) : 1 < a * b :=
one_lt_mul_of_lt_of_le' ha hb.le

@[to_additive]
lemma lt_mul_of_lt_of_one_le' (hbc : b < c) (ha : 1 ≤ a) :
  b < c * a :=
hbc.trans_le $ le_mul_of_one_le_right' ha

@[to_additive]
lemma lt_mul_of_lt_of_one_lt' (hbc : b < c) (ha : 1 < a) :
  b < c * a :=
lt_mul_of_lt_of_one_le' hbc ha.le

@[to_additive]
lemma le_mul_of_le_of_one_le (hbc : b ≤ c) (ha : 1 ≤ a) : b ≤ c * a :=
calc  b ≤ c : hbc
    ... = c * 1 : (mul_one c).symm
    ... ≤ c * a : mul_le_mul_left' ha c

@[to_additive add_nonneg]
lemma one_le_mul_right (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
calc  1 ≤ a     : ha
    ... = a * 1 : (mul_one a).symm
    ... ≤ a * b : mul_le_mul_left' hb a

end covariant_left

section covariant_right
variable [covariant_class α α (swap (*)) (≤)]

@[to_additive add_pos_of_nonneg_of_pos]
lemma one_lt_mul_of_le_of_lt' (ha : 1 ≤ a) (hb : 1 < b) : 1 < a * b :=
lt_of_lt_of_le hb $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_le_of_lt (ha : 1 ≤ a) (hbc : b < c) : b < a * c :=
hbc.trans_le $ le_mul_of_one_le_left' ha

@[to_additive]
lemma lt_mul_of_one_lt_of_lt (ha : 1 < a) (hbc : b < c) : b < a * c :=
lt_mul_of_one_le_of_lt ha.le hbc

end covariant_right

end mul_one_class

end preorder

section partial_order

/-!  Properties assuming `partial_order`. -/
variables [mul_one_class α] [partial_order α]
  [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]

@[to_additive]
lemma mul_eq_one_iff' (ha : 1 ≤ a) (hb : 1 ≤ b) : a * b = 1 ↔ a = 1 ∧ b = 1 :=
iff.intro
  (assume hab : a * b = 1,
   have a ≤ 1, from hab ▸ le_mul_of_le_of_one_le le_rfl hb,
   have a = 1, from le_antisymm this ha,
   have b ≤ 1, from hab ▸ le_mul_of_one_le_of_le ha le_rfl,
   have b = 1, from le_antisymm this hb,
   and.intro ‹a = 1› ‹b = 1›)
  (assume ⟨ha', hb'⟩, by rw [ha', hb', mul_one])

end partial_order

section mono
variables [has_mul α] [preorder α] [preorder β] {f g : β → α}

@[to_additive monotone.const_add]
lemma monotone.const_mul' [covariant_class α α (*) (≤)] (hf : monotone f) (a : α) :
  monotone (λ x, a * f x) :=
λ x y h, mul_le_mul_left' (hf h) a

@[to_additive monotone.add_const]
lemma monotone.mul_const' [covariant_class α α (swap (*)) (≤)]
  (hf : monotone f) (a : α) : monotone (λ x, f x * a) :=
λ x y h, mul_le_mul_right' (hf h) a

/--  The product of two monotone functions is monotone. -/
@[to_additive monotone.add "The sum of two monotone functions is monotone."]
lemma monotone.mul' [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]
  (hf : monotone f) (hg : monotone g) : monotone (λ x, f x * g x) :=
λ x y h, mul_le_mul' (hf h) (hg h)

section left
variables [covariant_class α α (*) (<)]

@[to_additive strict_mono.const_add]
lemma strict_mono.const_mul' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, c * f x) :=
λ a b ab, mul_lt_mul_left' (hf ab) c

end left

section right
variables [covariant_class α α (swap (*)) (<)]

@[to_additive strict_mono.add_const]
lemma strict_mono.mul_const' (hf : strict_mono f) (c : α) :
  strict_mono (λ x, f x * c) :=
λ a b ab, mul_lt_mul_right' (hf ab) c

end right

/--  The product of two strictly monotone functions is strictly monotone. -/
@[to_additive strict_mono.add
"The sum of two strictly monotone functions is strictly monotone."]
lemma strict_mono.mul' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (<)]
  (hf : strict_mono f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ a b ab, mul_lt_mul_of_lt_of_lt (hf ab) (hg ab)

/--  The product of a monotone function and a strictly monotone function is strictly monotone. -/
@[to_additive monotone.add_strict_mono
"The sum of a monotone function and a strictly monotone function is strictly monotone."]
lemma monotone.mul_strict_mono' [covariant_class α α (*) (<)] [covariant_class α α (swap (*)) (≤)]
  {f g : β → α} (hf : monotone f) (hg : strict_mono g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_le_of_lt (hf h.le) (hg h)

variables [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (<)]

/--  The product of a strictly monotone function and a monotone function is strictly monotone. -/
@[to_additive strict_mono.add_monotone
"The sum of a strictly monotone function and a monotone function is strictly monotone."]
lemma strict_mono.mul_monotone' (hf : strict_mono f) (hg : monotone g) :
  strict_mono (λ x, f x * g x) :=
λ x y h, mul_lt_mul_of_lt_of_le (hf h) (hg h.le)

end mono

/--
An element `a : α` is `mul_le_cancellable` if `x ↦ a * x` is order-reflecting.
We will make a separate version of many lemmas that require `[contravariant_class α α (*) (≤)]` with
`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`.
-/
@[to_additive /-" An element `a : α` is `add_le_cancellable` if `x ↦ a + x` is order-reflecting.
We will make a separate version of many lemmas that require `[contravariant_class α α (+) (≤)]` with
`mul_le_cancellable` assumptions instead. These lemmas can then be instantiated to specific types,
like `ennreal`, where we can replace the assumption `add_le_cancellable x` by `x ≠ ∞`. "-/
]
def mul_le_cancellable [has_mul α] [has_le α] (a : α) : Prop :=
∀ ⦃b c⦄, a * b ≤ a * c → b ≤ c

@[to_additive]
lemma contravariant.mul_le_cancellable [has_mul α] [has_le α] [contravariant_class α α (*) (≤)]
  {a : α} : mul_le_cancellable a :=
λ b c, le_of_mul_le_mul_left'

namespace mul_le_cancellable

@[to_additive]
protected lemma injective [has_mul α] [partial_order α] {a : α} (ha : mul_le_cancellable a) :
  injective ((*) a) :=
λ b c h, le_antisymm (ha h.le) (ha h.ge)

@[to_additive]
protected lemma inj [has_mul α] [partial_order α] {a b c : α} (ha : mul_le_cancellable a) :
  a * b = a * c ↔ b = c :=
ha.injective.eq_iff

@[to_additive]
protected lemma injective_left [comm_semigroup α] [partial_order α] {a : α}
  (ha : mul_le_cancellable a) : injective (* a) :=
λ b c h, ha.injective $ by rwa [mul_comm a, mul_comm a]

@[to_additive]
protected lemma inj_left [comm_semigroup α] [partial_order α] {a b c : α}
  (hc : mul_le_cancellable c) : a * c = b * c ↔ a = b :=
hc.injective_left.eq_iff

variable [has_le α]

@[to_additive]
protected lemma mul_le_mul_iff_left [has_mul α] [covariant_class α α (*) (≤)]
  {a b c : α} (ha : mul_le_cancellable a) : a * b ≤ a * c ↔ b ≤ c :=
⟨λ h, ha h, λ h, mul_le_mul_left' h a⟩

@[to_additive]
protected lemma mul_le_mul_iff_right [comm_semigroup α] [covariant_class α α (*) (≤)]
  {a b c : α} (ha : mul_le_cancellable a) : b * a ≤ c * a ↔ b ≤ c :=
by rw [mul_comm b, mul_comm c, ha.mul_le_mul_iff_left]

@[to_additive]
protected lemma le_mul_iff_one_le_right [mul_one_class α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : a ≤ a * b ↔ 1 ≤ b :=
iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
protected lemma mul_le_iff_le_one_right [mul_one_class α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : a * b ≤ a ↔ b ≤ 1 :=
iff.trans (by rw [mul_one]) ha.mul_le_mul_iff_left

@[to_additive]
protected lemma le_mul_iff_one_le_left [comm_monoid α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : a ≤ b * a ↔ 1 ≤ b :=
by rw [mul_comm, ha.le_mul_iff_one_le_right]

@[to_additive]
protected lemma mul_le_iff_le_one_left [comm_monoid α] [covariant_class α α (*) (≤)]
  {a b : α} (ha : mul_le_cancellable a) : b * a ≤ a ↔ b ≤ 1 :=
by rw [mul_comm, ha.mul_le_iff_le_one_right]

end mul_le_cancellable
