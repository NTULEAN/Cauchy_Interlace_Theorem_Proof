/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import logic.nontrivial
import algebra.group.units_hom
import algebra.group.inj_surj
import algebra.group_with_zero.defs

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `group_with_zero` and `comm_group_with_zero`.
To reduce import dependencies, the type-classes themselves are in
`algebra.group_with_zero.defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/

set_option old_structure_cmd true
open_locale classical
open function

variables {M₀ G₀ M₀' G₀' : Type*}

mk_simp_attribute field_simps "The simpset `field_simps` is used by the tactic `field_simp` to
reduce an expression in a field to an expression of the form `n / d` where `n` and `d` are
division-free."

attribute [field_simps] mul_div_assoc'

section

section mul_zero_class

variables [mul_zero_class M₀] {a b : M₀}


/-- Pullback a `mul_zero_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.mul_zero_class [has_mul M₀'] [has_zero M₀'] (f : M₀' → M₀)
  (hf : injective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_class M₀' :=
{ mul := (*),
  zero := 0,
  zero_mul := λ a, hf $ by simp only [mul, zero, zero_mul],
  mul_zero := λ a, hf $ by simp only [mul, zero, mul_zero] }

/-- Pushforward a `mul_zero_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.mul_zero_class [has_mul M₀'] [has_zero M₀'] (f : M₀ → M₀')
  (hf : surjective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_class M₀' :=
{ mul := (*),
  zero := 0,
  mul_zero := hf.forall.2 $ λ x, by simp only [← zero, ← mul, mul_zero],
  zero_mul := hf.forall.2 $ λ x, by simp only [← zero, ← mul, zero_mul] }

lemma mul_eq_zero_of_left (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

lemma mul_eq_zero_of_right (a : M₀) (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

lemma left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 := mt (λ h, mul_eq_zero_of_left h b)

lemma right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 := mt (mul_eq_zero_of_right a)

lemma ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

lemma mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) :
  a * b = 0 :=
if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

/-- To match `one_mul_eq_id`. -/
lemma zero_mul_eq_const : ((*) (0 : M₀)) = function.const _ 0 := funext zero_mul

/-- To match `mul_one_eq_id`. -/
lemma mul_zero_eq_const : (* (0 : M₀)) = function.const _ 0 := funext mul_zero

end mul_zero_class

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected lemma function.injective.no_zero_divisors [has_mul M₀] [has_zero M₀]
  [has_mul M₀'] [has_zero M₀'] [no_zero_divisors M₀']
  (f : M₀ → M₀') (hf : injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  no_zero_divisors M₀ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y H,
  have f x * f y = 0, by rw [← mul, H, zero],
  (eq_zero_or_eq_zero_of_mul_eq_zero this).imp (λ H, hf $ by rwa zero)  (λ H, hf $ by rwa zero) }

lemma eq_zero_of_mul_self_eq_zero [has_mul M₀] [has_zero M₀] [no_zero_divisors M₀]
  {a : M₀} (h : a * a = 0) :
  a = 0 :=
(eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

section

variables [mul_zero_class M₀] [no_zero_divisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
⟨eq_zero_or_eq_zero_of_mul_eq_zero,
  λo, o.elim (λ h, mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp] theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 :=
by rw [eq_comm, mul_eq_zero]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
(not_congr mul_eq_zero).trans not_or_distrib

@[field_simps] theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
mul_ne_zero_iff.2 ⟨ha, hb⟩

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
mul_eq_zero.trans $ (or_comm _ _).trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
not_congr mul_eq_zero_comm

lemma mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
lemma zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp

end

end

section

variables [mul_zero_one_class M₀]

/-- Pullback a `mul_zero_one_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.mul_zero_one_class [has_mul M₀'] [has_zero M₀'] [has_one M₀']
  (f : M₀' → M₀)
  (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_one_class M₀' :=
{ ..hf.mul_zero_class f zero mul, ..hf.mul_one_class f one mul }

/-- Pushforward a `mul_zero_one_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.mul_zero_one_class [has_mul M₀'] [has_zero M₀'] [has_one M₀']
  (f : M₀ → M₀')
  (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
  mul_zero_one_class M₀' :=
{ ..hf.mul_zero_class f zero mul, ..hf.mul_one_class f one mul }

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
lemma eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 :=
by rw [← mul_one a, ← h, mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def unique_of_zero_eq_one (h : (0 : M₀) = 1) : unique M₀ :=
{ default := 0, uniq := eq_zero_of_zero_eq_one h }

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ subsingleton M₀ :=
⟨λ h, @unique.subsingleton _ (unique_of_zero_eq_one h), λ h, @subsingleton.elim _ h _ _⟩

alias subsingleton_iff_zero_eq_one ↔ subsingleton_of_zero_eq_one _

lemma eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
@subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
lemma zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ (∀a:M₀, a = 0) :=
not_or_of_imp eq_zero_of_zero_eq_one
end

section

variables [mul_zero_one_class M₀] [nontrivial M₀] {a b : M₀}

/-- In a nontrivial monoid with zero, zero and one are different. -/
@[simp] lemma zero_ne_one : 0 ≠ (1:M₀) :=
begin
  assume h,
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩,
  apply hx,
  calc x = 1 * x : by rw [one_mul]
  ... = 0 : by rw [← h, zero_mul]
  ... = 1 * y : by rw [← h, zero_mul]
  ... = y : by rw [one_mul]
end

@[simp] lemma one_ne_zero : (1:M₀) ≠ 0 :=
zero_ne_one.symm

lemma ne_zero_of_eq_one {a : M₀} (h : a = 1) : a ≠ 0 :=
calc a = 1 : h
   ... ≠ 0 : one_ne_zero

lemma left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
left_ne_zero_of_mul $ ne_zero_of_eq_one h

lemma right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
right_ne_zero_of_mul $ ne_zero_of_eq_one h

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
protected lemma pullback_nonzero [has_zero M₀'] [has_one M₀']
  (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) : nontrivial M₀' :=
⟨⟨0, 1, mt (congr_arg f) $ by { rw [zero, one], exact zero_ne_one }⟩⟩

end

section semigroup_with_zero

/-- Pullback a `semigroup_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.semigroup_with_zero
  [has_zero M₀'] [has_mul M₀'] [semigroup_with_zero M₀] (f : M₀' → M₀) (hf : injective f)
  (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup_with_zero M₀' :=
{ .. hf.mul_zero_class f zero mul,
  .. ‹has_zero M₀'›,
  .. hf.semigroup f mul }

/-- Pushforward a `semigroup_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.semigroup_with_zero
  [semigroup_with_zero M₀] [has_zero M₀'] [has_mul M₀'] (f : M₀ → M₀') (hf : surjective f)
  (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
  semigroup_with_zero M₀' :=
{ .. hf.mul_zero_class f zero mul,
  .. ‹has_zero M₀'›,
  .. hf.semigroup f mul }

end semigroup_with_zero

section monoid_with_zero

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [monoid_with_zero M₀]
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  monoid_with_zero M₀' :=
{ .. hf.monoid f one mul, .. hf.mul_zero_class f zero mul }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [monoid_with_zero M₀]
  (f : M₀ → M₀') (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  monoid_with_zero M₀' :=
{ .. hf.monoid f one mul, .. hf.mul_zero_class f zero mul }

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [comm_monoid_with_zero M₀]
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_monoid_with_zero M₀' :=
{ .. hf.comm_monoid f one mul, .. hf.mul_zero_class f zero mul }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.comm_monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  [comm_monoid_with_zero M₀]
  (f : M₀ → M₀') (hf : surjective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  comm_monoid_with_zero M₀' :=
{ .. hf.comm_monoid f one mul, .. hf.mul_zero_class f zero mul }

variables [monoid_with_zero M₀]

namespace units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp] lemma ne_zero [nontrivial M₀] (u : M₀ˣ) :
  (u : M₀) ≠ 0 :=
left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume
-- `nonzero M₀`.

@[simp] lemma mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
⟨λ h, by simpa using mul_eq_zero_of_left h ↑u⁻¹, λ h, mul_eq_zero_of_left h u⟩

@[simp] lemma mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
⟨λ h, by simpa using mul_eq_zero_of_right ↑u⁻¹ h, mul_eq_zero_of_right u⟩

end units

namespace is_unit

lemma ne_zero [nontrivial M₀] {a : M₀} (ha : is_unit a) : a ≠ 0 := let ⟨u, hu⟩ :=
ha in hu ▸ u.ne_zero

lemma mul_right_eq_zero {a b : M₀} (ha : is_unit a) : a * b = 0 ↔ b = 0 :=
let ⟨u, hu⟩ := ha in hu ▸ u.mul_right_eq_zero

lemma mul_left_eq_zero {a b : M₀} (hb : is_unit b) : a * b = 0 ↔ a = 0 :=
let ⟨u, hu⟩ := hb in hu ▸ u.mul_left_eq_zero

end is_unit

@[simp] theorem is_unit_zero_iff : is_unit (0 : M₀) ↔ (0:M₀) = 1 :=
⟨λ ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩, by rwa zero_mul at a0,
 λ h, @is_unit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

@[simp] theorem not_is_unit_zero [nontrivial M₀] : ¬ is_unit (0 : M₀) :=
mt is_unit_zero_iff.1 zero_ne_one

namespace ring
open_locale classical

/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `ring` namespace for brevity, it requires the weaker assumption
`monoid_with_zero M₀` instead of `ring M₀`. -/
noncomputable def inverse : M₀ → M₀ :=
λ x, if h : is_unit x then ((h.unit⁻¹ : M₀ˣ) : M₀) else 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp] lemma inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) :=
begin
  simp only [units.is_unit, inverse, dif_pos],
  exact units.inv_unique rfl
end

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp] lemma inverse_non_unit (x : M₀) (h : ¬(is_unit x)) : inverse x = 0 := dif_neg h

lemma mul_inverse_cancel (x : M₀) (h : is_unit x) : x * inverse x = 1 :=
by { rcases h with ⟨u, rfl⟩, rw [inverse_unit, units.mul_inv], }

lemma inverse_mul_cancel (x : M₀) (h : is_unit x) : inverse x * x = 1 :=
by { rcases h with ⟨u, rfl⟩, rw [inverse_unit, units.inv_mul], }

lemma mul_inverse_cancel_right (x y : M₀) (h : is_unit x) : y * x * inverse x = y :=
by rw [mul_assoc, mul_inverse_cancel x h, mul_one]

lemma inverse_mul_cancel_right (x y : M₀) (h : is_unit x) : y * inverse x * x = y :=
by rw [mul_assoc, inverse_mul_cancel x h, mul_one]

lemma mul_inverse_cancel_left (x y : M₀) (h : is_unit x) : x * (inverse x * y) = y :=
by rw [← mul_assoc, mul_inverse_cancel x h, one_mul]

lemma inverse_mul_cancel_left (x y : M₀) (h : is_unit x) : inverse x * (x * y) = y :=
by rw [← mul_assoc, inverse_mul_cancel x h, one_mul]

variables (M₀)

@[simp] lemma inverse_one : inverse (1 : M₀) = 1 :=
inverse_unit 1

@[simp] lemma inverse_zero : inverse (0 : M₀) = 0 :=
by { nontriviality, exact inverse_non_unit _ not_is_unit_zero }

variables {M₀}

lemma mul_inverse_rev' {a b : M₀} (h : commute a b) : inverse (a * b) = inverse b * inverse a :=
begin
  by_cases hab : is_unit (a * b),
  { obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab,
    rw [←units.coe_mul, inverse_unit, inverse_unit, inverse_unit, ←units.coe_mul,
      mul_inv_rev], },
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab),
  { rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]},
  { rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]},
end

lemma mul_inverse_rev {M₀} [comm_monoid_with_zero M₀] (a b : M₀) :
  ring.inverse (a * b) = inverse b * inverse a :=
mul_inverse_rev' (commute.all _ _)

end ring

lemma is_unit.ring_inverse {a : M₀} : is_unit a → is_unit (ring.inverse a)
| ⟨u, hu⟩ := hu ▸ ⟨u⁻¹, (ring.inverse_unit u).symm⟩

@[simp] lemma is_unit_ring_inverse {a : M₀} : is_unit (ring.inverse a) ↔ is_unit a :=
⟨λ h, begin
  casesI subsingleton_or_nontrivial M₀,
  { convert h },
  { contrapose h,
    rw ring.inverse_non_unit _ h,
    exact not_is_unit_zero, },
end, is_unit.ring_inverse⟩

lemma commute.ring_inverse_ring_inverse {a b : M₀} (h : commute a b) :
  commute (ring.inverse a) (ring.inverse b) :=
(ring.mul_inverse_rev' h.symm).symm.trans $ (congr_arg _ h.symm.eq).trans $ ring.mul_inverse_rev' h

variable (M₀)

end monoid_with_zero

section cancel_monoid_with_zero

variables [cancel_monoid_with_zero M₀] {a b c : M₀}

@[priority 10] -- see Note [lower instance priority]
instance cancel_monoid_with_zero.to_no_zero_divisors : no_zero_divisors M₀ :=
⟨λ a b ab0, by { by_cases a = 0, { left, exact h }, right,
  apply cancel_monoid_with_zero.mul_left_cancel_of_ne_zero h, rw [ab0, mul_zero], }⟩

lemma mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b := ⟨mul_right_cancel₀ hc, λ h, h ▸ rfl⟩

lemma mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c := ⟨mul_left_cancel₀ ha, λ h, h ▸ rfl⟩

@[simp] lemma mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 :=
by by_cases hc : c = 0; [simp [hc], simp [mul_left_inj', hc]]

@[simp] lemma mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 :=
by by_cases ha : a = 0; [simp [ha], simp [mul_right_inj', ha]]

lemma mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
calc a * b = a ↔ a * b = a * 1 : by rw mul_one
     ...       ↔ b = 1 ∨ a = 0 : mul_eq_mul_left_iff

lemma mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
calc a * b = b ↔ a * b = 1 * b : by rw one_mul
     ...       ↔ a = 1 ∨ b = 0 : mul_eq_mul_right_iff

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.cancel_monoid_with_zero [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  cancel_monoid_with_zero M₀' :=
{ mul_left_cancel_of_ne_zero := λ x y z hx H, hf $ mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) $
    by erw [← mul, ← mul, H]; refl,
  mul_right_cancel_of_ne_zero := λ x y z hx H, hf $ mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) $
    by erw [← mul, ← mul, H]; refl,
  .. hf.monoid f one mul, .. hf.mul_zero_class f zero mul }

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_left_cancel₀ ha $ h₂.symm ▸ (mul_one a).symm

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
classical.by_contradiction $ λ ha, h₁ $ mul_right_cancel₀ ha $ h₂.symm ▸ (one_mul a).symm

end cancel_monoid_with_zero

section cancel_comm_monoid_with_zero

variables [cancel_comm_monoid_with_zero M₀] {a b c : M₀}

/-- Pullback a `cancel_comm_monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.cancel_comm_monoid_with_zero
  [has_zero M₀'] [has_mul M₀'] [has_one M₀']
  (f : M₀' → M₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  cancel_comm_monoid_with_zero M₀' :=
{ .. hf.comm_monoid_with_zero f zero one mul,
  .. hf.cancel_monoid_with_zero f zero one mul }

end cancel_comm_monoid_with_zero

section group_with_zero
variables [group_with_zero G₀] {a b c g h x : G₀}

alias div_eq_mul_inv ← division_def

/-- Pullback a `group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.group_with_zero [has_zero G₀'] [has_mul G₀'] [has_one G₀']
  [has_inv G₀'] [has_div G₀'] (f : G₀' → G₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  group_with_zero G₀' :=
{ inv_zero := hf $ by erw [inv, zero, inv_zero],
  mul_inv_cancel := λ x hx, hf $ by erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)],
  .. hf.monoid_with_zero f zero one mul,
  .. hf.div_inv_monoid f one mul inv div,
  .. pullback_nonzero f zero one, }

/-- Pushforward a `group_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.group_with_zero [has_zero G₀'] [has_mul G₀'] [has_one G₀']
  [has_inv G₀'] [has_div G₀'] (h01 : (0:G₀') ≠ 1) (f : G₀ → G₀') (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
  (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) :
  group_with_zero G₀' :=
{ inv_zero := by erw [← zero, ← inv, inv_zero],
  mul_inv_cancel := hf.forall.2 $ λ x hx,
    by erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) $ trans_rel_left ne hx zero.symm)];
      exact one,
  exists_pair_ne := ⟨0, 1, h01⟩,
  .. hf.monoid_with_zero f zero one mul,
  .. hf.div_inv_monoid f one mul inv div }

@[simp] lemma mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) :
  (a * b) * b⁻¹ = a :=
calc (a * b) * b⁻¹ = a * (b * b⁻¹) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) :
  a * (a⁻¹ * b) = b :=
calc a * (a⁻¹ * b) = (a * a⁻¹) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

lemma inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 :=
assume a_eq_0, by simpa [a_eq_0] using mul_inv_cancel h

@[simp] lemma inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
calc a⁻¹ * a = (a⁻¹ * a) * a⁻¹ * a⁻¹⁻¹ : by simp [inv_ne_zero h]
         ... = a⁻¹ * a⁻¹⁻¹             : by simp [h]
         ... = 1                       : by simp [inv_ne_zero h]

lemma group_with_zero.mul_left_injective (h : x ≠ 0) :
  function.injective (λ y, x * y) :=
λ y y' w, by simpa only [←mul_assoc, inv_mul_cancel h, one_mul] using congr_arg (λ y, x⁻¹ * y) w

lemma group_with_zero.mul_right_injective (h : x ≠ 0) :
  function.injective (λ y, y * x) :=
λ y y' w, by simpa only [mul_assoc, mul_inv_cancel h, mul_one] using congr_arg (λ y, y * x⁻¹) w

@[simp] lemma inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) :
  (a * b⁻¹) * b = a :=
calc (a * b⁻¹) * b = a * (b⁻¹ * b) : mul_assoc _ _ _
               ... = a             : by simp [h]

@[simp] lemma inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) :
  a⁻¹ * (a * b) = b :=
calc a⁻¹ * (a * b) = (a⁻¹ * a) * b : (mul_assoc _ _ _).symm
               ... = b             : by simp [h]

@[simp] lemma inv_one : 1⁻¹ = (1:G₀) :=
calc 1⁻¹ = 1 * 1⁻¹ : by rw [one_mul]
     ... = (1:G₀)  : by simp

@[simp] lemma inv_inv₀ (a : G₀) : a⁻¹⁻¹ = a :=
begin
  by_cases h : a = 0, { simp [h] },
  calc a⁻¹⁻¹ = a * (a⁻¹ * a⁻¹⁻¹) : by simp [h]
         ... = a                 : by simp [inv_ne_zero h]
end

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp] lemma mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_assoc, mul_inv_cancel h, mul_one] }
end

/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp] lemma mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [mul_inv_cancel h, one_mul] }
end

/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp] lemma inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a :=
begin
  by_cases h : a = 0,
  { rw [h, inv_zero, mul_zero] },
  { rw [inv_mul_cancel h, one_mul] }
end

/-- Multiplying `a` by itself and then dividing by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma mul_self_div_self (a : G₀) : a * a / a = a :=
by rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma div_self_mul_self (a : G₀) : a / a * a = a :=
by rw [div_eq_mul_inv, mul_inv_mul_self a]

lemma inv_involutive₀ : function.involutive (has_inv.inv : G₀ → G₀) :=
inv_inv₀

lemma eq_inv_of_mul_right_eq_one (h : a * b = 1) :
  b = a⁻¹ :=
by rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

lemma eq_inv_of_mul_left_eq_one (h : a * b = 1) :
  a = b⁻¹ :=
by rw [← mul_inv_cancel_right₀ (right_ne_zero_of_mul_eq_one h) a, h, one_mul]

lemma inv_injective₀ : function.injective (@has_inv.inv G₀ _) :=
inv_involutive₀.injective

@[simp] lemma inv_inj₀ : g⁻¹ = h⁻¹ ↔ g = h := inv_injective₀.eq_iff

/-- This is the analogue of `inv_eq_iff_inv_eq` for `group_with_zero`.
  It could also be named `inv_eq_iff_inv_eq'`. -/
lemma inv_eq_iff : g⁻¹ = h ↔ h⁻¹ = g :=
by rw [← inv_inj₀, eq_comm, inv_inv₀]

/-- This is the analogue of `eq_inv_iff_eq_inv` for `group_with_zero`.
  It could also be named `eq_inv_iff_eq_inv'`. -/
lemma eq_inv_iff : a = b⁻¹ ↔ b = a⁻¹ :=
by rw [eq_comm, inv_eq_iff, eq_comm]

@[simp] lemma inv_eq_one₀ : g⁻¹ = 1 ↔ g = 1 :=
by rw [inv_eq_iff, inv_one, eq_comm]

lemma eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
by split; rintro rfl; [rw inv_mul_cancel_right₀ hc, rw mul_inv_cancel_right₀ hc]

lemma eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
by split; rintro rfl; [rw mul_inv_cancel_left₀ hb, rw inv_mul_cancel_left₀ hb]

lemma inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
by rw [eq_comm, eq_inv_mul_iff_mul_eq₀ ha, eq_comm]

lemma mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
by rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hb, eq_comm]

lemma mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b :=
by rw [mul_inv_eq_iff_eq_mul₀ hb, one_mul]

lemma inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b :=
by rw [inv_mul_eq_iff_eq_mul₀ ha, mul_one, eq_comm]

lemma mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ :=
by { convert mul_inv_eq_one₀ (inv_ne_zero hb), rw [inv_inv₀] }

lemma mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b :=
by { convert inv_mul_eq_one₀ (inv_ne_zero ha), rw [inv_inv₀] }

end group_with_zero

namespace units
variables [group_with_zero G₀]
variables {a b : G₀}

/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp] lemma mk0_one (h := one_ne_zero) :
  mk0 (1 : G₀) h = 1 :=
by { ext, refl }

@[simp] lemma coe_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a := rfl

@[simp] lemma mk0_coe (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
units.ext rfl

@[simp, norm_cast] lemma coe_inv' (u : G₀ˣ) : ((u⁻¹ : G₀ˣ) : G₀) = u⁻¹ :=
eq_inv_of_mul_left_eq_one u.inv_mul

@[simp] lemma mul_inv' (u : G₀ˣ) : (u : G₀) * u⁻¹ = 1 := mul_inv_cancel u.ne_zero

@[simp] lemma inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 := inv_mul_cancel u.ne_zero

@[simp] lemma mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) :
  units.mk0 a ha = units.mk0 b hb ↔ a = b :=
⟨λ h, by injection h, λ h, units.ext h⟩

@[simp] lemma exists_iff_ne_zero {x : G₀} : (∃ u : G₀ˣ, ↑u = x) ↔ x ≠ 0 :=
⟨λ ⟨u, hu⟩, hu ▸ u.ne_zero, assume hx, ⟨mk0 x hx, rfl⟩⟩

lemma _root_.group_with_zero.eq_zero_or_unit (a : G₀) :
  a = 0 ∨ ∃ u : G₀ˣ, a = u :=
begin
  by_cases h : a = 0,
  { left,
    exact h },
  { right,
    simpa only [eq_comm] using units.exists_iff_ne_zero.mpr h }
end

end units

section group_with_zero
variables [group_with_zero G₀]

lemma is_unit.mk0 (x : G₀) (hx : x ≠ 0) : is_unit x := (units.mk0 x hx).is_unit

lemma is_unit_iff_ne_zero {x : G₀} : is_unit x ↔ x ≠ 0 :=
units.exists_iff_ne_zero

@[priority 10] -- see Note [lower instance priority]
instance group_with_zero.no_zero_divisors : no_zero_divisors G₀ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h,
    begin
      contrapose! h,
      exact ((units.mk0 a h.1) * (units.mk0 b h.2)).ne_zero
    end,
  .. (‹_› : group_with_zero G₀) }

@[priority 10] -- see Note [lower instance priority]
instance group_with_zero.cancel_monoid_with_zero : cancel_monoid_with_zero G₀ :=
{ mul_left_cancel_of_ne_zero := λ x y z hx h,
    by rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
  mul_right_cancel_of_ne_zero := λ x y z hy h,
    by rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z],
  .. (‹_› : group_with_zero G₀) }

-- Can't be put next to the other `mk0` lemmas becuase it depends on the
-- `no_zero_divisors` instance, which depends on `mk0`.
@[simp] lemma units.mk0_mul (x y : G₀) (hxy) :
  units.mk0 (x * y) hxy =
    units.mk0 x (mul_ne_zero_iff.mp hxy).1 * units.mk0 y (mul_ne_zero_iff.mp hxy).2 :=
by { ext, refl }

lemma mul_inv_rev₀ (x y : G₀) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  by_cases hx : x = 0, { simp [hx] },
  by_cases hy : y = 0, { simp [hy] },
  symmetry,
  apply eq_inv_of_mul_left_eq_one,
  simp [mul_assoc, hx, hy]
end

@[simp] lemma div_self {a : G₀} (h : a ≠ 0) : a / a = 1 :=
by rw [div_eq_mul_inv, mul_inv_cancel h]

@[simp] lemma div_one (a : G₀) : a / 1 = a :=
by simp [div_eq_mul_inv a 1]

@[simp] lemma zero_div (a : G₀) : 0 / a = 0 :=
by rw [div_eq_mul_inv, zero_mul]

@[simp] lemma div_zero (a : G₀) : a / 0 = 0 :=
by rw [div_eq_mul_inv, inv_zero, mul_zero]

@[simp] lemma div_mul_cancel (a : G₀) {b : G₀} (h : b ≠ 0) : a / b * b = a :=
by rw [div_eq_mul_inv, inv_mul_cancel_right₀ h a]

lemma div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (div_mul_cancel a)

@[simp] lemma mul_div_cancel (a : G₀) {b : G₀} (h : b ≠ 0) : a * b / b = a :=
by rw [div_eq_mul_inv, mul_inv_cancel_right₀ h a]

lemma mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
classical.by_cases (λ hb : b = 0, by simp [*]) (mul_div_cancel a)

local attribute [simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp] lemma div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
calc a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ : by simp [mul_inv_rev₀]
... = a⁻¹ : inv_mul_mul_self _

lemma div_eq_mul_one_div (a b : G₀) : a / b = a * (1 / b) :=
by simp

lemma mul_one_div_cancel {a : G₀} (h : a ≠ 0) : a * (1 / a) = 1 :=
by simp [h]

lemma one_div_mul_cancel {a : G₀} (h : a ≠ 0) : (1 / a) * a = 1 :=
by simp [h]

lemma one_div_one : 1 / 1 = (1:G₀) :=
div_self (ne.symm zero_ne_one)

lemma one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 :=
by simpa only [one_div] using inv_ne_zero h

lemma eq_one_div_of_mul_eq_one {a b : G₀} (h : a * b = 1) : b = 1 / a :=
by simpa only [one_div] using eq_inv_of_mul_right_eq_one h

lemma eq_one_div_of_mul_eq_one_left {a b : G₀} (h : b * a = 1) : b = 1 / a :=
by simpa only [one_div] using eq_inv_of_mul_left_eq_one h

@[simp] lemma one_div_div (a b : G₀) : 1 / (a / b) = b / a :=
by rw [one_div, div_eq_mul_inv, mul_inv_rev₀, inv_inv₀, div_eq_mul_inv]

lemma one_div_one_div (a : G₀) : 1 / (1 / a) = a :=
by simp

lemma eq_of_one_div_eq_one_div {a b : G₀} (h : 1 / a = 1 / b) : a = b :=
by rw [← one_div_one_div a, h, one_div_one_div]

variables {a b c : G₀}

@[simp] lemma inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 :=
by rw [inv_eq_iff, inv_zero, eq_comm]

@[simp] lemma zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
eq_comm.trans $ inv_eq_zero.trans eq_comm

lemma one_div_mul_one_div_rev (a b : G₀) : (1 / a) * (1 / b) =  1 / (b * a) :=
by simp only [div_eq_mul_inv, one_mul, mul_inv_rev₀]

theorem divp_eq_div (a : G₀) (u : G₀ˣ) : a /ₚ u = a / u :=
by simpa only [div_eq_mul_inv] using congr_arg ((*) a) u.coe_inv'

@[simp] theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) :
  a /ₚ units.mk0 b hb = a / b :=
divp_eq_div _ _

lemma inv_div : (a / b)⁻¹ = b / a :=
by rw [div_eq_mul_inv, mul_inv_rev₀, div_eq_mul_inv, inv_inv₀]

lemma inv_div_left : a⁻¹ / b = (b * a)⁻¹ :=
by rw [mul_inv_rev₀, div_eq_mul_inv]

lemma div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 :=
by { rw div_eq_mul_inv, exact mul_ne_zero ha (inv_ne_zero hb) }

@[simp] lemma div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0:=
by simp [div_eq_mul_inv]

lemma div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
(not_congr div_eq_zero_iff).trans not_or_distrib

lemma div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
by rw [← divp_mk0 _ hc, ← divp_mk0 _ hc, divp_left_inj]

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
⟨λ h, by rw [← h, div_mul_cancel _ hb],
 λ h, by rw [← h, mul_div_cancel _ hb]⟩

lemma eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
by rw [eq_comm, div_eq_iff_mul_eq hc]

lemma div_eq_of_eq_mul {x : G₀} (hx : x ≠ 0) {y z : G₀} (h : y = z * x) : y / x = z :=
(div_eq_iff_mul_eq hx).2 h.symm

lemma eq_div_of_mul_eq {x : G₀} (hx : x ≠ 0) {y z : G₀} (h : z * x = y) : z = y / x :=
eq.symm $ div_eq_of_eq_mul hx h.symm

lemma eq_of_div_eq_one (h : a / b = 1) : a = b :=
begin
  by_cases hb : b = 0,
  { rw [hb, div_zero] at h,
    exact eq_of_zero_eq_one h a b },
  { rwa [div_eq_iff_mul_eq hb, one_mul, eq_comm] at h }
end

lemma div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
⟨eq_of_div_eq_one, λ h, h.symm ▸ div_self hb⟩

lemma div_mul_left {a b : G₀} (hb : b ≠ 0) : b / (a * b) = 1 / a :=
by simp only [div_eq_mul_inv, mul_inv_rev₀, mul_inv_cancel_left₀ hb, one_mul]

lemma mul_div_mul_right (a b : G₀) {c : G₀} (hc : c ≠ 0) :
  (a * c) / (b * c) = a / b :=
by simp only [div_eq_mul_inv, mul_inv_rev₀, mul_assoc, mul_inv_cancel_left₀ hc]

lemma mul_mul_div (a : G₀) {b : G₀} (hb : b ≠ 0) : a = a * b * (1 / b) :=
by simp [hb]

lemma ring.inverse_eq_inv (a : G₀) : ring.inverse a = a⁻¹ :=
begin
  obtain rfl | ha := eq_or_ne a 0,
  { simp },
  { exact ring.inverse_unit (units.mk0 a ha) }
end

@[simp] lemma ring.inverse_eq_inv' : (ring.inverse : G₀ → G₀) = has_inv.inv :=
funext ring.inverse_eq_inv

@[field_simps] lemma div_div_eq_mul_div (a b c : G₀) :
  a / (b / c) = (a * c) / b :=
by rw [div_eq_mul_one_div, one_div_div, ← mul_div_assoc]

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp] lemma div_div_self (a : G₀) : a / (a / a) = a :=
begin
  rw div_div_eq_mul_div,
  exact mul_self_div_self a
end

lemma ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 :=
assume ha : a = 0, begin rw [ha, div_zero] at h, contradiction end

lemma eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
classical.by_cases
  (assume ha, ha)
  (assume ha, ((one_div_ne_zero ha) h).elim)

lemma div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : (a / c) / (b / c) = a / b :=
by rw [div_div_eq_mul_div, div_mul_cancel _ hc]

lemma div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : (a / c) * (c / b) = a / b :=
by rw [← mul_div_assoc, div_mul_cancel _ hc]

@[field_simps] lemma eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
eq_div_iff_mul_eq hb

@[field_simps] lemma div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
(div_eq_iff_mul_eq hb).trans eq_comm

end group_with_zero

section comm_group_with_zero -- comm
variables [comm_group_with_zero G₀] {a b c : G₀}

@[priority 10] -- see Note [lower instance priority]
instance comm_group_with_zero.cancel_comm_monoid_with_zero : cancel_comm_monoid_with_zero G₀ :=
{ ..group_with_zero.cancel_monoid_with_zero, ..comm_group_with_zero.to_comm_monoid_with_zero G₀ }

/-- Pullback a `comm_group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.comm_group_with_zero [has_zero G₀'] [has_mul G₀'] [has_one G₀']
  [has_inv G₀'] [has_div G₀'] (f : G₀' → G₀) (hf : injective f) (zero : f 0 = 0) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  comm_group_with_zero G₀' :=
{ .. hf.group_with_zero f zero one mul inv div, .. hf.comm_semigroup f mul }

/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def function.surjective.comm_group_with_zero [has_zero G₀'] [has_mul G₀']
  [has_one G₀'] [has_inv G₀'] [has_div G₀'] (h01 : (0:G₀') ≠ 1) (f : G₀ → G₀') (hf : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
  (div : ∀ x y, f (x / y) = f x / f y) :
  comm_group_with_zero G₀' :=
{ .. hf.group_with_zero h01 f zero one mul inv div, .. hf.comm_semigroup f mul }

lemma mul_inv₀ : (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
by rw [mul_inv_rev₀, mul_comm]

lemma one_div_mul_one_div (a b : G₀) : (1 / a) * (1 / b) = 1 / (a * b) :=
by rw [one_div_mul_one_div_rev, mul_comm b]

lemma div_mul_right {a : G₀} (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
by rw [mul_comm, div_mul_left ha]

lemma mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b :=
by rw [mul_comm, mul_div_cancel_of_imp h]

lemma mul_div_cancel_left {a : G₀} (b : G₀) (ha : a ≠ 0) : a * b / a = b :=
mul_div_cancel_left_of_imp $ λ h, (ha h).elim

lemma mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a :=
by rw [mul_comm, div_mul_cancel_of_imp h]

lemma mul_div_cancel' (a : G₀) {b : G₀} (hb : b ≠ 0) : b * (a / b) = a :=
by rw [mul_comm, (div_mul_cancel _ hb)]

local attribute [simp] mul_assoc mul_comm mul_left_comm

lemma div_mul_div (a b c d : G₀) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
by simp [div_eq_mul_inv, mul_inv₀]

lemma mul_div_mul_left (a b : G₀) {c : G₀} (hc : c ≠ 0) :
      (c * a) / (c * b) = a / b :=
by rw [mul_comm c, mul_comm c, mul_div_mul_right _ _ hc]

@[field_simps] lemma div_mul_eq_mul_div (a b c : G₀) : (b / c) * a = (b * a) / c :=
by simp [div_eq_mul_inv]

lemma div_mul_eq_mul_div_comm (a b c : G₀) :
      (b / c) * a = b * (a / c) :=
by rw [div_mul_eq_mul_div, ← one_mul c, ← div_mul_div, div_one, one_mul]

lemma mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0)
      (hd : d ≠ 0) (h : a / b = c / d) : a * d = c * b :=
by rw [← mul_one (a*d), mul_assoc, mul_comm d, ← mul_assoc, ← div_self hb,
       ← div_mul_eq_mul_div_comm, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps] lemma div_div_eq_div_mul (a b c : G₀) :
      (a / b) / c = a / (b * c) :=
by rw [div_eq_mul_one_div, div_mul_div, mul_one]

lemma div_div_div_div_eq (a : G₀) {b c d : G₀} :
      (a / b) / (c / d) = (a * d) / (b * c) :=
by rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div_eq_div_mul]

lemma div_mul_eq_div_mul_one_div (a b c : G₀) :
      a / (b * c) = (a / b) * (1 / c) :=
by rw [← div_div_eq_div_mul, ← div_eq_mul_one_div]

lemma div_helper {a : G₀} (b : G₀) (h : a ≠ 0) : (1 / (a * b)) * a = 1 / b :=
by rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

end comm_group_with_zero

section comm_group_with_zero
variables [comm_group_with_zero G₀] {a b c d : G₀}

lemma div_eq_inv_mul : a / b = b⁻¹ * a :=
by rw [div_eq_mul_inv, mul_comm]

lemma mul_div_right_comm (a b c : G₀) : (a * b) / c = (a / c) * b :=
by rw [div_eq_mul_inv, mul_assoc, mul_comm b, ← mul_assoc, div_eq_mul_inv]

lemma mul_comm_div' (a b c : G₀) : (a / b) * c = a * (c / b) :=
by rw [← mul_div_assoc, mul_div_right_comm]

lemma div_mul_comm' (a b c : G₀) : (a / b) * c = (c / b) * a :=
by rw [div_mul_eq_mul_div, mul_comm, mul_div_right_comm]

lemma mul_div_comm (a b c : G₀) : a * (b / c) = b * (a / c) :=
by rw [← mul_div_assoc, mul_comm, mul_div_assoc]

lemma div_right_comm (a : G₀) : (a / b) / c = (a / c) / b :=
by rw [div_div_eq_div_mul, div_div_eq_div_mul, mul_comm]

@[field_simps] lemma div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
calc a / b = c / d ↔ a / b * (b * d) = c / d * (b * d) :
by rw [mul_left_inj' (mul_ne_zero hb hd)]
               ... ↔ a * d = c * b :
by rw [← mul_assoc, div_mul_cancel _ hb,
      ← mul_assoc, mul_right_comm, div_mul_cancel _ hd]

lemma div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b :=
by rw [div_eq_mul_inv, inv_div, mul_div_cancel' _ ha]

end comm_group_with_zero

namespace semiconj_by

@[simp] lemma zero_right [mul_zero_class G₀] (a : G₀) : semiconj_by a 0 0 :=
by simp only [semiconj_by, mul_zero, zero_mul]

@[simp] lemma zero_left [mul_zero_class G₀] (x y : G₀) : semiconj_by 0 x y :=
by simp only [semiconj_by, mul_zero, zero_mul]

variables [group_with_zero G₀] {a x y x' y' : G₀}

@[simp] lemma inv_symm_left_iff₀ : semiconj_by a⁻¹ x y ↔ semiconj_by a y x :=
classical.by_cases
  (λ ha : a = 0, by simp only [ha, inv_zero, semiconj_by.zero_left])
  (λ ha, @units_inv_symm_left_iff _ _ (units.mk0 a ha) _ _)

lemma inv_symm_left₀ (h : semiconj_by a x y) : semiconj_by a⁻¹ y x :=
semiconj_by.inv_symm_left_iff₀.2 h

lemma inv_right₀ (h : semiconj_by a x y) : semiconj_by a x⁻¹ y⁻¹ :=
begin
  by_cases ha : a = 0,
  { simp only [ha, zero_left] },
  by_cases hx : x = 0,
  { subst x,
    simp only [semiconj_by, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h,
    simp [h.resolve_right ha] },
  { have := mul_ne_zero ha hx,
    rw [h.eq, mul_ne_zero_iff] at this,
    exact @units_inv_right _ _ _ (units.mk0 x hx) (units.mk0 y this.1) h },
end

@[simp] lemma inv_right_iff₀ : semiconj_by a x⁻¹ y⁻¹ ↔ semiconj_by a x y :=
⟨λ h, inv_inv₀ x ▸ inv_inv₀ y ▸ h.inv_right₀, inv_right₀⟩

lemma div_right (h : semiconj_by a x y) (h' : semiconj_by a x' y') :
  semiconj_by a (x / x') (y / y') :=
by { rw [div_eq_mul_inv, div_eq_mul_inv], exact h.mul_right h'.inv_right₀ }

end semiconj_by

namespace commute

@[simp] theorem zero_right [mul_zero_class G₀] (a : G₀) :commute a 0 := semiconj_by.zero_right a
@[simp] theorem zero_left [mul_zero_class G₀] (a : G₀) : commute 0 a := semiconj_by.zero_left a a

variables [group_with_zero G₀] {a b c : G₀}

@[simp] theorem inv_left_iff₀ : commute a⁻¹ b ↔ commute a b :=
semiconj_by.inv_symm_left_iff₀

theorem inv_left₀ (h : commute a b) : commute a⁻¹ b := inv_left_iff₀.2 h

@[simp] theorem inv_right_iff₀ : commute a b⁻¹ ↔ commute a b :=
semiconj_by.inv_right_iff₀

theorem inv_right₀ (h : commute a b) : commute a b⁻¹ := inv_right_iff₀.2 h

theorem inv_inv₀ (h : commute a b) : commute a⁻¹ b⁻¹ := h.inv_left₀.inv_right₀

@[simp] theorem div_right (hab : commute a b) (hac : commute a c) :
  commute a (b / c) :=
hab.div_right hac

@[simp] theorem div_left (hac : commute a c) (hbc : commute b c) :
  commute (a / b) c :=
by { rw div_eq_mul_inv, exact hac.mul_left hbc.inv_left₀ }

end commute

namespace monoid_with_zero_hom

variables [group_with_zero G₀] [group_with_zero G₀'] [monoid_with_zero M₀] [nontrivial M₀]

section monoid_with_zero

variables (f : G₀ →*₀ M₀) {a : G₀}

lemma map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
⟨λ hfa ha, hfa $ ha.symm ▸ f.map_zero, λ ha, ((is_unit.mk0 a ha).map f.to_monoid_hom).ne_zero⟩

@[simp] lemma map_eq_zero : f a = 0 ↔ a = 0 :=
not_iff_not.1 f.map_ne_zero

end monoid_with_zero

section group_with_zero

variables (f : G₀ →*₀ G₀') (a b : G₀)

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp] lemma map_inv : f a⁻¹ = (f a)⁻¹ :=
begin
  by_cases h : a = 0, by simp [h],
  apply eq_inv_of_mul_left_eq_one,
  rw [← f.map_mul, inv_mul_cancel h, f.map_one]
end

@[simp] lemma map_div : f (a / b) = f a / f b :=
by simpa only [div_eq_mul_inv] using ((f.map_mul _ _).trans $ _root_.congr_arg _ $ f.map_inv b)

end group_with_zero

end monoid_with_zero_hom

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def inv_monoid_with_zero_hom {G₀ : Type*} [comm_group_with_zero G₀] : G₀ →*₀ G₀ :=
{ to_fun := has_inv.inv,
  map_zero' := inv_zero,
  map_one' := inv_one,
  map_mul' := λ _ _, mul_inv₀ }

@[simp] lemma monoid_hom.map_units_inv {M G₀ : Type*} [monoid M] [group_with_zero G₀]
  (f : M →* G₀) (u : Mˣ) : f ↑u⁻¹ = (f u)⁻¹ :=
by rw [← units.coe_map, ← units.coe_map, ← units.coe_inv', monoid_hom.map_inv]

@[simp] lemma monoid_with_zero_hom.map_units_inv {M G₀ : Type*} [monoid_with_zero M]
  [group_with_zero G₀] (f : M →*₀ G₀) (u : Mˣ) : f ↑u⁻¹ = (f u)⁻¹ :=
f.to_monoid_hom.map_units_inv u

section noncomputable_defs

variables {M : Type*} [nontrivial M]

/-- Constructs a `group_with_zero` structure on a `monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def group_with_zero_of_is_unit_or_eq_zero [hM : monoid_with_zero M]
  (h : ∀ (a : M), is_unit a ∨ a = 0) : group_with_zero M :=
{ inv := λ a, if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹,
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ a h0, by
  { change a * (if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).unit⁻¹) = 1,
    rw [dif_neg h0, units.mul_inv_eq_iff_eq_mul, one_mul, is_unit.unit_spec] },
  exists_pair_ne := nontrivial.exists_pair_ne,
.. hM }

/-- Constructs a `comm_group_with_zero` structure on a `comm_monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def comm_group_with_zero_of_is_unit_or_eq_zero [hM : comm_monoid_with_zero M]
  (h : ∀ (a : M), is_unit a ∨ a = 0) : comm_group_with_zero M :=
{ .. (group_with_zero_of_is_unit_or_eq_zero h), .. hM }

end noncomputable_defs
