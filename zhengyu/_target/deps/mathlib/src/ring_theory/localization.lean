/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston
-/
import data.equiv.ring
import group_theory.monoid_localization
import ring_theory.algebraic
import ring_theory.ideal.local_ring
import ring_theory.ideal.quotient
import ring_theory.integral_closure
import ring_theory.non_zero_divisors
import group_theory.submonoid.inverses
import tactic.ring_exp

/-!
# Localizations of commutative rings

We characterize the localization of a commutative ring `R` at a submonoid `M` up to
isomorphism; that is, a commutative ring `S` is the localization of `R` at `M` iff we can find a
ring homomorphism `f : R →+* S` satisfying 3 properties:
1. For all `y ∈ M`, `f y` is a unit;
2. For all `z : S`, there exists `(x, y) : R × M` such that `z * f y = f x`;
3. For all `x, y : R`, `f x = f y` iff there exists `c ∈ M` such that `x * c = y * c`.

In the following, let `R, P` be commutative rings, `S, Q` be `R`- and `P`-algebras
and `M, T` be submonoids of `R` and `P` respectively, e.g.:
```
variables (R S P Q : Type*) [comm_ring R] [comm_ring S] [comm_ring P] [comm_ring Q]
variables [algebra R S] [algebra P Q] (M : submonoid R) (T : submonoid P)
```

## Main definitions

 * `is_localization (M : submonoid R) (S : Type*)` is a typeclass expressing that `S` is a
   localization of `R` at `M`, i.e. the canonical map `algebra_map R S : R →+* S` is a
   localization map (satisfying the above properties).
 * `is_localization.mk' S` is a surjection sending `(x, y) : R × M` to `f x * (f y)⁻¹`
 * `is_localization.lift` is the ring homomorphism from `S` induced by a homomorphism from `R`
   which maps elements of `M` to invertible elements of the codomain.
 * `is_localization.map S Q` is the ring homomorphism from `S` to `Q` which maps elements
   of `M` to elements of `T`
 * `is_localization.ring_equiv_of_ring_equiv`: if `R` and `P` are isomorphic by an isomorphism
   sending `M` to `T`, then `S` and `Q` are isomorphic
 * `is_localization.alg_equiv`: if `Q` is another localization of `R` at `M`, then `S` and `Q`
   are isomorphic as `R`-algebras
 * `is_localization.is_integer` is a predicate stating that `x : S` is in the image of `R`
 * `is_localization.away (x : R) S` expresses that `S` is a localization away from `x`, as an
   abbreviation of `is_localization (submonoid.powers x) S`
 * `is_localization.at_prime (I : ideal R) [is_prime I] (S : Type*)` expresses that `S` is a
   localization at (the complement of) a prime ideal `I`, as an abbreviation of
   `is_localization I.prime_compl S`
 * `is_fraction_ring R K` expresses that `K` is a field of fractions of `R`, as an abbreviation of
   `is_localization (non_zero_divisors R) K`

## Main results

 * `localization M S`, a construction of the localization as a quotient type, defined in
   `group_theory.monoid_localization`, has `comm_ring`, `algebra R` and `is_localization M`
   instances if `R` is a ring. `localization.away`, `localization.at_prime` and `fraction_ring`
   are abbreviations for `localization`s and have their corresponding `is_localization` instances
 * `is_localization.at_prime.local_ring`: a theorem (not an instance) stating a localization at the
   complement of a prime ideal is a local ring
 * `is_fraction_ring.field`: a definition (not an instance) stating the localization of an integral
   domain `R` at `R \ {0}` is a field
 * `rat.is_fraction_ring` is an instance stating `ℚ` is the field of fractions of `ℤ`

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

A previous version of this file used a fully bundled type of ring localization maps,
then used a type synonym `f.codomain` for `f : localization_map M S` to instantiate the
`R`-algebra structure on `S`. This results in defining ad-hoc copies for everything already
defined on `S`. By making `is_localization` a predicate on the `algebra_map R S`,
we can ensure the localization map commutes nicely with other `algebra_map`s.

To prove most lemmas about a localization map `algebra_map R S` in this file we invoke the
corresponding proof for the underlying `comm_monoid` localization map
`is_localization.to_localization_map M S`, which can be found in `group_theory.monoid_localization`
and the namespace `submonoid.localization_map`.

To reason about the localization as a quotient type, use `mk_eq_of_mk'` and associated lemmas.
These show the quotient map `mk : R → M → localization M` equals the surjection
`localization_map.mk'` induced by the map `algebra_map : R →+* localization M`.
The lemma `mk_eq_of_mk'` hence gives you access to the results in the rest of the file,
which are about the `localization_map.mk'` induced by any localization map.

The proof that "a `comm_ring` `K` which is the localization of an integral domain `R` at `R \ {0}`
is a field" is a `def` rather than an `instance`, so if you want to reason about a field of
fractions `K`, assume `[field K]` instead of just `[comm_ring K]`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

open function
open_locale big_operators polynomial

/-- The typeclass `is_localization (M : submodule R) S` where `S` is an `R`-algebra
expresses that `S` is isomorphic to the localization of `R` at `M`. -/
class is_localization : Prop :=
(map_units [] : ∀ y : M, is_unit (algebra_map R S y))
(surj [] : ∀ z : S, ∃ x : R × M, z * algebra_map R S x.2 = algebra_map R S x.1)
(eq_iff_exists [] : ∀ {x y}, algebra_map R S x = algebra_map R S y ↔ ∃ c : M, x * c = y * c)

variables {M S}

namespace is_localization

section is_localization

variables [is_localization M S]

section

variables (M)

lemma of_le (N : submonoid R) (h₁ : M ≤ N)
  (h₂ : ∀ r ∈ N, is_unit (algebra_map R S r)) : is_localization N S :=
{ map_units := λ r, h₂ r r.2,
  surj := λ s, by { obtain ⟨⟨x, y, hy⟩, H⟩ := is_localization.surj M s, exact ⟨⟨x, y, h₁ hy⟩, H⟩ },
  eq_iff_exists := λ x y, begin
    split,
    { rw is_localization.eq_iff_exists M,
      rintro ⟨c, hc⟩,
      exact ⟨⟨c, h₁ c.2⟩, hc⟩ },
    { rintro ⟨c, h⟩,
      simpa only [set_like.coe_mk, map_mul, (h₂ c c.2).mul_left_inj] using
        congr_arg (algebra_map R S) h }
  end }

variables (S)

/-- `is_localization.to_localization_map M S` shows `S` is the monoid localization of `R` at `M`. -/
@[simps]
def to_localization_map : submonoid.localization_map M S :=
{ to_fun := algebra_map R S,
  map_units' := is_localization.map_units _,
  surj' := is_localization.surj _,
  eq_iff_exists' := λ _ _, is_localization.eq_iff_exists _ _,
  .. algebra_map R S }

@[simp]
lemma to_localization_map_to_map :
  (to_localization_map M S).to_map = (algebra_map R S : R →* S) := rfl

lemma to_localization_map_to_map_apply (x) :
  (to_localization_map M S).to_map x = algebra_map R S x := rfl

end

section

variables (R)

-- TODO: define a subalgebra of `is_integer`s
/-- Given `a : S`, `S` a localization of `R`, `is_integer R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def is_integer (a : S) : Prop := a ∈ (algebra_map R S).range

end

lemma is_integer_zero : is_integer R (0 : S) := subring.zero_mem _
lemma is_integer_one : is_integer R (1 : S) := subring.one_mem _

lemma is_integer_add {a b : S} (ha : is_integer R a) (hb : is_integer R b) :
  is_integer R (a + b) :=
subring.add_mem _ ha hb

lemma is_integer_mul {a b : S} (ha : is_integer R a) (hb : is_integer R b) :
  is_integer R (a * b) :=
subring.mul_mem _ ha hb

lemma is_integer_smul {a : R} {b : S} (hb : is_integer R b) :
  is_integer R (a • b) :=
begin
  rcases hb with ⟨b', hb⟩,
  use a * b',
  rw [←hb, (algebra_map R S).map_mul, algebra.smul_def]
end

variables (M)

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
lemma exists_integer_multiple' (a : S) :
  ∃ (b : M), is_integer R (a * algebra_map R S b) :=
let ⟨⟨num, denom⟩, h⟩ := is_localization.surj _ a in ⟨denom, set.mem_range.mpr ⟨num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_scalar` instance.
-/
lemma exists_integer_multiple (a : S) :
  ∃ (b : M), is_integer R ((b : R) • a) :=
by { simp_rw [algebra.smul_def, mul_comm _ a], apply exists_integer_multiple' }

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
noncomputable def sec (z : S) : R × M :=
classical.some $ is_localization.surj _ z

@[simp] lemma to_localization_map_sec : (to_localization_map M S).sec = sec M := rfl

/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x` (so this lemma is true by definition). -/
lemma sec_spec (z : S) :
  z * algebra_map R S (is_localization.sec M z).2 =
    algebra_map R S (is_localization.sec M z).1 :=
classical.some_spec $ is_localization.surj _ z

/-- Given `z : S`, `is_localization.sec M z` is defined to be a pair `(x, y) : R × M` such
that `z * f y = f x`, so this lemma is just an application of `S`'s commutativity. -/
lemma sec_spec' (z : S) :
  algebra_map R S (is_localization.sec M z).1 =
    algebra_map R S (is_localization.sec M z).2 * z :=
by rw [mul_comm, sec_spec]

open_locale big_operators

/-- We can clear the denominators of a `finset`-indexed family of fractions. -/
lemma exist_integer_multiples {ι : Type*} (s : finset ι) (f : ι → S) :
  ∃ (b : M), ∀ i ∈ s, is_localization.is_integer R ((b : R) • f i) :=
begin
  haveI := classical.prop_decidable,
  refine ⟨∏ i in s, (sec M (f i)).2, λ i hi, ⟨_, _⟩⟩,
  { exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1 },
  rw [ring_hom.map_mul, sec_spec', ←mul_assoc, ←(algebra_map R S).map_mul, ← algebra.smul_def],
  congr' 2,
  refine trans _ ((submonoid.subtype M).map_prod _ _).symm,
  rw [mul_comm, ←finset.prod_insert (s.not_mem_erase i), finset.insert_erase hi],
  refl
end

/-- We can clear the denominators of a `fintype`-indexed family of fractions. -/
lemma exist_integer_multiples_of_fintype {ι : Type*} [fintype ι] (f : ι → S) :
  ∃ (b : M), ∀ i, is_localization.is_integer R ((b : R) • f i) :=
begin
  obtain ⟨b, hb⟩ := exist_integer_multiples M finset.univ f,
  exact ⟨b, λ i, hb i (finset.mem_univ _)⟩
end

/-- We can clear the denominators of a finite set of fractions. -/
lemma exist_integer_multiples_of_finset (s : finset S) :
  ∃ (b : M), ∀ a ∈ s, is_integer R ((b : R) • a) :=
exist_integer_multiples M s id

/-- A choice of a common multiple of the denominators of a `finset`-indexed family of fractions. -/
noncomputable
def common_denom {ι : Type*} (s : finset ι) (f : ι → S) : M :=
(exist_integer_multiples M s f).some

/-- The numerator of a fraction after clearing the denominators
of a `finset`-indexed family of fractions. -/
noncomputable
def integer_multiple {ι : Type*} (s : finset ι) (f : ι → S) (i : s) : R :=
((exist_integer_multiples M s f).some_spec i i.prop).some

@[simp]
lemma map_integer_multiple {ι : Type*} (s : finset ι) (f : ι → S) (i : s) :
  algebra_map R S (integer_multiple M s f i) = common_denom M s f • f i :=
((exist_integer_multiples M s f).some_spec _ i.prop).some_spec

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable
def common_denom_of_finset (s : finset S) : M :=
common_denom M s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable
def finset_integer_multiple [decidable_eq R] (s : finset S) : finset R :=
s.attach.image (λ t, integer_multiple M s id t)

open_locale pointwise

lemma finset_integer_multiple_image [decidable_eq R] (s : finset S) :
  algebra_map R S '' (finset_integer_multiple M s) =
    common_denom_of_finset M s • s :=
begin
  delta finset_integer_multiple common_denom,
  rw finset.coe_image,
  ext,
  split,
  { rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩,
    rw map_integer_multiple,
    exact set.mem_image_of_mem _ x.prop },
  { rintro ⟨x, hx, rfl⟩,
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integer_multiple M s id _⟩ }
end

variables {R M}

lemma map_right_cancel {x y} {c : M} (h : algebra_map R S (c * x) = algebra_map R S (c * y)) :
  algebra_map R S x = algebra_map R S y :=
(to_localization_map M S).map_right_cancel h

lemma map_left_cancel {x y} {c : M} (h : algebra_map R S (x * c) = algebra_map R S (y * c)) :
  algebra_map R S x = algebra_map R S y :=
(to_localization_map M S).map_left_cancel h

lemma eq_zero_of_fst_eq_zero {z x} {y : M}
  (h : z * algebra_map R S y = algebra_map R S x) (hx : x = 0) : z = 0 :=
by { rw [hx, (algebra_map R S).map_zero] at h,
     exact (is_unit.mul_left_eq_zero (is_localization.map_units S y)).1 h}

variables (M S)

lemma map_eq_zero_iff (r : R) :
  algebra_map R S r = 0 ↔ ∃ m : M, r * m = 0 :=
begin
  split,
  intro h,
  { obtain ⟨m, hm⟩ := (is_localization.eq_iff_exists M S).mp
      ((algebra_map R S).map_zero.trans h.symm),
    exact ⟨m, by simpa using hm.symm⟩ },
  { rintro ⟨m, hm⟩,
    rw [← (is_localization.map_units S m).mul_left_inj, zero_mul, ← ring_hom.map_mul, hm,
      ring_hom.map_zero] }
end

variables {M}

/-- `is_localization.mk' S` is the surjection sending `(x, y) : R × M` to
`f x * (f y)⁻¹`. -/
noncomputable def mk' (x : R) (y : M) : S :=
(to_localization_map M S).mk' x y

@[simp] lemma mk'_sec (z : S) :
  mk' S (is_localization.sec M z).1 (is_localization.sec M z).2 = z :=
(to_localization_map M S).mk'_sec _

lemma mk'_mul (x₁ x₂ : R) (y₁ y₂ : M) :
  mk' S (x₁ * x₂) (y₁ * y₂) = mk' S x₁ y₁ * mk' S x₂ y₂ :=
(to_localization_map M S).mk'_mul _ _ _ _

lemma mk'_one (x) : mk' S x (1 : M) = algebra_map R S x :=
(to_localization_map M S).mk'_one _

@[simp]
lemma mk'_spec (x) (y : M) :
  mk' S x y * algebra_map R S y = algebra_map R S x :=
(to_localization_map M S).mk'_spec _ _

@[simp]
lemma mk'_spec' (x) (y : M) :
  algebra_map R S y * mk' S x y = algebra_map R S x :=
(to_localization_map M S).mk'_spec' _ _

@[simp]
lemma mk'_spec_mk (x) (y : R) (hy : y ∈ M) :
  mk' S x ⟨y, hy⟩ * algebra_map R S y = algebra_map R S x :=
mk'_spec S x ⟨y, hy⟩

@[simp]
lemma mk'_spec'_mk (x) (y : R) (hy : y ∈ M) :
  algebra_map R S y * mk' S x ⟨y, hy⟩ = algebra_map R S x :=
mk'_spec' S x ⟨y, hy⟩

variables {S}

theorem eq_mk'_iff_mul_eq {x} {y : M} {z} :
  z = mk' S x y ↔ z * algebra_map R S y = algebra_map R S x :=
(to_localization_map M S).eq_mk'_iff_mul_eq

theorem mk'_eq_iff_eq_mul {x} {y : M} {z} :
  mk' S x y = z ↔ algebra_map R S x = z * algebra_map R S y :=
(to_localization_map M S).mk'_eq_iff_eq_mul

variables (M)

lemma mk'_surjective (z : S) : ∃ x (y : M), mk' S x y = z :=
let ⟨r, hr⟩ := is_localization.surj _ z in ⟨r.1, r.2, (eq_mk'_iff_mul_eq.2 hr).symm⟩

variables {M}

lemma mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : M} :
  mk' S x₁ y₁ = mk' S x₂ y₂ ↔ algebra_map R S (x₁ * y₂) = algebra_map R S (x₂ * y₁) :=
(to_localization_map M S).mk'_eq_iff_eq

lemma mk'_mem_iff {x} {y : M} {I : ideal S} : mk' S x y ∈ I ↔ algebra_map R S x ∈ I :=
begin
  split;
  intro h,
  { rw [← mk'_spec S x y, mul_comm],
    exact I.mul_mem_left ((algebra_map R S) y) h },
  { rw ← mk'_spec S x y at h,
    obtain ⟨b, hb⟩ := is_unit_iff_exists_inv.1 (map_units S y),
    have := I.mul_mem_left b h,
    rwa [mul_comm, mul_assoc, hb, mul_one] at this }
end

protected lemma eq {a₁ b₁} {a₂ b₂ : M} :
  mk' S a₁ a₂ = mk' S b₁ b₂ ↔ ∃ c : M, a₁ * b₂ * c = b₁ * a₂ * c :=
(to_localization_map M S).eq

lemma mk'_eq_zero_iff (x : R) (s : M) :
  mk' S x s = 0 ↔ ∃ (m : M), x * m = 0 :=
by rw [← (map_units S s).mul_left_inj, mk'_spec, zero_mul, map_eq_zero_iff M]

section ext

variables [algebra R P] [is_localization M P]

lemma eq_iff_eq {x y} :
  algebra_map R S x = algebra_map R S y ↔ algebra_map R P x = algebra_map R P y :=
(to_localization_map M S).eq_iff_eq (to_localization_map M P)

lemma mk'_eq_iff_mk'_eq {x₁ x₂}
  {y₁ y₂ : M} : mk' S x₁ y₁ = mk' S x₂ y₂ ↔ mk' P x₁ y₁ = mk' P x₂ y₂ :=
(to_localization_map M S).mk'_eq_iff_mk'_eq (to_localization_map M P)

lemma mk'_eq_of_eq {a₁ b₁ : R} {a₂ b₂ : M} (H : b₁ * a₂ = a₁ * b₂) :
  mk' S a₁ a₂ = mk' S b₁ b₂ :=
(to_localization_map M S).mk'_eq_of_eq H

variables (S)

@[simp] lemma mk'_self {x : R} (hx : x ∈ M) : mk' S x ⟨x, hx⟩ = 1 :=
(to_localization_map M S).mk'_self _ hx

@[simp] lemma mk'_self' {x : M} : mk' S (x : R) x = 1 :=
(to_localization_map M S).mk'_self' _

lemma mk'_self'' {x : M} : mk' S x.1 x = 1 :=
mk'_self' _

end ext

lemma mul_mk'_eq_mk'_of_mul (x y : R) (z : M) :
  (algebra_map R S) x * mk' S y z = mk' S (x * y) z :=
(to_localization_map M S).mul_mk'_eq_mk'_of_mul _ _ _

lemma mk'_eq_mul_mk'_one (x : R) (y : M) :
  mk' S x y = (algebra_map R S) x * mk' S 1 y :=
((to_localization_map M S).mul_mk'_one_eq_mk' _ _).symm

@[simp] lemma mk'_mul_cancel_left (x : R) (y : M) :
  mk' S (y * x : R) y = (algebra_map R S) x :=
(to_localization_map M S).mk'_mul_cancel_left _ _

lemma mk'_mul_cancel_right (x : R) (y : M) :
  mk' S (x * y) y = (algebra_map R S) x :=
(to_localization_map M S).mk'_mul_cancel_right _ _

@[simp] lemma mk'_mul_mk'_eq_one (x y : M) :
  mk' S (x : R) y * mk' S (y : R) x = 1 :=
by rw [←mk'_mul, mul_comm]; exact mk'_self _ _

lemma mk'_mul_mk'_eq_one' (x : R) (y : M) (h : x ∈ M) :
  mk' S x y * mk' S (y : R) ⟨x, h⟩ = 1 :=
mk'_mul_mk'_eq_one ⟨x, h⟩ _

section

variables (M)

lemma is_unit_comp (j : S →+* P) (y : M) :
  is_unit (j.comp (algebra_map R S) y) :=
(to_localization_map M S).is_unit_comp j.to_monoid_hom _

end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g(M) ⊆ units P`, `f x = f y → g x = g y` for all `x y : R`. -/
lemma eq_of_eq {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) {x y}
  (h : (algebra_map R S) x = (algebra_map R S) y) :
  g x = g y :=
@submonoid.localization_map.eq_of_eq _ _ _ _ _ _ _
  (to_localization_map M S) g.to_monoid_hom hg _ _ h

lemma mk'_add (x₁ x₂ : R) (y₁ y₂ : M) :
  mk' S (x₁ * y₂ + x₂ * y₁) (y₁ * y₂) = mk' S x₁ y₁ + mk' S x₂ y₂ :=
mk'_eq_iff_eq_mul.2 $ eq.symm
begin
  rw [mul_comm (_ + _), mul_add, mul_mk'_eq_mk'_of_mul, ←eq_sub_iff_add_eq, mk'_eq_iff_eq_mul,
      mul_comm _ ((algebra_map R S) _), mul_sub, eq_sub_iff_add_eq, ←eq_sub_iff_add_eq', ←mul_assoc,
      ←(algebra_map R S).map_mul, mul_mk'_eq_mk'_of_mul, mk'_eq_iff_eq_mul],
  simp only [(algebra_map R S).map_add, submonoid.coe_mul, (algebra_map R S).map_mul],
  ring_exp,
end

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →+* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` sending `z : S` to `g x * (g y)⁻¹`, where `(x, y) : R × M` are such that
`z = f x * (f y)⁻¹`. -/
noncomputable def lift {g : R →+* P} (hg : ∀ y : M, is_unit (g y)) : S →+* P :=
ring_hom.mk' (@submonoid.localization_map.lift _ _ _ _ _ _ _
  (to_localization_map M S) g.to_monoid_hom hg) $
begin
  intros x y,
  rw [(to_localization_map M S).lift_spec, mul_comm, add_mul, ←sub_eq_iff_eq_add, eq_comm,
      (to_localization_map M S).lift_spec_mul, mul_comm _ (_ - _), sub_mul, eq_sub_iff_add_eq',
      ←eq_sub_iff_add_eq, mul_assoc, (to_localization_map M S).lift_spec_mul],
  show g _ * (g _ * g _) = g _ * (g _ * g _ - g _ * g _),
  simp only [← g.map_sub, ← g.map_mul, to_localization_map_sec],
  apply eq_of_eq hg,
  rw [(algebra_map R S).map_mul, sec_spec', mul_sub, (algebra_map R S).map_sub],
  simp only [ring_hom.map_mul, sec_spec'],
  ring,
  assumption
end

variables {g : R →+* P} (hg : ∀ y : M, is_unit (g y))

/-- Given a localization map `f : R →+* S` for a submonoid `M ⊆ R` and a map of `comm_ring`s
`g : R →* P` such that `g y` is invertible for all `y : M`, the homomorphism induced from
`S` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : R, y ∈ M`. -/
lemma lift_mk' (x y) :
  lift hg (mk' S x y) = g x * ↑(is_unit.lift_right (g.to_monoid_hom.mrestrict M) hg y)⁻¹ :=
(to_localization_map M S).lift_mk' _ _ _

lemma lift_mk'_spec (x v) (y : M) :
  lift hg (mk' S x y) = v ↔ g x = g y * v :=
(to_localization_map M S).lift_mk'_spec _ _ _ _

@[simp] lemma lift_eq (x : R) :
  lift hg ((algebra_map R S) x) = g x :=
(to_localization_map M S).lift_eq _ _

lemma lift_eq_iff {x y : R × M} :
  lift hg (mk' S x.1 x.2) = lift hg (mk' S y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) :=
(to_localization_map M S).lift_eq_iff _

@[simp] lemma lift_comp : (lift hg).comp (algebra_map R S) = g :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ (to_localization_map M S).lift_comp _

@[simp] lemma lift_of_comp (j : S →+* P) :
  lift (is_unit_comp M j) = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ (to_localization_map M S).lift_of_comp j.to_monoid_hom

variables (M)
/-- See note [partially-applied ext lemmas] -/
lemma monoid_hom_ext ⦃j k : S →* P⦄
  (h : j.comp (algebra_map R S : R →* S) = k.comp (algebra_map R S)) : j = k :=
submonoid.localization_map.epic_of_localization_map (to_localization_map M S) $
  monoid_hom.congr_fun h

/-- See note [partially-applied ext lemmas] -/
lemma ring_hom_ext ⦃j k : S →+* P⦄
  (h : j.comp (algebra_map R S) = k.comp (algebra_map R S)) : j = k :=
ring_hom.coe_monoid_hom_injective $ monoid_hom_ext M $ monoid_hom.ext $ ring_hom.congr_fun h

/-- To show `j` and `k` agree on the whole localization, it suffices to show they agree
on the image of the base ring, if they preserve `1` and `*`. -/
protected lemma ext (j k : S → P) (hj1 : j 1 = 1) (hk1 : k 1 = 1)
  (hjm : ∀ a b, j (a * b) = j a * j b) (hkm : ∀ a b, k (a * b) = k a * k b)
  (h : ∀ a, j (algebra_map R S a) = k (algebra_map R S a)) : j = k :=
monoid_hom.mk.inj (monoid_hom_ext M $ monoid_hom.ext h : (⟨j, hj1, hjm⟩ : S →* P) = ⟨k, hk1, hkm⟩)

variables {M}

lemma lift_unique {j : S →+* P}
  (hj : ∀ x, j ((algebra_map R S) x) = g x) : lift hg = j :=
ring_hom.ext $ monoid_hom.ext_iff.1 $ @submonoid.localization_map.lift_unique
  _ _ _ _ _ _ _ (to_localization_map M S) g.to_monoid_hom hg j.to_monoid_hom hj

@[simp] lemma lift_id (x) : lift (map_units S : ∀ y : M, is_unit _) x = x :=
(to_localization_map M S).lift_id _

lemma lift_surjective_iff :
  surjective (lift hg : S → P) ↔ ∀ v : P, ∃ x : R × M, v * g x.2 = g x.1 :=
(to_localization_map M S).lift_surjective_iff hg

lemma lift_injective_iff :
  injective (lift hg : S → P) ↔ ∀ x y, algebra_map R S x = algebra_map R S y ↔ g x = g y :=
(to_localization_map M S).lift_injective_iff hg

section map

variables {T : submonoid P} {Q : Type*} [comm_ring Q] (hy : M ≤ T.comap g)
variables [algebra P Q] [is_localization T Q]

section

variables (Q)

/-- Map a homomorphism `g : R →+* P` to `S →+* Q`, where `S` and `Q` are
localizations of `R` and `P` at `M` and `T` respectively,
such that `g(M) ⊆ T`.

We send `z : S` to `algebra_map P Q (g x) * (algebra_map P Q (g y))⁻¹`, where
`(x, y) : R × M` are such that `z = f x * (f y)⁻¹`. -/
noncomputable def map (g : R →+* P) (hy : M ≤ T.comap g) : S →+* Q :=
@lift R _ M _ _ _ _ _ _ ((algebra_map P Q).comp g) (λ y, map_units _ ⟨g y, hy y.2⟩)

end

lemma map_eq (x) :
  map Q g hy ((algebra_map R S) x) = algebra_map P Q (g x) :=
lift_eq (λ y, map_units _ ⟨g y, hy y.2⟩) x

@[simp] lemma map_comp :
  (map Q g hy).comp (algebra_map R S) = (algebra_map P Q).comp g :=
lift_comp $ λ y, map_units _ ⟨g y, hy y.2⟩

lemma map_mk' (x) (y : M) :
  map Q g hy (mk' S x y) = mk' Q (g x) ⟨g y, hy y.2⟩ :=
@submonoid.localization_map.map_mk' _ _ _ _ _ _ _ (to_localization_map M S)
g.to_monoid_hom _ (λ y, hy y.2) _ _ (to_localization_map T Q) _ _

@[simp] lemma map_id (z : S) (h : M ≤ M.comap (ring_hom.id R) := le_refl M) :
  map S (ring_hom.id _) h z = z :=
lift_id _

lemma map_unique (j : S →+* Q)
  (hj : ∀ x : R, j (algebra_map R S x) = algebra_map P Q (g x)) : map Q g hy = j :=
lift_unique (λ y, map_units _ ⟨g y, hy y.2⟩) hj

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_comp_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  [algebra A W] [is_localization U W] {l : P →+* A} (hl : T ≤ U.comap l) :
  (map W l hl).comp (map Q g hy : S →+* _) = map W (l.comp g) (λ x hx, hl (hy hx)) :=
ring_hom.ext $ λ x, @submonoid.localization_map.map_map _ _ _ _ _ P _ (to_localization_map M S) g _
_ _ _ _ _ _ _ _ _ (to_localization_map U W) l _ x

/-- If `comm_ring` homs `g : R →+* P, l : P →+* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
lemma map_map {A : Type*} [comm_ring A] {U : submonoid A} {W} [comm_ring W]
  [algebra A W] [is_localization U W] {l : P →+* A} (hl : T ≤ U.comap l) (x : S) :
  map W l hl (map Q g hy x) = map W (l.comp g) (λ x hx, hl (hy hx)) x :=
by rw ←map_comp_map hy hl; refl

section

variables (S Q)

/-- If `S`, `Q` are localizations of `R` and `P` at submonoids `M, T` respectively, an
isomorphism `j : R ≃+* P` such that `j(M) = T` induces an isomorphism of localizations
`S ≃+* Q`. -/
@[simps]
noncomputable def ring_equiv_of_ring_equiv (h : R ≃+* P) (H : M.map h.to_monoid_hom = T) :
  S ≃+* Q :=
have H' : T.map h.symm.to_monoid_hom = M,
by { rw [← M.map_id, ← H, submonoid.map_map], congr, ext, apply h.symm_apply_apply },
{ to_fun := map Q (h : R →+* P) (M.le_comap_of_map_le (le_of_eq H)),
  inv_fun := map S (h.symm : P →+* R) (T.le_comap_of_map_le (le_of_eq H')),
  left_inv := λ x, by { rw [map_map, map_unique _ (ring_hom.id _), ring_hom.id_apply],
                        intro x, convert congr_arg (algebra_map R S) (h.symm_apply_apply x).symm },
  right_inv := λ x, by { rw [map_map, map_unique _ (ring_hom.id _), ring_hom.id_apply],
                         intro x, convert congr_arg (algebra_map P Q) (h.apply_symm_apply x).symm },
  .. map Q (h : R →+* P) _ }

end

lemma ring_equiv_of_ring_equiv_eq_map {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) :
  (ring_equiv_of_ring_equiv S Q j H : S →+* Q) =
    map Q (j : R →+* P) (M.le_comap_of_map_le (le_of_eq H)) := rfl

@[simp] lemma ring_equiv_of_ring_equiv_eq {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x) :
  ring_equiv_of_ring_equiv S Q j H ((algebra_map R S) x) = algebra_map P Q (j x) :=
map_eq _ _

lemma ring_equiv_of_ring_equiv_mk' {j : R ≃+* P} (H : M.map j.to_monoid_hom = T) (x : R) (y : M) :
  ring_equiv_of_ring_equiv S Q j H (mk' S x y) =
    mk' Q (j x) ⟨j y, show j y ∈ T, from H ▸ set.mem_image_of_mem j y.2⟩ :=
map_mk' _ _ _

end map

section alg_equiv

variables {Q : Type*} [comm_ring Q] [algebra R Q] [is_localization M Q]

section

variables (M S Q)

/-- If `S`, `Q` are localizations of `R` at the submonoid `M` respectively,
there is an isomorphism of localizations `S ≃ₐ[R] Q`. -/
@[simps]
noncomputable def alg_equiv : S ≃ₐ[R] Q :=
{ commutes' := ring_equiv_of_ring_equiv_eq _,
  .. ring_equiv_of_ring_equiv S Q (ring_equiv.refl R) M.map_id }

end

@[simp]
lemma alg_equiv_mk' (x : R) (y : M) : alg_equiv M S Q (mk' S x y) = mk' Q x y:=
map_mk' _ _ _

@[simp]
lemma alg_equiv_symm_mk' (x : R) (y : M) : (alg_equiv M S Q).symm (mk' Q x y) = mk' S x y:=
map_mk' _ _ _

end alg_equiv

end is_localization

section

variables (M)

lemma is_localization_of_alg_equiv [algebra R P] [is_localization M S] (h : S ≃ₐ[R] P) :
  is_localization M P :=
begin
  constructor,
  { intro y,
    convert (is_localization.map_units S y).map h.to_alg_hom.to_ring_hom.to_monoid_hom,
    exact (h.commutes y).symm },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj M (h.symm y),
    apply_fun h at e,
    simp only [h.map_mul, h.apply_symm_apply, h.commutes] at e,
    exact ⟨⟨x, s⟩, e⟩ },
  { intros x y,
    rw [← h.symm.to_equiv.injective.eq_iff, ← is_localization.eq_iff_exists M S,
      ← h.symm.commutes, ← h.symm.commutes],
    refl }
end

lemma is_localization_iff_of_alg_equiv [algebra R P] (h : S ≃ₐ[R] P) :
  is_localization M S ↔ is_localization M P :=
⟨λ _, by exactI is_localization_of_alg_equiv M h,
  λ _, by exactI is_localization_of_alg_equiv M h.symm⟩

lemma is_localization_iff_of_ring_equiv (h : S ≃+* P) :
  is_localization M S ↔
    @@is_localization _ M P _ (h.to_ring_hom.comp $ algebra_map R S).to_algebra :=
begin
  letI := (h.to_ring_hom.comp $ algebra_map R S).to_algebra,
  exact is_localization_iff_of_alg_equiv M { commutes' := λ _, rfl, ..h },
end

variable (S)

lemma is_localization_of_base_ring_equiv [is_localization M S] (h : R ≃+* P) :
  @@is_localization _ (M.map h.to_monoid_hom) S _
    ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  constructor,
  { rintros ⟨_, ⟨y, hy, rfl⟩⟩,
    convert is_localization.map_units S ⟨y, hy⟩,
    dsimp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply],
    exact congr_arg _ (h.symm_apply_apply _) },
  { intro y,
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj M y,
    refine ⟨⟨h x, _, _, s.prop, rfl⟩, _⟩,
    dsimp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply] at ⊢ e,
    convert e; exact h.symm_apply_apply _ },
  { intros x y,
    rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_apply, ring_hom.comp_apply,
      is_localization.eq_iff_exists M S],
    simp_rw ← h.to_equiv.apply_eq_iff_eq,
    change (∃ (c : M), h (h.symm x * c) = h (h.symm y * c)) ↔ _,
    simp only [ring_equiv.apply_symm_apply, ring_equiv.map_mul],
    exact ⟨λ ⟨c, e⟩, ⟨⟨_, _, c.prop, rfl⟩, e⟩, λ ⟨⟨_, c, h, e₁⟩, e₂⟩, ⟨⟨_, h⟩, e₁.symm ▸ e₂⟩⟩ }
end

lemma is_localization_iff_of_base_ring_equiv (h : R ≃+* P) :
  is_localization M S ↔ @@is_localization _ (M.map h.to_monoid_hom) S _
    ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  refine ⟨λ _, by exactI is_localization_of_base_ring_equiv _ _ h, _⟩,
  letI := ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra,
  intro H,
  convert @@is_localization_of_base_ring_equiv _ _ _ _ _ _ H h.symm,
  { erw [submonoid.map_equiv_eq_comap_symm, submonoid.comap_map_eq_of_injective],
    exact h.to_equiv.injective },
  rw [ring_hom.algebra_map_to_algebra, ring_hom.comp_assoc],
  simp only [ring_hom.comp_id, ring_equiv.symm_symm, ring_equiv.symm_to_ring_hom_comp_to_ring_hom],
  apply algebra.algebra_ext,
  intro r,
  rw ring_hom.algebra_map_to_algebra
end

end

section away

variables (x : R)

/-- Given `x : R`, the typeclass `is_localization.away x S` states that `S` is
isomorphic to the localization of `R` at the submonoid generated by `x`. -/
abbreviation away (S : Type*) [comm_ring S] [algebra R S] :=
is_localization (submonoid.powers x) S

namespace away

variables [is_localization.away x S]

/-- Given `x : R` and a localization map `F : R →+* S` away from `x`, `inv_self` is `(F x)⁻¹`. -/
noncomputable def inv_self : S :=
mk' S (1 : R) ⟨x, submonoid.mem_powers _⟩

variables {g : R →+* P}

/-- Given `x : R`, a localization map `F : R →+* S` away from `x`, and a map of `comm_ring`s
`g : R →+* P` such that `g x` is invertible, the homomorphism induced from `S` to `P` sending
`z : S` to `g y * (g x)⁻ⁿ`, where `y : R, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def lift (hg : is_unit (g x)) : S →+* P :=
is_localization.lift $ λ (y : submonoid.powers x), show is_unit (g y.1),
begin
  obtain ⟨n, hn⟩ := y.2,
  rw [←hn, g.map_pow],
  exact is_unit.map (pow_monoid_hom n) hg,
end

@[simp] lemma away_map.lift_eq (hg : is_unit (g x)) (a : R) :
  lift x hg ((algebra_map R S) a) = g a := lift_eq _ _

@[simp] lemma away_map.lift_comp (hg : is_unit (g x)) :
  (lift x hg).comp (algebra_map R S) = g := lift_comp _

/-- Given `x y : R` and localizations `S`, `P` away from `x` and `x * y`
respectively, the homomorphism induced from `S` to `P`. -/
noncomputable def away_to_away_right (y : R) [algebra R P] [is_localization.away (x * y) P] :
  S →+* P :=
lift x $ show is_unit ((algebra_map R P) x), from
is_unit_of_mul_eq_one ((algebra_map R P) x) (mk' P y ⟨x * y, submonoid.mem_powers _⟩) $
by rw [mul_mk'_eq_mk'_of_mul, mk'_self]

variables (S) (Q : Type*) [comm_ring Q] [algebra P Q]

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable
def map (f : R →+* P) (r : R) [is_localization.away r S]
  [is_localization.away (f r) Q] : S →+* Q :=
is_localization.map Q f
  (show submonoid.powers r ≤ (submonoid.powers (f r)).comap f,
    by { rintros x ⟨n, rfl⟩, use n, simp })

end away

end away

section inv_submonoid

variables (M S)

/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def inv_submonoid : submonoid S := (M.map (algebra_map R S : R →* S)).left_inv

variable [is_localization M S]

lemma submonoid_map_le_is_unit : M.map (algebra_map R S : R →* S) ≤ is_unit.submonoid S :=
by { rintros _ ⟨a, ha, rfl⟩, exact is_localization.map_units S ⟨_, ha⟩ }

/-- There is an equivalence of monoids between the image of `M` and `inv_submonoid`. -/
noncomputable
abbreviation equiv_inv_submonoid : M.map (algebra_map R S : R →* S) ≃* inv_submonoid M S :=
((M.map (algebra_map R S : R →* S)).left_inv_equiv (submonoid_map_le_is_unit M S)).symm

/-- There is a canonical map from `M` to `inv_submonoid` sending `x` to `1 / x`. -/
noncomputable
def to_inv_submonoid : M →* inv_submonoid M S :=
(equiv_inv_submonoid M S).to_monoid_hom.comp ((algebra_map R S : R →* S).submonoid_map M)

lemma to_inv_submonoid_surjective : function.surjective (to_inv_submonoid M S) :=
function.surjective.comp (equiv.surjective _) (monoid_hom.submonoid_map_surjective _ _)

@[simp]
lemma to_inv_submonoid_mul (m : M) : (to_inv_submonoid M S m : S) * (algebra_map R S m) = 1 :=
submonoid.left_inv_equiv_symm_mul _ _ _

@[simp]
lemma mul_to_inv_submonoid (m : M) : (algebra_map R S m) * (to_inv_submonoid M S m : S) = 1 :=
submonoid.mul_left_inv_equiv_symm _ _ ⟨_, _⟩

@[simp]
lemma smul_to_inv_submonoid (m : M) : m • (to_inv_submonoid M S m : S) = 1 :=
by { convert mul_to_inv_submonoid M S m, rw ← algebra.smul_def, refl }

variables {S}

lemma surj' (z : S) : ∃ (r : R) (m : M), z = r • to_inv_submonoid M S m :=
begin
  rcases is_localization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebra_map R S r⟩,
  refine ⟨r, m, _⟩,
  rw [algebra.smul_def, ← e, mul_assoc],
  simp,
end

lemma to_inv_submonoid_eq_mk' (x : M) :
  (to_inv_submonoid M S x : S) = mk' S 1 x :=
by { rw ← (is_localization.map_units S x).mul_left_inj, simp }

lemma mem_inv_submonoid_iff_exists_mk' (x : S) :
  x ∈ inv_submonoid M S ↔ ∃ m : M, mk' S 1 m = x :=
begin
  simp_rw ← to_inv_submonoid_eq_mk',
  exact ⟨λ h, ⟨_, congr_arg subtype.val (to_inv_submonoid_surjective M S ⟨x, h⟩).some_spec⟩,
    λ h, h.some_spec ▸ (to_inv_submonoid M S h.some).prop⟩
end

variables (S)

lemma span_inv_submonoid : submodule.span R (inv_submonoid M S : set S) = ⊤ :=
begin
  rw eq_top_iff,
  rintros x -,
  rcases is_localization.surj' M x with ⟨r, m, rfl⟩,
  exact submodule.smul_mem _ _ (submodule.subset_span (to_inv_submonoid M S m).prop),
end

lemma finite_type_of_monoid_fg [monoid.fg M] : algebra.finite_type R S :=
begin
  have := monoid.fg_of_surjective _ (to_inv_submonoid_surjective M S),
  rw monoid.fg_iff_submonoid_fg at this,
  rcases this with ⟨s, hs⟩,
  refine ⟨⟨s, _⟩⟩,
  rw eq_top_iff,
  rintro x -,
  change x ∈ ((algebra.adjoin R _ : subalgebra R S).to_submodule : set S),
  rw [algebra.adjoin_eq_span, hs, span_inv_submonoid],
  trivial
end

end inv_submonoid

variables (M S)

include M

lemma non_zero_divisors_le_comap [is_localization M S] :
    non_zero_divisors R ≤ (non_zero_divisors S).comap (algebra_map R S)  :=
begin
  rintros a ha b (e : b * algebra_map R S a = 0),
  obtain ⟨x, s, rfl⟩ := mk'_surjective M b,
  rw [← @mk'_one R _ M, ← mk'_mul, ← (algebra_map R S).map_zero, ← @mk'_one R _ M,
    is_localization.eq] at e,
  obtain ⟨c, e⟩ := e,
  rw [zero_mul, zero_mul, submonoid.coe_one, mul_one, mul_comm x a, mul_assoc, mul_comm] at e,
  rw mk'_eq_zero_iff,
  exact ⟨c, ha _ e⟩
end

lemma map_non_zero_divisors_le [is_localization M S] :
    (non_zero_divisors R).map (algebra_map R S).to_monoid_hom ≤ non_zero_divisors S  :=
submonoid.map_le_iff_le_comap.mpr (non_zero_divisors_le_comap M S)

end is_localization

namespace localization

open is_localization

/-! ### Constructing a localization at a given submonoid -/

variables {M}

section

instance [subsingleton R] : subsingleton (localization M) :=
⟨λ a b, by { induction a, induction b, congr, refl, refl }⟩

/-- Addition in a ring localization is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨b * c + d * a, b * d⟩`.

Should not be confused with `add_localization.add`, which is defined as
`⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.
-/
@[irreducible] protected def add (z w : localization M) : localization M :=
localization.lift_on₂ z w
  (λ a b c d, mk ((b : R) * c + d * a) (b * d)) $
λ a a' b b' c c' d d' h1 h2, mk_eq_mk_iff.2
begin
  rw r_eq_r' at h1 h2 ⊢,
  cases h1 with t₅ ht₅,
  cases h2 with t₆ ht₆,
  use t₆ * t₅,
  calc ((b : R) * c + d * a) * (b' * d') * (t₆ * t₅) =
      (c * d' * t₆) * (b * b' * t₅) + (a * b' * t₅) * (d * d' * t₆) : by ring
      ... = (b' * c' + d' * a') * (b * d) * (t₆ * t₅) : by rw [ht₆, ht₅]; ring
end

instance : has_add (localization M) := ⟨localization.add⟩

lemma add_mk (a b c d) : (mk a b : localization M) + mk c d = mk (b * c + d * a) (b * d) :=
by { unfold has_add.add localization.add, apply lift_on₂_mk }

lemma add_mk_self (a b c) : (mk a b : localization M) + mk c b = mk (a + c) b :=
begin
  rw [add_mk, mk_eq_mk_iff, r_eq_r'],
  refine (r' M).symm ⟨1, _⟩,
  simp only [submonoid.coe_one, submonoid.coe_mul],
  ring
end

/-- Negation in a ring localization is defined as `-⟨a, b⟩ = ⟨-a, b⟩`. -/
@[irreducible] protected def neg (z : localization M) : localization M :=
localization.lift_on z (λ a b, mk (-a) b) $
  λ a b c d h, mk_eq_mk_iff.2
begin
  rw r_eq_r' at h ⊢,
  cases h with t ht,
  use t,
  rw [neg_mul, neg_mul, ht],
  ring_nf,
end

instance : has_neg (localization M) := ⟨localization.neg⟩

lemma neg_mk (a b) : -(mk a b : localization M) = mk (-a) b :=
by { unfold has_neg.neg localization.neg, apply lift_on_mk }

/-- The zero element in a ring localization is defined as `⟨0, 1⟩`.

Should not be confused with `add_localization.zero` which is `⟨0, 0⟩`. -/
@[irreducible] protected def zero : localization M :=
mk 0 1

instance : has_zero (localization M) := ⟨localization.zero⟩

lemma mk_zero (b) : (mk 0 b : localization M) = 0 :=
calc mk 0 b = mk 0 1 : mk_eq_mk_iff.mpr (r_of_eq (by simp))
... = 0 : by  unfold has_zero.zero localization.zero

lemma lift_on_zero {p : Type*} (f : ∀ (a : R) (b : M), p) (H) : lift_on 0 f H = f 0 1 :=
by rw [← mk_zero 1, lift_on_mk]

private meta def tac := `[
{ intros,
  simp only [add_mk, localization.mk_mul, neg_mk, ← mk_zero 1],
  refine mk_eq_mk_iff.mpr (r_of_eq _),
  simp only [submonoid.coe_mul, prod.fst_mul, prod.snd_mul],
  ring }]

instance : comm_ring (localization M) :=
{ zero := 0,
  one  := 1,
  add  := (+),
  mul  := (*),
  npow := localization.npow _,
  nsmul := (•),
  nsmul_zero' := λ x, localization.induction_on x
    (λ x, by simp only [smul_mk, zero_nsmul, mk_zero]),
  nsmul_succ' := λ n x, localization.induction_on x
    (λ x, by simp only [smul_mk, succ_nsmul, add_mk_self]),
  zsmul := (•),
  zsmul_zero' := λ x, localization.induction_on x
    (λ x, by simp only [smul_mk, zero_zsmul, mk_zero]),
  zsmul_succ' := λ n x, localization.induction_on x
    (λ x, by simp [smul_mk, add_mk_self, -mk_eq_monoid_of_mk', add_comm (n : ℤ) 1, add_smul]),
  zsmul_neg' := λ n x, localization.induction_on x
    (λ x, by { rw [smul_mk, smul_mk, neg_mk, ← neg_smul], refl }),
  add_assoc      := λ m n k, localization.induction_on₃ m n k (by tac),
  zero_add       := λ y, localization.induction_on y (by tac),
  add_zero       := λ y, localization.induction_on y (by tac),
  neg            := has_neg.neg,
  sub            := λ x y, x + -y,
  sub_eq_add_neg := λ x y, rfl,
  add_left_neg   := λ y, by exact localization.induction_on y (by tac),
  add_comm       := λ y z, localization.induction_on₂ z y (by tac),
  left_distrib   := λ m n k, localization.induction_on₃ m n k (by tac),
  right_distrib  := λ m n k, localization.induction_on₃ m n k (by tac),
   ..localization.comm_monoid M }

instance {S : Type*} [monoid S] [distrib_mul_action S R] [is_scalar_tower S R R] :
  distrib_mul_action S (localization M) :=
{ smul_zero := λ s, by simp only [←localization.mk_zero 1, localization.smul_mk, smul_zero],
  smul_add := λ s x y, localization.induction_on₂ x y $
    prod.rec $ by exact λ r₁ x₁, prod.rec $ by exact λ r₂ x₂,
      by simp only [localization.smul_mk, localization.add_mk, smul_add, mul_comm _ (s • _),
                    mul_comm _ r₁, mul_comm _ r₂, smul_mul_assoc] }

instance {S : Type*} [semiring S] [mul_semiring_action S R] [is_scalar_tower S R R] :
  mul_semiring_action S (localization M) :=
{ ..localization.mul_distrib_mul_action }

instance {S : Type*} [semiring S] [module S R] [is_scalar_tower S R R] :
  module S (localization M) :=
{ zero_smul := localization.ind $ prod.rec $
    by { intros, simp only [localization.smul_mk, zero_smul, mk_zero] },
  add_smul := λ s₁ s₂, localization.ind $ prod.rec $
    by { intros, simp only [localization.smul_mk, add_smul, add_mk_self] },
  ..localization.distrib_mul_action }

instance {S : Type*} [comm_semiring S] [algebra S R] : algebra S (localization M) :=
{ to_ring_hom :=
  ring_hom.comp
  { to_fun := (monoid_of M).to_map,
    map_zero' := by rw [← mk_zero (1 : M), mk_one_eq_monoid_of_mk],
    map_add' := λ x y,
      by simp only [← mk_one_eq_monoid_of_mk, add_mk, submonoid.coe_one, one_mul, add_comm],
    .. localization.monoid_of M } (algebra_map S R),
  smul_def' := λ s, localization.ind $ prod.rec $ begin
    intros r x,
    dsimp,
    simp only [←mk_one_eq_monoid_of_mk, mk_mul, localization.smul_mk, one_mul, algebra.smul_def],
  end,
  commutes' := λ s, localization.ind $ prod.rec $ begin
    intros r x,
    dsimp,
    simp only [←mk_one_eq_monoid_of_mk, mk_mul, localization.smul_mk, one_mul, mul_one,
               algebra.commutes],
  end }

instance : is_localization M (localization M) :=
{ map_units := (localization.monoid_of M).map_units,
  surj := (localization.monoid_of M).surj,
  eq_iff_exists := λ _ _, (localization.monoid_of M).eq_iff_exists }

end

@[simp] lemma to_localization_map_eq_monoid_of :
  to_localization_map M (localization M) = monoid_of M := rfl

lemma monoid_of_eq_algebra_map (x) :
  (monoid_of M).to_map x = algebra_map R (localization M) x :=
rfl

lemma mk_one_eq_algebra_map (x) : mk x 1 = algebra_map R (localization M) x := rfl

lemma mk_eq_mk'_apply (x y) : mk x y = is_localization.mk' (localization M) x y :=
by rw [mk_eq_monoid_of_mk'_apply, mk', to_localization_map_eq_monoid_of]

@[simp] lemma mk_eq_mk' : (mk : R → M → localization M) = is_localization.mk' (localization M) :=
mk_eq_monoid_of_mk'

variables [is_localization M S]

section

variables (M S)

/-- The localization of `R` at `M` as a quotient type is isomorphic to any other localization. -/
@[simps]
noncomputable def alg_equiv : localization M ≃ₐ[R] S :=
is_localization.alg_equiv M _ _

end

@[simp] lemma alg_equiv_mk' (x : R) (y : M) :
  alg_equiv M S (mk' (localization M) x y) = mk' S x y :=
alg_equiv_mk' _ _

@[simp] lemma alg_equiv_symm_mk' (x : R) (y : M) :
  (alg_equiv M S).symm (mk' S x y) = mk' (localization M) x y :=
alg_equiv_symm_mk' _ _

lemma alg_equiv_mk (x y) :
  alg_equiv M S (mk x y) = mk' S x y :=
by rw [mk_eq_mk', alg_equiv_mk']

lemma alg_equiv_symm_mk (x : R) (y : M) :
  (alg_equiv M S).symm (mk' S x y) = mk x y :=
by rw [mk_eq_mk', alg_equiv_symm_mk']

/-- Given a map `f : R →+* S` and an element `r : R`, such that `f r` is invertible,
  we may construct a map `Rᵣ →+* S`. -/
noncomputable
abbreviation away_lift (f : R →+* P) (r : R) (hr : is_unit (f r)) :
  localization.away r →+* P :=
is_localization.away.lift r hr

/-- Given a map `f : R →+* S` and an element `r : R`, we may construct a map `Rᵣ →+* Sᵣ`. -/
noncomputable
abbreviation away_map (f : R →+* P) (r : R) :
  localization.away r →+* localization.away (f r) :=
is_localization.away.map _ _ f r

end localization

variables {M}

section at_prime

variables (I : ideal R) [hp : I.is_prime]
include hp
namespace ideal

/-- The complement of a prime ideal `I ⊆ R` is a submonoid of `R`. -/
def prime_compl :
  submonoid R :=
{ carrier := (Iᶜ : set R),
  one_mem' := by convert I.ne_top_iff_one.1 hp.1; refl,
  mul_mem' := λ x y hnx hny hxy, or.cases_on (hp.mem_or_mem hxy) hnx hny }

end ideal

variables (S)

/-- Given a prime ideal `P`, the typeclass `is_localization.at_prime S P` states that `S` is
isomorphic to the localization of `R` at the complement of `P`. -/
protected abbreviation is_localization.at_prime := is_localization I.prime_compl S

/-- Given a prime ideal `P`, `localization.at_prime S P` is a localization of
`R` at the complement of `P`, as a quotient type. -/
protected abbreviation localization.at_prime := localization I.prime_compl

namespace is_localization

theorem at_prime.local_ring [is_localization.at_prime S I] : local_ring S :=
local_of_nonunits_ideal
  (λ hze, begin
      rw [←(algebra_map R S).map_one, ←(algebra_map R S).map_zero] at hze,
      obtain ⟨t, ht⟩ := (eq_iff_exists I.prime_compl S).1 hze,
      exact ((show (t : R) ∉ I, from t.2) (have htz : (t : R) = 0, by simpa using ht.symm,
        htz.symm ▸ I.zero_mem))
    end)
  (begin
    intros x hx y hy hu,
    cases is_unit_iff_exists_inv.1 hu with z hxyz,
    have : ∀ {r : R} {s : I.prime_compl}, mk' S r s ∈ nonunits S → r ∈ I, from
      λ (r : R) (s : I.prime_compl), not_imp_comm.1
        (λ nr, is_unit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : I.prime_compl),
          mk'_mul_mk'_eq_one' _ _ nr⟩),
    rcases mk'_surjective I.prime_compl x with ⟨rx, sx, hrx⟩,
    rcases mk'_surjective I.prime_compl y with ⟨ry, sy, hry⟩,
    rcases mk'_surjective I.prime_compl z with ⟨rz, sz, hrz⟩,
    rw [←hrx, ←hry, ←hrz, ←mk'_add, ←mk'_mul,
        ←mk'_self S I.prime_compl.one_mem] at hxyz,
    rw ←hrx at hx, rw ←hry at hy,
    obtain ⟨t, ht⟩ := is_localization.eq.1 hxyz,
    simp only [mul_one, one_mul, submonoid.coe_mul, subtype.coe_mk] at ht,
    rw [←sub_eq_zero, ←sub_mul] at ht,
    have hr := (hp.mem_or_mem_of_mul_eq_zero ht).resolve_right t.2,
    rw sub_eq_add_neg at hr,
    have := I.neg_mem_iff.1 ((ideal.add_mem_iff_right _ _).1 hr),
    { exact not_or (mt hp.mem_or_mem (not_or sx.2 sy.2)) sz.2 (hp.mem_or_mem this)},
    { exact I.mul_mem_right _ (I.add_mem (I.mul_mem_right _ (this hx))
                                         (I.mul_mem_right _ (this hy)))}
  end)

end is_localization

namespace localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
instance at_prime.local_ring : local_ring (localization I.prime_compl) :=
is_localization.at_prime.local_ring (localization I.prime_compl) I

end localization

end at_prime

namespace is_localization
variables [is_localization M S]

section ideals

variables (M) (S)
include M

/-- Explicit characterization of the ideal given by `ideal.map (algebra_map R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_to_map_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
private def map_ideal (I : ideal R) : ideal S :=
{ carrier := { z : S | ∃ x : I × M, z * algebra_map R S x.2 = algebra_map R S x.1},
  zero_mem' := ⟨⟨0, 1⟩, by simp⟩,
  add_mem' := begin
    rintros a b ⟨a', ha⟩ ⟨b', hb⟩,
    use ⟨a'.2 * b'.1 + b'.2 * a'.1, I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩,
    use a'.2 * b'.2,
    simp only [ring_hom.map_add, submodule.coe_mk, submonoid.coe_mul, ring_hom.map_mul],
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebra_map R S a'.2) (algebra_map R S b'.2),
        ← mul_assoc b, hb],
    ring
  end,
  smul_mem' := begin
    rintros c x ⟨x', hx⟩,
    obtain ⟨c', hc⟩ := is_localization.surj M c,
    use ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩,
    use c'.2 * x'.2,
    simp only [←hx, ←hc, smul_eq_mul, submodule.coe_mk, submonoid.coe_mul, ring_hom.map_mul],
    ring
  end }

theorem mem_map_algebra_map_iff {I : ideal R} {z} :
  z ∈ ideal.map (algebra_map R S) I ↔ ∃ x : I × M, z * algebra_map R S x.2 = algebra_map R S x.1 :=
begin
  split,
  { change _ → z ∈ map_ideal M S I,
    refine λ h, ideal.mem_Inf.1 h (λ z hz, _),
    obtain ⟨y, hy⟩ := hz,
    use ⟨⟨⟨y, hy.left⟩, 1⟩, by simp [hy.right]⟩ },
  { rintros ⟨⟨a, s⟩, h⟩,
    rw [← ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm],
    exact h.symm ▸ ideal.mem_map_of_mem _ a.2 }
end

theorem map_comap (J : ideal S) :
  ideal.map (algebra_map R S) (ideal.comap (algebra_map R S) J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 le_rfl) $ λ x hJ,
begin
  obtain ⟨r, s, hx⟩ := mk'_surjective M x,
  rw ←hx at ⊢ hJ,
  exact ideal.mul_mem_right _ _ (ideal.mem_map_of_mem _ (show (algebra_map R S) r ∈ J, from
    mk'_spec S r s ▸ J.mul_mem_right ((algebra_map R S) s) hJ)),
end

theorem comap_map_of_is_prime_disjoint (I : ideal R) (hI : I.is_prime)
  (hM : disjoint (M : set R) I) :
  ideal.comap (algebra_map R S) (ideal.map (algebra_map R S) I) = I :=
begin
  refine le_antisymm (λ a ha, _) ideal.le_comap_map,
  rw [ideal.mem_comap, mem_map_algebra_map_iff M S] at ha,
  obtain ⟨⟨b, s⟩, h⟩ := ha,
  have : (algebra_map R S) (a * ↑s - b) = 0 := by simpa [sub_eq_zero] using h,
  rw [← (algebra_map R S).map_zero, eq_iff_exists M S] at this,
  obtain ⟨c, hc⟩ := this,
  have : a * s ∈ I,
  { rw zero_mul at hc,
    let this : (a * ↑s - ↑b) * ↑c ∈ I := hc.symm ▸ I.zero_mem,
    cases hI.mem_or_mem this with h1 h2,
    { simpa using I.add_mem h1 b.2 },
    { exfalso,
      refine hM ⟨c.2, h2⟩ } },
  cases hI.mem_or_mem this with h1 h2,
  { exact h1 },
  { exfalso,
    refine hM ⟨s.2, h2⟩ }
end

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def order_embedding : ideal S ↪o ideal R :=
{ to_fun := λ J, ideal.comap (algebra_map R S) J,
  inj'   := function.left_inverse.injective (map_comap M S),
  map_rel_iff'   := λ J₁ J₂, ⟨λ hJ, (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ ideal.map_mono hJ,
    ideal.comap_mono⟩ }

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
lemma is_prime_iff_is_prime_disjoint (J : ideal S) :
  J.is_prime ↔ (ideal.comap (algebra_map R S) J).is_prime ∧
    disjoint (M : set R) ↑(ideal.comap (algebra_map R S) J) :=
begin
  split,
  { refine λ h, ⟨⟨_, _⟩, λ m hm,
      h.ne_top (ideal.eq_top_of_is_unit_mem _ hm.2 (map_units S ⟨m, hm.left⟩))⟩,
    { refine λ hJ, h.ne_top _,
      rw [eq_top_iff, ← (order_embedding M S).le_iff_le],
      exact le_of_eq hJ.symm },
    { intros x y hxy,
      rw [ideal.mem_comap, ring_hom.map_mul] at hxy,
      exact h.mem_or_mem hxy } },
  { refine λ h, ⟨λ hJ, h.left.ne_top (eq_top_iff.2 _), _⟩,
    { rwa [eq_top_iff, ← (order_embedding M S).le_iff_le] at hJ },
    { intros x y hxy,
      obtain ⟨a, s, ha⟩ := mk'_surjective M x,
      obtain ⟨b, t, hb⟩ := mk'_surjective M y,
      have : mk' S (a * b) (s * t) ∈ J := by rwa [mk'_mul, ha, hb],
      rw [mk'_mem_iff, ← ideal.mem_comap] at this,
      replace this := h.left.mem_or_mem this,
      rw [ideal.mem_comap, ideal.mem_comap] at this,
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff] } }
end

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
lemma is_prime_of_is_prime_disjoint (I : ideal R) (hp : I.is_prime)
  (hd : disjoint (M : set R) ↑I) : (ideal.map (algebra_map R S) I).is_prime :=
begin
  rw [is_prime_iff_is_prime_disjoint M S, comap_map_of_is_prime_disjoint M S I hp hd],
  exact ⟨hp, hd⟩
end

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
def order_iso_of_prime :
  {p : ideal S // p.is_prime} ≃o {p : ideal R // p.is_prime ∧ disjoint (M : set R) ↑p} :=
{ to_fun := λ p, ⟨ideal.comap (algebra_map R S) p.1,
                  (is_prime_iff_is_prime_disjoint M S p.1).1 p.2⟩,
  inv_fun := λ p, ⟨ideal.map (algebra_map R S) p.1,
                   is_prime_of_is_prime_disjoint M S p.1 p.2.1 p.2.2⟩,
  left_inv := λ J, subtype.eq (map_comap M S J),
  right_inv := λ I, subtype.eq (comap_map_of_is_prime_disjoint M S I.1 I.2.1 I.2.2),
  map_rel_iff' := λ I I', ⟨λ h, (show I.val ≤ I'.val,
    from (map_comap M S I.val) ▸ (map_comap M S I'.val) ▸ (ideal.map_mono h)), λ h x hx, h hx⟩ }

/-- `quotient_map` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
lemma surjective_quotient_map_of_maximal_of_localization {I : ideal S} [I.is_prime] {J : ideal R}
  {H : J ≤ I.comap (algebra_map R S)} (hI : (I.comap (algebra_map R S)).is_maximal) :
  function.surjective (I.quotient_map (algebra_map R S) H) :=
begin
  intro s,
  obtain ⟨s, rfl⟩ := ideal.quotient.mk_surjective s,
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M s,
  by_cases hM : (ideal.quotient.mk (I.comap (algebra_map R S))) m = 0,
  { have : I = ⊤,
    { rw ideal.eq_top_iff_one,
      rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_comap] at hM,
      convert I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM,
      rw [← mk'_eq_mul_mk'_one, mk'_self] },
    exact ⟨0, eq_comm.1 (by simp [ideal.quotient.eq_zero_iff_mem, this])⟩ },
  { rw ideal.quotient.maximal_ideal_iff_is_field_quotient at hI,
    obtain ⟨n, hn⟩ := hI.3 hM,
    obtain ⟨rn, rfl⟩ := ideal.quotient.mk_surjective n,
    refine ⟨(ideal.quotient.mk J) (r * rn), _⟩,
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    rw ← ring_hom.map_mul at hn,
    replace hn := congr_arg (ideal.quotient_map I (algebra_map R S) le_rfl) hn,
    simp only [ring_hom.map_one, ideal.quotient_map_mk, ring_hom.map_mul] at hn,
    rw [ideal.quotient_map_mk, ← sub_eq_zero, ← ring_hom.map_sub,
      ideal.quotient.eq_zero_iff_mem, ← ideal.quotient.eq_zero_iff_mem, ring_hom.map_sub,
      sub_eq_zero, mk'_eq_mul_mk'_one],
    simp only [mul_eq_mul_left_iff, ring_hom.map_mul],
    exact or.inl (mul_left_cancel₀ (λ hn, hM (ideal.quotient.eq_zero_iff_mem.2
      (ideal.mem_comap.2 (ideal.quotient.eq_zero_iff_mem.1 hn)))) (trans hn
      (by rw [← ring_hom.map_mul, ← mk'_eq_mul_mk'_one, mk'_self, ring_hom.map_one]))) }
end

end ideals

section at_units
variables (R) (S) (M)

/-- The localization at a module of units is isomorphic to the ring -/
noncomputable
def at_units (H : ∀ x : M, is_unit (x : R)) : R ≃ₐ[R] S :=
begin
  refine alg_equiv.of_bijective (algebra.of_id R S) ⟨_, _⟩,
  { intros x y hxy,
    obtain ⟨c, eq⟩ := (is_localization.eq_iff_exists M S).mp hxy,
    obtain ⟨u, hu⟩ := H c,
    rwa [← hu, units.mul_left_inj] at eq },
  { intros y,
    obtain ⟨⟨x, s⟩, eq⟩ := is_localization.surj M y,
    obtain ⟨u, hu⟩ := H s,
    use x * u.inv,
    dsimp only [algebra.of_id, ring_hom.to_fun_eq_coe, alg_hom.coe_mk],
    rw [ring_hom.map_mul, ← eq, ← hu, mul_assoc, ← ring_hom.map_mul],
    simp }
end

/-- The localization away from a unit is isomorphic to the ring -/
noncomputable
def at_unit (x : R) (e : is_unit x) [is_localization.away x S] : R ≃ₐ[R] S :=
begin
  apply at_units R (submonoid.powers x),
  rintros ⟨xn, n, hxn⟩,
  obtain ⟨u, hu⟩ := e,
  rw is_unit_iff_exists_inv,
  use u.inv ^ n,
  simp[← hxn, ← hu, ← mul_pow]
end

/-- The localization at one is isomorphic to the ring. -/
noncomputable
def at_one [is_localization.away (1 : R) S] : R ≃ₐ[R] S :=
@at_unit R _ S _ _ (1 : R) is_unit_one _

end at_units

section localization_localization

variable (M)

variables (N : submonoid S) (T : Type*) [comm_ring T] [algebra R T]

section

variables [algebra S T] [is_scalar_tower R S T]

/--
Localizing wrt `M ⊆ R` and then wrt `N ⊆ S = M⁻¹R` is equal to the localization of `R` wrt this
module. See `localization_localization_is_localization`.
-/
-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
@[nolint unused_arguments]
def localization_localization_submodule : submonoid R :=
(N ⊔ M.map (algebra_map R S)).comap (algebra_map R S)

variables {M N}
@[simp]
lemma mem_localization_localization_submodule {x : R} :
  x ∈ localization_localization_submodule M N ↔
    ∃ (y : N) (z : M), algebra_map R S x = y * algebra_map R S z :=
begin
  rw [localization_localization_submodule, submonoid.mem_comap, submonoid.mem_sup],
  split,
  { rintros ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩, exact ⟨⟨y, hy⟩, ⟨z, hz⟩ ,e.symm⟩ },
  { rintros ⟨y, z, e⟩, exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩ }
end

variables (M N)

lemma localization_localization_map_units [is_localization N T]
  (y : localization_localization_submodule M N) : is_unit (algebra_map R T y) :=
begin
  obtain ⟨y', z, eq⟩ := mem_localization_localization_submodule.mp y.prop,
  rw [is_scalar_tower.algebra_map_apply R S T, eq, ring_hom.map_mul, is_unit.mul_iff],
  exact ⟨is_localization.map_units T y',
    (is_localization.map_units _ z).map (algebra_map S T : S →* T)⟩,
end

lemma localization_localization_surj [is_localization N T] (x : T) :
  ∃ (y : R × localization_localization_submodule M N),
    x * (algebra_map R T y.2) = algebra_map R T y.1 :=
begin
  rcases is_localization.surj N x with ⟨⟨y, s⟩, eq₁⟩, -- x = y / s
  rcases is_localization.surj M y with ⟨⟨z, t⟩, eq₂⟩, -- y = z / t
  rcases is_localization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩, -- s = z' / t'
  dsimp only at eq₁ eq₂ eq₃,
  use z * t', use z' * t, -- x = y / s = (z * t') / (z' * t)
  { rw mem_localization_localization_submodule,
    refine ⟨s, t * t', _⟩,
    rw [ring_hom.map_mul, ← eq₃, mul_assoc, ← ring_hom.map_mul, mul_comm t, submonoid.coe_mul] },
  { simp only [subtype.coe_mk, ring_hom.map_mul, is_scalar_tower.algebra_map_apply R S T,
      ← eq₃, ← eq₂, ← eq₁],
    ring },
end

lemma localization_localization_eq_iff_exists [is_localization N T] (x y : R) :
  algebra_map R T x = algebra_map R T y ↔
    ∃ (c : localization_localization_submodule M N), x * c = y * c :=
begin
  rw [is_scalar_tower.algebra_map_apply R S T, is_scalar_tower.algebra_map_apply R S T,
      is_localization.eq_iff_exists N T],
  split,
  { rintros ⟨z, eq₁⟩,
    rcases is_localization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩,
    dsimp only at eq₂,
    obtain ⟨c, eq₃ : x * z' * ↑ c = y * z' * ↑ c⟩ := (is_localization.eq_iff_exists M S).mp _,
    swap, { rw [ring_hom.map_mul, ring_hom.map_mul, ← eq₂, ← mul_assoc, ← mul_assoc, ← eq₁] },
    use z' * c,
    { rw mem_localization_localization_submodule,
      refine ⟨z, s * c, _⟩,
      rw [ring_hom.map_mul, ← eq₂, mul_assoc, ← ring_hom.map_mul, submonoid.coe_mul] },
    { simpa only [mul_assoc] using eq₃ } },
  { rintro ⟨⟨c, hc⟩, eq₁ : x * c = y * c⟩,
    rw mem_localization_localization_submodule at hc,
    rcases hc with ⟨z₁, z, eq₂⟩,
    use z₁,
    refine (is_localization.map_units S z).mul_left_inj.mp _,
    rw [mul_assoc, mul_assoc, ← eq₂, ← ring_hom.map_mul, ← ring_hom.map_mul, eq₁] }
end

/--
Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization is a localization.
-/
lemma localization_localization_is_localization [is_localization N T] :
  is_localization (localization_localization_submodule M N) T :=
{ map_units := localization_localization_map_units M N T,
  surj := localization_localization_surj M N T,
  eq_iff_exists := localization_localization_eq_iff_exists M N T }

include M

/--
Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the localization of a
localization is a localization.
-/
lemma localization_localization_is_localization_of_has_all_units
  [is_localization N T] (H : ∀ (x : S), is_unit x → x ∈ N) :
  is_localization (N.comap (algebra_map R S).to_monoid_hom) T :=
begin
  convert localization_localization_is_localization M N T,
  symmetry,
  rw sup_eq_left,
  rintros _ ⟨x, hx, rfl⟩,
  exact H _ (is_localization.map_units _ ⟨x, hx⟩),
end

/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
lemma is_localization_is_localization_at_prime_is_localization (p : ideal S) [Hp : p.is_prime]
  [is_localization.at_prime T p] :
  is_localization.at_prime T (p.comap (algebra_map R S)) :=
begin
  apply localization_localization_is_localization_of_has_all_units M p.prime_compl T,
  intros x hx hx',
  exact (Hp.1 : ¬ _) (p.eq_top_of_is_unit_mem hx' hx),
end

instance (p : ideal (localization M)) [p.is_prime] : algebra R (localization.at_prime p) :=
localization.algebra

instance (p : ideal (localization M)) [p.is_prime] :
  is_scalar_tower R (localization M) (localization.at_prime p) :=
is_scalar_tower.of_algebra_map_eq' rfl

instance localization_localization_at_prime_is_localization (p : ideal (localization M))
  [p.is_prime] : is_localization.at_prime (localization.at_prime p) (p.comap (algebra_map R _)) :=
is_localization_is_localization_at_prime_is_localization M _ _

/--
Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` the localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R` at `f⁻¹(p)`.
-/
noncomputable
def localization_localization_at_prime_iso_localization (p : ideal (localization M)) [p.is_prime] :
  localization.at_prime (p.comap (algebra_map R _)) ≃ₐ[R] localization.at_prime p :=
is_localization.alg_equiv (p.comap (algebra_map R _)).prime_compl _ _

end

variables (S)

/-- Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`. -/
noncomputable
def localization_algebra_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T] :
  algebra S T :=
(is_localization.lift (λ y, (map_units T ⟨↑y, h y.prop⟩ : _)) : S →+* T).to_algebra

/-- If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes with the
localization maps -/
lemma localization_is_scalar_tower_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T] :
  @@is_scalar_tower R S T _ (localization_algebra_of_submonoid_le S T M N h).to_has_scalar _ :=
begin
  letI := localization_algebra_of_submonoid_le S T M N h,
  exact is_scalar_tower.of_algebra_map_eq' (is_localization.lift_comp _).symm
end

noncomputable
instance (x : ideal R) [H : x.is_prime] [is_domain R] :
  algebra (localization.at_prime x) (localization (non_zero_divisors R)) :=
localization_algebra_of_submonoid_le _ _ x.prime_compl (non_zero_divisors R)
  (by { intros a ha, rw mem_non_zero_divisors_iff_ne_zero, exact λ h, ha (h.symm ▸ x.zero_mem) })

/-- If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S` at `N`. -/
lemma is_localization_of_submonoid_le
  (M N : submonoid R) (h : M ≤ N) [is_localization M S] [is_localization N T]
  [algebra S T] [is_scalar_tower R S T] :
  is_localization (N.map (algebra_map R S).to_monoid_hom) T :=
{ map_units := begin
    rintro ⟨_, ⟨y, hy, rfl⟩⟩,
    convert is_localization.map_units T ⟨y, hy⟩,
    exact (is_scalar_tower.algebra_map_apply _ _ _ _).symm
  end,
  surj := λ y, begin
    obtain ⟨⟨x, s⟩, e⟩ := is_localization.surj N y,
    refine ⟨⟨algebra_map _ _ x, _, _, s.prop, rfl⟩, _⟩,
    simpa [← is_scalar_tower.algebra_map_apply] using e
  end,
  eq_iff_exists := λ x₁ x₂, begin
    obtain ⟨⟨y₁, s₁⟩, e₁⟩ := is_localization.surj M x₁,
    obtain ⟨⟨y₂, s₂⟩, e₂⟩ := is_localization.surj M x₂,
    refine iff.trans _ (set.exists_image_iff (algebra_map R S) N (λ c, x₁ * c = x₂ * c)).symm,
    dsimp only at e₁ e₂ ⊢,
    suffices : algebra_map R T (y₁ * s₂) = algebra_map R T (y₂ * s₁) ↔
      ∃ (a : N), algebra_map R S (a * (y₁ * s₂)) = algebra_map R S (a * (y₂ * s₁)),
    { have h₁ := (is_localization.map_units T ⟨_, h s₁.prop⟩).mul_left_inj,
      have h₂ := (is_localization.map_units T ⟨_, h s₂.prop⟩).mul_left_inj,
      simp only [is_scalar_tower.algebra_map_apply R S T, subtype.coe_mk] at h₁ h₂,
      simp only [is_scalar_tower.algebra_map_apply R S T, map_mul, ← e₁, ← e₂, ← mul_assoc,
        mul_right_comm _ (algebra_map R S s₂),
        mul_right_comm _ (algebra_map S T (algebra_map R S s₂)),
        (is_localization.map_units S s₁).mul_left_inj,
        (is_localization.map_units S s₂).mul_left_inj] at this,
      rw [h₂, h₁] at this,
      simpa only [mul_comm] using this },
    simp_rw [is_localization.eq_iff_exists N T, is_localization.eq_iff_exists M S],
    split,
    { rintro ⟨a, e⟩, exact ⟨a, 1, by { convert e using 1; simp; ring }⟩ },
    { rintro ⟨a, b, e⟩, exact ⟨a * (⟨_, h b.prop⟩ : N), by { convert e using 1; simp; ring }⟩ }
  end }

/-- If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then the
localization at `N` is equal to the localizaton of `M`. -/
lemma is_localization_of_is_exists_mul_mem (M N : submonoid R) [is_localization M S] (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : is_localization N S :=
{ map_units := λ y, begin
    obtain ⟨m, hm⟩ := h' y,
    have := is_localization.map_units S ⟨_, hm⟩,
    erw map_mul at this,
    exact (is_unit.mul_iff.mp this).2
  end,
  surj := λ z, by { obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M z, exact ⟨⟨y, _, h s.prop⟩, e⟩ },
  eq_iff_exists := λ x₁ x₂, begin
    rw is_localization.eq_iff_exists M,
    refine ⟨λ ⟨x, hx⟩, ⟨⟨_, h x.prop⟩, hx⟩, _⟩,
    rintros ⟨x, h⟩,
    obtain ⟨m, hm⟩ := h' x,
    refine ⟨⟨_, hm⟩, _⟩,
    simp [mul_comm m, ← mul_assoc, h]
  end }

end localization_localization

variables (S)

/-- Map from ideals of `R` to submodules of `S` induced by `f`. -/
-- This was previously a `has_coe` instance, but if `S = R` then this will loop.
-- It could be a `has_coe_t` instance, but we keep it explicit here to avoid slowing down
-- the rest of the library.
def coe_submodule (I : ideal R) : submodule R S := submodule.map (algebra.linear_map R S) I

lemma mem_coe_submodule (I : ideal R) {x : S} :
  x ∈ coe_submodule S I ↔ ∃ y : R, y ∈ I ∧ algebra_map R S y = x :=
iff.rfl

lemma coe_submodule_mono {I J : ideal R} (h : I ≤ J) :
  coe_submodule S I ≤ coe_submodule S J :=
submodule.map_mono h

@[simp] lemma coe_submodule_bot : coe_submodule S (⊥ : ideal R) = ⊥ :=
by rw [coe_submodule, submodule.map_bot]

@[simp] lemma coe_submodule_top : coe_submodule S (⊤ : ideal R) = 1 :=
by rw [coe_submodule, submodule.map_top, submodule.one_eq_range]

@[simp] lemma coe_submodule_sup (I J : ideal R) :
  coe_submodule S (I ⊔ J) = coe_submodule S I ⊔ coe_submodule S J :=
submodule.map_sup _ _ _

@[simp] lemma coe_submodule_mul (I J : ideal R) :
  coe_submodule S (I * J) = coe_submodule S I * coe_submodule S J :=
submodule.map_mul _ _ (algebra.of_id R S)

lemma coe_submodule_fg
  (hS : function.injective (algebra_map R S)) (I : ideal R) :
  submodule.fg (coe_submodule S I) ↔ submodule.fg I :=
⟨submodule.fg_of_fg_map _ (linear_map.ker_eq_bot.mpr hS), submodule.fg.map _⟩

@[simp]
lemma coe_submodule_span (s : set R) :
  coe_submodule S (ideal.span s) = submodule.span R ((algebra_map R S) '' s) :=
by { rw [is_localization.coe_submodule, ideal.span, submodule.map_span], refl }

@[simp]
lemma coe_submodule_span_singleton (x : R) :
  coe_submodule S (ideal.span {x}) = submodule.span R {(algebra_map R S) x} :=
by rw [coe_submodule_span, set.image_singleton]

variables {g : R →+* P}
variables {T : submonoid P} (hy : M ≤ T.comap g) {Q : Type*} [comm_ring Q]
variables [algebra P Q] [is_localization T Q]

lemma map_smul (x : S) (z : R) :
  map Q g hy (z • x : S) = g z • map Q g hy x :=
by rw [algebra.smul_def, algebra.smul_def, ring_hom.map_mul, map_eq]

section

include M

lemma is_noetherian_ring (h : is_noetherian_ring R) : is_noetherian_ring S :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at h ⊢,
  exact order_embedding.well_founded ((is_localization.order_embedding M S).dual) h
end

end

section integer_normalization

open polynomial
open_locale classical

variables (M) {S}

/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
noncomputable def coeff_integer_normalization (p : S[X]) (i : ℕ) : R :=
if hi : i ∈ p.support
then classical.some (classical.some_spec
      (exist_integer_multiples_of_finset M (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩))
else 0

lemma coeff_integer_normalization_of_not_mem_support (p : S[X]) (i : ℕ)
  (h : coeff p i = 0) : coeff_integer_normalization M p i = 0 :=
by simp only [coeff_integer_normalization, h, mem_support_iff, eq_self_iff_true, not_true,
  ne.def, dif_neg, not_false_iff]

lemma coeff_integer_normalization_mem_support (p : S[X]) (i : ℕ)
  (h : coeff_integer_normalization M p i ≠ 0) : i ∈ p.support :=
begin
  contrapose h,
  rw [ne.def, not_not, coeff_integer_normalization, dif_neg h]
end

/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integer_normalization (p : S[X]) :
  R[X] :=
∑ i in p.support, monomial i (coeff_integer_normalization M p i)

@[simp]
lemma integer_normalization_coeff (p : S[X]) (i : ℕ) :
  (integer_normalization M p).coeff i = coeff_integer_normalization M p i :=
by simp [integer_normalization, coeff_monomial, coeff_integer_normalization_of_not_mem_support]
  {contextual := tt}

lemma integer_normalization_spec (p : S[X]) :
  ∃ (b : M), ∀ i,
    algebra_map R S ((integer_normalization M p).coeff i) = (b : R) • p.coeff i :=
begin
  use classical.some (exist_integer_multiples_of_finset M (p.support.image p.coeff)),
  intro i,
  rw [integer_normalization_coeff, coeff_integer_normalization],
  split_ifs with hi,
  { exact classical.some_spec (classical.some_spec
      (exist_integer_multiples_of_finset M (p.support.image p.coeff))
      (p.coeff i)
      (finset.mem_image.mpr ⟨i, hi, rfl⟩)) },
  { convert (smul_zero _).symm,
    { apply ring_hom.map_zero },
    { exact not_mem_support_iff.mp hi } }
end

lemma integer_normalization_map_to_map (p : S[X]) :
  ∃ (b : M), (integer_normalization M p).map (algebra_map R S) = (b : R) • p :=
let ⟨b, hb⟩ := integer_normalization_spec M p in
⟨b, polynomial.ext (λ i, by { rw [coeff_map, coeff_smul], exact hb i })⟩

variables {R' : Type*} [comm_ring R']

lemma integer_normalization_eval₂_eq_zero (g : S →+* R') (p : S[X])
  {x : R'} (hx : eval₂ g x p = 0) :
  eval₂ (g.comp (algebra_map R S)) x (integer_normalization M p) = 0 :=
let ⟨b, hb⟩ := integer_normalization_map_to_map M p in
trans (eval₂_map (algebra_map R S) g x).symm
  (by rw [hb, ← is_scalar_tower.algebra_map_smul S (b : R) p, eval₂_smul, hx, mul_zero])

lemma integer_normalization_aeval_eq_zero [algebra R R'] [algebra S R'] [is_scalar_tower R S R']
  (p : S[X]) {x : R'} (hx : aeval x p = 0) :
  aeval x (integer_normalization M p) = 0 :=
by rw [aeval_def, is_scalar_tower.algebra_map_eq R S R',
       integer_normalization_eval₂_eq_zero _ _ _ hx]

end integer_normalization

variables {R M} (S) {K : Type*}

lemma to_map_eq_zero_iff {x : R} (hM : M ≤ non_zero_divisors R) :
  algebra_map R S x = 0 ↔ x = 0 :=
begin
  rw ← (algebra_map R S).map_zero,
  split; intro h,
  { cases (eq_iff_exists M S).mp h with c hc,
    rw zero_mul at hc,
    exact hM c.2 x hc },
  { rw h },
end

protected lemma injective (hM : M ≤ non_zero_divisors R) :
  injective (algebra_map R S) :=
begin
  rw ring_hom.injective_iff (algebra_map R S),
  intros a ha,
  rwa to_map_eq_zero_iff S hM at ha
end

protected lemma to_map_ne_zero_of_mem_non_zero_divisors [nontrivial R]
  (hM : M ≤ non_zero_divisors R) {x : R} (hx : x ∈ non_zero_divisors R) : algebra_map R S x ≠ 0 :=
show (algebra_map R S).to_monoid_with_zero_hom x ≠ 0,
from map_ne_zero_of_mem_non_zero_divisors (algebra_map R S) (is_localization.injective S hM) hx

variables (S Q M)

/-- Injectivity of a map descends to the map induced on localizations. -/
lemma map_injective_of_injective
  (hg : function.injective g) [is_localization (M.map g : submonoid P) Q]
  (hM : (M.map g : submonoid P) ≤ non_zero_divisors P) :
  function.injective (map Q g M.le_comap_map : S → Q) :=
begin
  rintros x y hxy,
  obtain ⟨a, b, rfl⟩ := mk'_surjective M x,
  obtain ⟨c, d, rfl⟩ := mk'_surjective M y,
  rw [map_mk' _ a b, map_mk' _ c d, mk'_eq_iff_eq] at hxy,
  refine mk'_eq_iff_eq.2 (congr_arg (algebra_map _ _) (hg _)),
  convert is_localization.injective _ hM hxy; simp,
end

variables {S Q M}

@[mono]
lemma coe_submodule_le_coe_submodule (h : M ≤ non_zero_divisors R)
  {I J : ideal R} :
  coe_submodule S I ≤ coe_submodule S J ↔ I ≤ J :=
submodule.map_le_map_iff_of_injective (is_localization.injective _ h) _ _

@[mono]
lemma coe_submodule_strict_mono (h : M ≤ non_zero_divisors R) :
  strict_mono (coe_submodule S : ideal R → submodule R S) :=
strict_mono_of_le_iff_le (λ _ _, (coe_submodule_le_coe_submodule h).symm)

variables (S) {Q M}

lemma coe_submodule_injective (h : M ≤ non_zero_divisors R) :
  function.injective (coe_submodule S : ideal R → submodule R S) :=
injective_of_le_imp_le _ (λ _ _, (coe_submodule_le_coe_submodule h).mp)

lemma coe_submodule_is_principal {I : ideal R} (h : M ≤ non_zero_divisors R) :
  (coe_submodule S I).is_principal ↔ I.is_principal :=
begin
  split; unfreezingI { rintros ⟨⟨x, hx⟩⟩ },
  { have x_mem : x ∈ coe_submodule S I := hx.symm ▸ submodule.mem_span_singleton_self x,
    obtain ⟨x, x_mem, rfl⟩ := (mem_coe_submodule _ _).mp x_mem,
    refine ⟨⟨x, coe_submodule_injective S h _⟩⟩,
    rw [ideal.submodule_span_eq, hx, coe_submodule_span_singleton] },
  { refine ⟨⟨algebra_map R S x, _⟩⟩,
    rw [hx, ideal.submodule_span_eq, coe_submodule_span_singleton] }
end

variables {A : Type*} [comm_ring A] [is_domain A]

/-- A `comm_ring` `S` which is the localization of an integral domain `R` at a subset of
non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem is_domain_of_le_non_zero_divisors
  [algebra A S] {M : submonoid A} [is_localization M S]
  (hM : M ≤ non_zero_divisors A) : is_domain S :=
{ eq_zero_or_eq_zero_of_mul_eq_zero :=
    begin
      intros z w h,
      cases surj M z with x hx,
      cases surj M w with y hy,
      have : z * w * algebra_map A S y.2 * algebra_map A S x.2 =
        algebra_map A S x.1 * algebra_map A S y.1,
      by rw [mul_assoc z, hy, ←hx]; ac_refl,
      rw [h, zero_mul, zero_mul, ← (algebra_map A S).map_mul] at this,
      cases eq_zero_or_eq_zero_of_mul_eq_zero ((to_map_eq_zero_iff S hM).mp this.symm) with H H,
      { exact or.inl (eq_zero_of_fst_eq_zero hx H) },
      { exact or.inr (eq_zero_of_fst_eq_zero hy H) },
    end,
  exists_pair_ne := ⟨(algebra_map A S) 0, (algebra_map A S) 1,
                     λ h, zero_ne_one (is_localization.injective S hM h)⟩, }

/-- The localization at of an integral domain to a set of non-zero elements is an integral domain.
See note [reducible non-instances]. -/
@[reducible]
theorem is_domain_localization {M : submonoid A} (hM : M ≤ non_zero_divisors A) :
  is_domain (localization M) :=
is_domain_of_le_non_zero_divisors _ hM

/--
The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
instance is_domain_of_local_at_prime {P : ideal A} (hp : P.is_prime) :
  is_domain (localization.at_prime P) :=
is_domain_localization (le_non_zero_divisors_of_no_zero_divisors
  (not_not_intro P.zero_mem))

namespace at_prime

variables (I : ideal R) [hI : I.is_prime] [is_localization.at_prime S I]
include hI

lemma is_unit_to_map_iff (x : R) :
  is_unit ((algebra_map R S) x) ↔ x ∈ I.prime_compl :=
⟨λ h hx, (is_prime_of_is_prime_disjoint I.prime_compl S I hI disjoint_compl_left).ne_top $
  (ideal.map (algebra_map R S) I).eq_top_of_is_unit_mem (ideal.mem_map_of_mem _ hx) h,
λ h, map_units S ⟨x, h⟩⟩

-- Can't use typeclasses to infer the `local_ring` instance, so use an `opt_param` instead
-- (since `local_ring` is a `Prop`, there should be no unification issues.)
lemma to_map_mem_maximal_iff (x : R) (h : _root_.local_ring S := local_ring S I) :
  algebra_map R S x ∈ local_ring.maximal_ideal S ↔ x ∈ I :=
not_iff_not.mp $ by
simpa only [@local_ring.mem_maximal_ideal S, mem_nonunits_iff, not_not]
  using is_unit_to_map_iff S I x

lemma is_unit_mk'_iff (x : R) (y : I.prime_compl) :
  is_unit (mk' S x y) ↔ x ∈ I.prime_compl :=
⟨λ h hx, mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h,
λ h, is_unit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩

lemma mk'_mem_maximal_iff (x : R) (y : I.prime_compl) (h : _root_.local_ring S := local_ring S I) :
  mk' S x y ∈ local_ring.maximal_ideal S ↔ x ∈ I :=
not_iff_not.mp $ by
simpa only [@local_ring.mem_maximal_ideal S, mem_nonunits_iff, not_not]
  using is_unit_mk'_iff S I x y

end at_prime

end is_localization

namespace localization

open is_localization

local attribute [instance] classical.prop_decidable

variables (I : ideal R) [hI : I.is_prime]
include hI

variables {I}
/-- The unique maximal ideal of the localization at `I.prime_compl` lies over the ideal `I`. -/
lemma at_prime.comap_maximal_ideal :
  ideal.comap (algebra_map R (localization.at_prime I))
    (local_ring.maximal_ideal (localization I.prime_compl)) = I :=
ideal.ext $ λ x, by
simpa only [ideal.mem_comap] using at_prime.to_map_mem_maximal_iff _ I x

/-- The image of `I` in the localization at `I.prime_compl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `at_prime.local_ring` -/
lemma at_prime.map_eq_maximal_ideal :
  ideal.map (algebra_map R (localization.at_prime I)) I =
    (local_ring.maximal_ideal (localization I.prime_compl)) :=
begin
  convert congr_arg (ideal.map _) at_prime.comap_maximal_ideal.symm,
  rw map_comap I.prime_compl
end

lemma le_comap_prime_compl_iff {J : ideal P} [hJ : J.is_prime] {f : R →+* P} :
  I.prime_compl ≤ J.prime_compl.comap f ↔ J.comap f ≤ I :=
⟨λ h x hx, by { contrapose! hx, exact h hx },
 λ h x hx hfxJ, hx (h hfxJ)⟩

variables (I)

/--
For a ring hom `f : R →+* S` and a prime ideal `J` in `S`, the induced ring hom from the
localization of `R` at `J.comap f` to the localization of `S` at `J`.

To make this definition more flexible, we allow any ideal `I` of `R` as input, together with a proof
that `I = J.comap f`. This can be useful when `I` is not definitionally equal to `J.comap f`.
 -/
noncomputable def local_ring_hom (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) :
  localization.at_prime I →+* localization.at_prime J :=
is_localization.map (localization.at_prime J) f (le_comap_prime_compl_iff.mpr (ge_of_eq hIJ))

lemma local_ring_hom_to_map (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) (x : R) :
  local_ring_hom I J f hIJ (algebra_map _ _ x) = algebra_map _ _ (f x) :=
map_eq _ _

lemma local_ring_hom_mk' (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) (x : R) (y : I.prime_compl) :
  local_ring_hom I J f hIJ (is_localization.mk' _ x y) =
    is_localization.mk' (localization.at_prime J) (f x)
      (⟨f y, le_comap_prime_compl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.prime_compl) :=
map_mk' _ _ _

instance is_local_ring_hom_local_ring_hom (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) :
  is_local_ring_hom (local_ring_hom I J f hIJ) :=
is_local_ring_hom.mk $ λ x hx,
begin
  rcases is_localization.mk'_surjective I.prime_compl x with ⟨r, s, rfl⟩,
  rw local_ring_hom_mk' at hx,
  rw at_prime.is_unit_mk'_iff at hx ⊢,
  exact λ hr, hx ((set_like.ext_iff.mp hIJ r).mp hr),
end

lemma local_ring_hom_unique (J : ideal P) [hJ : J.is_prime] (f : R →+* P)
  (hIJ : I = J.comap f) {j : localization.at_prime I →+* localization.at_prime J}
  (hj : ∀ x : R, j (algebra_map _ _ x) = algebra_map _ _ (f x)) :
  local_ring_hom I J f hIJ = j :=
map_unique _ _ hj

@[simp] lemma local_ring_hom_id :
  local_ring_hom I I (ring_hom.id R) (ideal.comap_id I).symm = ring_hom.id _ :=
local_ring_hom_unique _ _ _ _ (λ x, rfl)

@[simp] lemma local_ring_hom_comp {S : Type*} [comm_ring S]
  (J : ideal S) [hJ : J.is_prime] (K : ideal P) [hK : K.is_prime]
  (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* P) (hJK : J = K.comap g) :
  local_ring_hom I K (g.comp f) (by rw [hIJ, hJK, ideal.comap_comap f g]) =
  (local_ring_hom J K g hJK).comp (local_ring_hom I J f hIJ) :=
local_ring_hom_unique _ _ _ _
  (λ r, by simp only [function.comp_app, ring_hom.coe_comp, local_ring_hom_to_map])

end localization

open is_localization

/-- If `R` is a field, then localizing at a submonoid not containing `0` adds no new elements. -/
lemma localization_map_bijective_of_field
  {R Rₘ : Type*} [comm_ring R] [is_domain R] [comm_ring Rₘ]
  {M : submonoid R} (hM : (0 : R) ∉ M) (hR : is_field R)
  [algebra R Rₘ] [is_localization M Rₘ] : function.bijective (algebra_map R Rₘ) :=
begin
  refine ⟨is_localization.injective _ (le_non_zero_divisors_of_no_zero_divisors hM), λ x, _⟩,
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M x,
  obtain ⟨n, hn⟩ := hR.mul_inv_cancel (λ hm0, hM (hm0 ▸ hm) : m ≠ 0),
  exact ⟨r * n,
    by erw [eq_mk'_iff_mul_eq, ← ring_hom.map_mul, mul_assoc, mul_comm n, hn, mul_one]⟩
end

variables (R) {A : Type*} [comm_ring A] [is_domain A]
variables (K : Type*)

/-- `is_fraction_ring R K` states `K` is the field of fractions of an integral domain `R`. -/
-- TODO: should this extend `algebra` instead of assuming it?
abbreviation is_fraction_ring [comm_ring K] [algebra R K] := is_localization (non_zero_divisors R) K

/-- The cast from `int` to `rat` as a `fraction_ring`. -/
instance rat.is_fraction_ring : is_fraction_ring ℤ ℚ :=
{ map_units :=
  begin
    rintro ⟨x, hx⟩,
    rw mem_non_zero_divisors_iff_ne_zero at hx,
    simpa only [ring_hom.eq_int_cast, is_unit_iff_ne_zero, int.cast_eq_zero,
                ne.def, subtype.coe_mk] using hx,
    end,
  surj :=
  begin
    rintro ⟨n, d, hd, h⟩,
    refine ⟨⟨n, ⟨d, _⟩⟩, rat.mul_denom_eq_num⟩,
    rwa [mem_non_zero_divisors_iff_ne_zero, int.coe_nat_ne_zero_iff_pos]
  end,
  eq_iff_exists :=
  begin
    intros x y,
    rw [ring_hom.eq_int_cast, ring_hom.eq_int_cast, int.cast_inj],
    refine ⟨by { rintro rfl, use 1 }, _⟩,
    rintro ⟨⟨c, hc⟩, h⟩,
    apply int.eq_of_mul_eq_mul_right _ h,
    rwa mem_non_zero_divisors_iff_ne_zero at hc,
  end }

namespace is_fraction_ring

variables {R K}

section comm_ring

variables [comm_ring K] [algebra R K] [is_fraction_ring R K] [algebra A K] [is_fraction_ring A K]

lemma to_map_eq_zero_iff {x : R} :
  algebra_map R K x = 0 ↔ x = 0 :=
to_map_eq_zero_iff _ (le_of_eq rfl)

variables (R K)

protected theorem injective : function.injective (algebra_map R K) :=
is_localization.injective _ (le_of_eq rfl)

variables {R K}

@[simp, mono]
lemma coe_submodule_le_coe_submodule
  {I J : ideal R} : coe_submodule K I ≤ coe_submodule K J ↔ I ≤ J :=
is_localization.coe_submodule_le_coe_submodule le_rfl

@[mono]
lemma coe_submodule_strict_mono :
  strict_mono (coe_submodule K : ideal R → submodule R K) :=
strict_mono_of_le_iff_le (λ _ _, coe_submodule_le_coe_submodule.symm)

@[priority 100] instance [no_zero_divisors K] : no_zero_smul_divisors R K :=
no_zero_smul_divisors.of_algebra_map_injective $ is_fraction_ring.injective R K

variables (R K)

lemma coe_submodule_injective :
  function.injective (coe_submodule K : ideal R → submodule R K) :=
injective_of_le_imp_le _ (λ _ _, (coe_submodule_le_coe_submodule).mp)

@[simp]
lemma coe_submodule_is_principal {I : ideal R} :
  (coe_submodule K I).is_principal ↔ I.is_principal :=
is_localization.coe_submodule_is_principal _ le_rfl

variables {R K}

protected lemma to_map_ne_zero_of_mem_non_zero_divisors [nontrivial R]
  {x : R} (hx : x ∈ non_zero_divisors R) : algebra_map R K x ≠ 0 :=
is_localization.to_map_ne_zero_of_mem_non_zero_divisors _ le_rfl hx

variables (A)

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is an
integral domain. -/
protected theorem is_domain : is_domain K :=
is_domain_of_le_non_zero_divisors K (le_refl (non_zero_divisors A))

local attribute [instance] classical.dec_eq

/-- The inverse of an element in the field of fractions of an integral domain. -/
@[irreducible]
protected noncomputable def inv (z : K) : K :=
if h : z = 0 then 0 else
mk' K ↑(sec (non_zero_divisors A) z).2
  ⟨(sec _ z).1,
   mem_non_zero_divisors_iff_ne_zero.2 $ λ h0, h $
    eq_zero_of_fst_eq_zero (sec_spec (non_zero_divisors A) z) h0⟩

local attribute [semireducible] is_fraction_ring.inv

protected lemma mul_inv_cancel (x : K) (hx : x ≠ 0) :
  x * is_fraction_ring.inv A x = 1 :=
show x * dite _ _ _ = 1, by rw [dif_neg hx,
  ←is_unit.mul_left_inj (map_units K ⟨(sec _ x).1, mem_non_zero_divisors_iff_ne_zero.2 $
    λ h0, hx $ eq_zero_of_fst_eq_zero (sec_spec (non_zero_divisors A) x) h0⟩),
  one_mul, mul_assoc, mk'_spec, ←eq_mk'_iff_mul_eq]; exact (mk'_sec _ x).symm

/-- A `comm_ring` `K` which is the localization of an integral domain `R` at `R - {0}` is a field.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def to_field : field K :=
{ inv := is_fraction_ring.inv A,
  mul_inv_cancel := is_fraction_ring.mul_inv_cancel A,
  inv_zero := dif_pos rfl,
  .. is_fraction_ring.is_domain A,
  .. show comm_ring K, by apply_instance }

end comm_ring

variables {B : Type*} [comm_ring B] [is_domain B] [field K] {L : Type*} [field L]
  [algebra A K] [is_fraction_ring A K] {g : A →+* L}

lemma mk'_mk_eq_div {r s} (hs : s ∈ non_zero_divisors A) :
  mk' K r ⟨s, hs⟩ = algebra_map A K r / algebra_map A K s :=
mk'_eq_iff_eq_mul.2 $ (div_mul_cancel (algebra_map A K r)
    (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors hs)).symm

@[simp] lemma mk'_eq_div {r} (s : non_zero_divisors A) :
  mk' K r s = algebra_map A K r / algebra_map A K s :=
mk'_mk_eq_div s.2

lemma div_surjective (z : K) : ∃ (x y : A) (hy : y ∈ non_zero_divisors A),
  algebra_map _ _ x / algebra_map _ _ y = z :=
let ⟨x, ⟨y, hy⟩, h⟩ := mk'_surjective (non_zero_divisors A) z
in ⟨x, y, hy, by rwa mk'_eq_div at h⟩

lemma is_unit_map_of_injective (hg : function.injective g)
  (y : non_zero_divisors A) : is_unit (g y) :=
is_unit.mk0 (g y) $ show g.to_monoid_with_zero_hom y ≠ 0,
  from map_ne_zero_of_mem_non_zero_divisors g hg y.2

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field, we get a
field hom sending `z : K` to `g x * (g y)⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (hg : injective g) : K →+* L :=
lift $ λ (y : non_zero_divisors A), is_unit_map_of_injective hg y

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
the field hom induced from `K` to `L` maps `x` to `g x` for all
`x : A`. -/
@[simp] lemma lift_algebra_map (hg : injective g) (x) :
  lift hg (algebra_map A K x) = g x :=
lift_eq _ _

/-- Given an integral domain `A` with field of fractions `K`,
and an injective ring hom `g : A →+* L` where `L` is a field,
field hom induced from `K` to `L` maps `f x / f y` to `g x / g y` for all
`x : A, y ∈ non_zero_divisors A`. -/
lemma lift_mk' (hg : injective g) (x) (y : non_zero_divisors A) :
  lift hg (mk' K x y) = g x / g y :=
by simp only [mk'_eq_div, ring_hom.map_div, lift_algebra_map]

/-- Given integral domains `A, B` with fields of fractions `K`, `L`
and an injective ring hom `j : A →+* B`, we get a field hom
sending `z : K` to `g (j x) * (g (j y))⁻¹`, where `(x, y) : A × (non_zero_divisors A)` are
such that `z = f x * (f y)⁻¹`. -/
noncomputable def map {A B K L : Type*} [comm_ring A] [comm_ring B] [is_domain B]
  [comm_ring K] [algebra A K] [is_fraction_ring A K] [comm_ring L] [algebra B L]
  [is_fraction_ring B L] {j : A →+* B} (hj : injective j) :
  K →+* L :=
map L j (show non_zero_divisors A ≤ (non_zero_divisors B).comap j,
         from non_zero_divisors_le_comap_non_zero_divisors_of_injective j hj)

/-- Given integral domains `A, B` and localization maps to their fields of fractions
`f : A →+* K, g : B →+* L`, an isomorphism `j : A ≃+* B` induces an isomorphism of
fields of fractions `K ≃+* L`. -/
noncomputable def field_equiv_of_ring_equiv [algebra B L] [is_fraction_ring B L] (h : A ≃+* B) :
  K ≃+* L :=
ring_equiv_of_ring_equiv K L h
begin
  ext b,
  show b ∈ h.to_equiv '' _ ↔ _,
  erw [h.to_equiv.image_eq_preimage, set.preimage, set.mem_set_of_eq,
       mem_non_zero_divisors_iff_ne_zero, mem_non_zero_divisors_iff_ne_zero],
  exact h.symm.map_ne_zero_iff
end

lemma integer_normalization_eq_zero_iff {p : K[X]} :
  integer_normalization (non_zero_divisors A) p = 0 ↔ p = 0 :=
begin
  refine (polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm),
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integer_normalization_spec _ p,
  split; intros h i,
  { apply to_map_eq_zero_iff.mp,
    rw [hb i, h i],
    apply smul_zero,
    assumption },
  { have hi := h i,
    rw [polynomial.coeff_zero, ← @to_map_eq_zero_iff A _ K, hb i, algebra.smul_def] at hi,
    apply or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi),
    intro h,
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero,
    exact to_map_eq_zero_iff.mp h }
end

section

variables (A K) (C : Type*)
variables [comm_ring C]

/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
lemma is_algebraic_iff [algebra A C] [algebra K C] [is_scalar_tower A K C] {x : C} :
  is_algebraic A x ↔ is_algebraic K x :=
begin
  split; rintros ⟨p, hp, px⟩,
  { refine ⟨p.map (algebra_map A K), λ h, hp (polynomial.ext (λ i, _)), _⟩,
    { have : algebra_map A K (p.coeff i) = 0 := trans (polynomial.coeff_map _ _).symm (by simp [h]),
      exact to_map_eq_zero_iff.mp this },
    { rwa is_scalar_tower.aeval_apply _ K at px } },
  { exact ⟨integer_normalization _ p,
           mt integer_normalization_eq_zero_iff.mp hp,
           integer_normalization_aeval_eq_zero _ p px⟩ },
end

variables {A K C}

/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
lemma comap_is_algebraic_iff [algebra A C] [algebra K C] [is_scalar_tower A K C] :
  algebra.is_algebraic A C ↔ algebra.is_algebraic K C :=
⟨λ h x, (is_algebraic_iff A K C).mp (h x), λ h x, (is_algebraic_iff A K C).mpr (h x)⟩

end

section num_denom

variables (A) [unique_factorization_monoid A]

lemma exists_reduced_fraction (x : K) :
  ∃ (a : A) (b : non_zero_divisors A),
  (∀ {d}, d ∣ a → d ∣ b → is_unit d) ∧ mk' K a b = x :=
begin
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (non_zero_divisors A) x,
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    unique_factorization_monoid.exists_reduced_factors' a b
      (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero),
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  refine ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩,
  refine mul_left_cancel₀
    (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors b_nonzero) _,
  simp only [subtype.coe_mk, ring_hom.map_mul, algebra.smul_def] at *,
  erw [←hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩],
end

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
classical.some (exists_reduced_fraction A x)

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def denom (x : K) : non_zero_divisors A :=
classical.some (classical.some_spec (exists_reduced_fraction A x))

lemma num_denom_reduced (x : K) :
  ∀ {d}, d ∣ num A x → d ∣ denom A x → is_unit d :=
(classical.some_spec (classical.some_spec (exists_reduced_fraction A x))).1

@[simp] lemma mk'_num_denom (x : K) : mk' K (num A x) (denom A x) = x :=
(classical.some_spec (classical.some_spec (exists_reduced_fraction A x))).2

variables {A}

lemma num_mul_denom_eq_num_iff_eq {x y : K} :
  x * algebra_map A K (denom A y) = algebra_map A K (num A y) ↔ x = y :=
⟨λ h, by simpa only [mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h,
 λ h, eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩

lemma num_mul_denom_eq_num_iff_eq' {x y : K} :
  y * algebra_map A K (denom A x) = algebra_map A K (num A x) ↔ x = y :=
⟨λ h, by simpa only [eq_comm, mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h,
 λ h, eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩

lemma num_mul_denom_eq_num_mul_denom_iff_eq {x y : K} :
  num A y * denom A x = num A x * denom A y ↔ x = y :=
⟨λ h, by simpa only [mk'_num_denom] using mk'_eq_of_eq h,
 λ h, by rw h⟩

lemma eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
num_mul_denom_eq_num_iff_eq'.mp (by rw [zero_mul, h, ring_hom.map_zero])

lemma is_integer_of_is_unit_denom {x : K} (h : is_unit (denom A x : A)) : is_integer A x :=
begin
  cases h with d hd,
  have d_ne_zero : algebra_map A K (denom A x) ≠ 0 :=
    is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors (denom A x).2,
  use ↑d⁻¹ * num A x,
  refine trans _ (mk'_num_denom A x),
  rw [ring_hom.map_mul, ring_hom.map_units_inv, hd],
  apply mul_left_cancel₀ d_ne_zero,
  rw [←mul_assoc, mul_inv_cancel d_ne_zero, one_mul, mk'_spec']
end

lemma is_unit_denom_of_num_eq_zero {x : K} (h : num A x = 0) : is_unit (denom A x : A) :=
num_denom_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl

end num_denom

variables (S)

lemma is_fraction_ring_iff_of_base_ring_equiv (h : R ≃+* P) :
  is_fraction_ring R S ↔
    @@is_fraction_ring P _ S _ ((algebra_map R S).comp h.symm.to_ring_hom).to_algebra :=
begin
  delta is_fraction_ring,
  convert is_localization_iff_of_base_ring_equiv _ _ h,
  ext x,
  erw submonoid.map_equiv_eq_comap_symm,
  simp only [mul_equiv.coe_to_monoid_hom,
    ring_equiv.to_mul_equiv_eq_coe, submonoid.mem_comap],
  split,
  { rintros hx z (hz : z * h.symm x = 0),
    rw ← h.map_eq_zero_iff,
    apply hx,
    simpa only [h.map_zero, h.apply_symm_apply, h.map_mul] using congr_arg h hz },
  { rintros (hx : h.symm x ∈ _) z hz,
    rw ← h.symm.map_eq_zero_iff,
    apply hx,
    rw [← h.symm.map_mul, hz, h.symm.map_zero] }
end

variable (M)

lemma is_fraction_ring_of_is_localization (S T : Type*) [comm_ring S] [comm_ring T]
  [algebra R S] [algebra R T] [algebra S T] [is_scalar_tower R S T]
  [is_localization M S] [is_fraction_ring R T] (hM : M ≤ non_zero_divisors R) :
  is_fraction_ring S T :=
begin
  have := is_localization_of_submonoid_le S T M (non_zero_divisors R) _,
  refine @@is_localization_of_is_exists_mul_mem _ _ _ _ _ _ this _ _,
  { exact map_non_zero_divisors_le M S },
  { rintro ⟨x, hx⟩,
    obtain ⟨⟨y, s⟩, e⟩ := is_localization.surj M x,
    use algebra_map R S s,
    rw [mul_comm, subtype.coe_mk, e],
    refine set.mem_image_of_mem (algebra_map R S) _,
    intros z hz,
    apply is_localization.injective S hM,
    rw map_zero,
    apply hx,
    rw [← (map_units S s).mul_left_inj, mul_assoc, e, ← map_mul, hz, map_zero, zero_mul] },
  { exact hM }
end

protected
lemma nontrivial (R S : Type*) [comm_ring R] [nontrivial R] [comm_ring S] [algebra R S]
  [is_fraction_ring R S] : nontrivial S :=
begin
  apply nontrivial_of_ne,
  intro h,
  apply @zero_ne_one R,
  exact is_localization.injective S (le_of_eq rfl)
    (((algebra_map R S).map_zero.trans h).trans (algebra_map R S).map_one.symm),
end

lemma is_fraction_ring_of_is_domain_of_is_localization [is_domain R] (S T : Type*)
  [comm_ring S] [comm_ring T] [algebra R S] [algebra R T] [algebra S T]
  [is_scalar_tower R S T] [is_localization M S] [is_fraction_ring R T] : is_fraction_ring S T :=
begin
  haveI := is_fraction_ring.nontrivial R T,
  haveI := (algebra_map S T).domain_nontrivial,
  apply is_fraction_ring_of_is_localization M S T,
  intros x hx,
  rw mem_non_zero_divisors_iff_ne_zero,
  intro hx',
  apply @zero_ne_one S,
  rw [← (algebra_map R S).map_one, ← @mk'_one R _ M, @comm _ eq, mk'_eq_zero_iff],
  exact ⟨⟨_, hx⟩, (one_mul x).symm ▸ hx'⟩,
end

end is_fraction_ring

section algebra

section is_integral
variables {R S} {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]
variables [algebra R Rₘ] [is_localization M Rₘ]
variables [algebra S Sₘ] [is_localization (algebra.algebra_map_submonoid S M) Sₘ]

section

variables (S M)

/-- Definition of the natural algebra induced by the localization of an algebra.
Given an algebra `R → S`, a submonoid `R` of `M`, and a localization `Rₘ` for `M`,
let `Sₘ` be the localization of `S` to the image of `M` under `algebra_map R S`.
Then this is the natural algebra structure on `Rₘ → Sₘ`, such that the entire square commutes,
where `localization_map.map_comp` gives the commutativity of the underlying maps -/
noncomputable def localization_algebra : algebra Rₘ Sₘ :=
(map Sₘ (algebra_map R S)
    (show _ ≤ (algebra.algebra_map_submonoid S M).comap _, from M.le_comap_map)
  : Rₘ →+* Sₘ).to_algebra

end

lemma algebra_map_mk' (r : R) (m : M) :
  (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) (mk' Rₘ r m) =
    mk' Sₘ (algebra_map R S r) ⟨algebra_map R S m, algebra.mem_algebra_map_submonoid_of_mem m⟩ :=
map_mk' _ _ _

variables (Rₘ Sₘ)

/-- Injectivity of the underlying `algebra_map` descends to the algebra induced by localization. -/
lemma localization_algebra_injective (hRS : function.injective (algebra_map R S))
  (hM : algebra.algebra_map_submonoid S M ≤ non_zero_divisors S) :
  function.injective (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) :=
is_localization.map_injective_of_injective M Rₘ Sₘ hRS hM

variables {Rₘ Sₘ}

open polynomial

lemma ring_hom.is_integral_elem_localization_at_leading_coeff
  {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : submonoid R)
  (hM : p.leading_coeff ∈ M) {Rₘ Sₘ : Type*} [comm_ring Rₘ] [comm_ring Sₘ]
  [algebra R Rₘ] [is_localization M Rₘ]
  [algebra S Sₘ] [is_localization (M.map f : submonoid S) Sₘ] :
  (map Sₘ f M.le_comap_map : Rₘ →+* _).is_integral_elem (algebra_map S Sₘ x) :=
begin
  by_cases triv : (1 : Rₘ) = 0,
  { exact ⟨0, ⟨trans leading_coeff_zero triv.symm, eval₂_zero _ _⟩⟩ },
  haveI : nontrivial Rₘ := nontrivial_of_ne 1 0 triv,
  obtain ⟨b, hb⟩ := is_unit_iff_exists_inv.mp
    (map_units Rₘ ⟨p.leading_coeff, hM⟩),
  refine ⟨(p.map (algebra_map R Rₘ)) * C b, ⟨_, _⟩⟩,
  { refine monic_mul_C_of_leading_coeff_mul_eq_one _,
    rwa leading_coeff_map_of_leading_coeff_ne_zero (algebra_map R Rₘ),
    refine λ hfp, zero_ne_one (trans (zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1) },
  { refine eval₂_mul_eq_zero_of_left _ _ _ _,
    erw [eval₂_map, is_localization.map_comp, ← hom_eval₂ _ f (algebra_map S Sₘ) x],
    exact trans (congr_arg (algebra_map S Sₘ) hf) (ring_hom.map_zero _) }
end

/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leading_coeff {x : S} (p : R[X])
  (hp : aeval x p = 0) (hM : p.leading_coeff ∈ M) :
  (map Sₘ (algebra_map R S)
      (show _ ≤ (algebra.algebra_map_submonoid S M).comap _, from M.le_comap_map)
    : Rₘ →+* _).is_integral_elem (algebra_map S Sₘ x) :=
(algebra_map R S).is_integral_elem_localization_at_leading_coeff x p hp M hM

/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem is_integral_localization (H : algebra.is_integral R S) :
  (map Sₘ (algebra_map R S)
    (show _ ≤ (algebra.algebra_map_submonoid S M).comap _, from M.le_comap_map)
    : Rₘ →+* _).is_integral :=
begin
  intro x,
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (algebra.algebra_map_submonoid S M) x,
  obtain ⟨v, hv⟩ := hu,
  obtain ⟨v', hv'⟩ := is_unit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩),
  refine @is_integral_of_is_integral_mul_unit Rₘ _ _ _
    (localization_algebra M S) x (algebra_map S Sₘ u) v' _ _,
  { replace hv' := congr_arg (@algebra_map Rₘ Sₘ _ _ (localization_algebra M S)) hv',
    rw [ring_hom.map_mul, ring_hom.map_one, ← ring_hom.comp_apply _ (algebra_map R Rₘ)] at hv',
    erw is_localization.map_comp at hv',
    exact hv.2 ▸ hv' },
  { obtain ⟨p, hp⟩ := H s,
    exact hx.symm ▸ is_integral_localization_at_leading_coeff p hp.2 (hp.1.symm ▸ M.one_mem) }
end

lemma is_integral_localization' {R S : Type*} [comm_ring R] [comm_ring S]
  {f : R →+* S} (hf : f.is_integral) (M : submonoid R) :
  (map (localization (M.map (f : R →* S))) f M.le_comap_map : localization M →+* _).is_integral :=
@is_integral_localization R _ M S _ f.to_algebra _ _ _ _ _ _ _ _ hf

end is_integral

namespace is_integral_closure

variables (A) {L : Type*} [field K] [field L] [algebra A K] [algebra A L] [is_fraction_ring A K]
variables (C : Type*) [comm_ring C] [is_domain C] [algebra C L] [is_integral_closure C A L]
variables [algebra A C] [is_scalar_tower A C L]

open algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_algebraic (alg : is_algebraic A L)
  (inj : ∀ x, algebra_map A L x = 0 → x = 0) :
  is_fraction_ring C L :=
{ map_units := λ ⟨y, hy⟩,
    is_unit.mk0 _ (show algebra_map C L y ≠ 0, from λ h, mem_non_zero_divisors_iff_ne_zero.mp hy
      ((algebra_map C L).injective_iff.mp (algebra_map_injective C A L) _ h)),
  surj := λ z, let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj in
    ⟨⟨mk' C (x : L) x.2, algebra_map _ _ y,
        mem_non_zero_divisors_iff_ne_zero.mpr (λ h, hy (inj _
          (by rw [is_scalar_tower.algebra_map_apply A C L, h, ring_hom.map_zero])))⟩,
     by rw [set_like.coe_mk, algebra_map_mk', ← is_scalar_tower.algebra_map_apply A C L, hxy]⟩,
  eq_iff_exists := λ x y, ⟨λ h, ⟨1, by simpa using algebra_map_injective C A L h⟩, λ ⟨c, hc⟩,
    congr_arg (algebra_map _ L) (mul_right_cancel₀ (mem_non_zero_divisors_iff_ne_zero.mp c.2) hc)⟩ }

variables (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_finite_extension [algebra K L] [is_scalar_tower A K L]
  [finite_dimensional K L] : is_fraction_ring C L :=
is_fraction_ring_of_algebraic A C
  (is_fraction_ring.comap_is_algebraic_iff.mpr (is_algebraic_of_finite K L))
  (λ x hx, is_fraction_ring.to_map_eq_zero_iff.mp ((algebra_map K L).map_eq_zero.mp $
    (is_scalar_tower.algebra_map_apply _ _ _ _).symm.trans hx))

end is_integral_closure

namespace integral_closure

variables {L : Type*} [field K] [field L] [algebra A K] [is_fraction_ring A K]

open algebra

/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_algebraic [algebra A L] (alg : is_algebraic A L)
  (inj : ∀ x, algebra_map A L x = 0 → x = 0) :
  is_fraction_ring (integral_closure A L) L :=
is_integral_closure.is_fraction_ring_of_algebraic A (integral_closure A L) alg inj

variables (K L)

/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
lemma is_fraction_ring_of_finite_extension [algebra A L] [algebra K L]
  [is_scalar_tower A K L] [finite_dimensional K L] :
  is_fraction_ring (integral_closure A L) L :=
is_integral_closure.is_fraction_ring_of_finite_extension A K L (integral_closure A L)

end integral_closure

end algebra

variables (R A)

/-- The fraction ring of a commutative ring `R` as a quotient type.

We instantiate this definition as generally as possible, and assume that the
commutative ring `R` is an integral domain only when this is needed for proving.
-/
@[reducible] def fraction_ring := localization (non_zero_divisors R)

namespace fraction_ring

instance [subsingleton R] : subsingleton (fraction_ring R) :=
localization.subsingleton

instance [nontrivial R] : nontrivial (fraction_ring R) :=
⟨⟨(algebra_map R _) 0, (algebra_map _ _) 1,
  λ H, zero_ne_one (is_localization.injective _ le_rfl H)⟩⟩

variables {A}

noncomputable instance : field (fraction_ring A) :=
{ add := (+),
  mul := (*),
  neg := has_neg.neg,
  sub := has_sub.sub,
  one := 1,
  zero := 0,
  nsmul := add_monoid.nsmul,
  zsmul := sub_neg_monoid.zsmul,
  npow := localization.npow _,
  .. localization.comm_ring,
  .. is_fraction_ring.to_field A }

@[simp] lemma mk_eq_div {r s} : (localization.mk r s : fraction_ring A) =
  (algebra_map _ _ r / algebra_map A _ s : fraction_ring A) :=
by rw [localization.mk_eq_mk', is_fraction_ring.mk'_eq_div]

noncomputable instance [is_domain R] [field K] [algebra R K] [no_zero_smul_divisors R K] :
  algebra (fraction_ring R) K :=
ring_hom.to_algebra (is_fraction_ring.lift (no_zero_smul_divisors.algebra_map_injective R _))

instance [is_domain R] [field K] [algebra R K] [no_zero_smul_divisors R K] :
  is_scalar_tower R (fraction_ring R) K :=
is_scalar_tower.of_algebra_map_eq (λ x, (is_fraction_ring.lift_algebra_map _ x).symm)

variables (A)

/-- Given an integral domain `A` and a localization map to a field of fractions
`f : A →+* K`, we get an `A`-isomorphism between the field of fractions of `A` as a quotient
type and `K`. -/
noncomputable def alg_equiv (K : Type*) [field K] [algebra A K] [is_fraction_ring A K] :
  fraction_ring A ≃ₐ[A] K :=
localization.alg_equiv (non_zero_divisors A) K

instance [algebra R A] [no_zero_smul_divisors R A] : no_zero_smul_divisors R (fraction_ring A) :=
no_zero_smul_divisors.of_algebra_map_injective
  begin
    rw [is_scalar_tower.algebra_map_eq R A],
    exact function.injective.comp
      (no_zero_smul_divisors.algebra_map_injective _ _)
      (no_zero_smul_divisors.algebra_map_injective _ _)
  end

end fraction_ring

namespace is_fraction_ring

variables (R S K)

/-- `S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R` -/
lemma is_algebraic_iff' [field K] [is_domain R] [is_domain S] [algebra R K] [algebra S K]
  [no_zero_smul_divisors R K] [is_fraction_ring S K] [is_scalar_tower R S K] :
  algebra.is_algebraic R S ↔ algebra.is_algebraic R K :=
begin
  simp only [algebra.is_algebraic],
  split,
  { intros h x,
    rw [is_fraction_ring.is_algebraic_iff R (fraction_ring R) K, is_algebraic_iff_is_integral],
    obtain ⟨(a : S), b, ha, rfl⟩ := @div_surjective S _ _ _ _ _ _ x,
    obtain ⟨f, hf₁, hf₂⟩ := h b,
    rw [div_eq_mul_inv],
    refine is_integral_mul _ _,
    { rw [← is_algebraic_iff_is_integral],
      refine _root_.is_algebraic_of_larger_base_of_injective
        (no_zero_smul_divisors.algebra_map_injective R (fraction_ring R)) _,
      exact is_algebraic_algebra_map_of_is_algebraic (h a) },
    { rw [← is_algebraic_iff_is_integral],
      use (f.map (algebra_map R (fraction_ring R))).reverse,
      split,
      { rwa [ne.def, polynomial.reverse_eq_zero, ← polynomial.degree_eq_bot,
          polynomial.degree_map_eq_of_injective
            (no_zero_smul_divisors.algebra_map_injective R (fraction_ring R)),
          polynomial.degree_eq_bot]},
      { haveI : invertible (algebra_map S K b),
           from is_unit.invertible (is_unit_of_mem_non_zero_divisors
              (mem_non_zero_divisors_iff_ne_zero.2
                (λ h, non_zero_divisors.ne_zero ha
                    ((ring_hom.injective_iff (algebra_map S K)).1
                    (no_zero_smul_divisors.algebra_map_injective _ _) b h)))),
        rw [polynomial.aeval_def, ← inv_of_eq_inv, polynomial.eval₂_reverse_eq_zero_iff,
          polynomial.eval₂_map, ← is_scalar_tower.algebra_map_eq, ← polynomial.aeval_def,
          ← is_scalar_tower.algebra_map_aeval, hf₂, ring_hom.map_zero] } } },
  { intros h x,
    obtain ⟨f, hf₁, hf₂⟩ := h (algebra_map S K x),
    use [f, hf₁],
    rw [← is_scalar_tower.algebra_map_aeval] at hf₂,
    exact (algebra_map S K).injective_iff.1
      (no_zero_smul_divisors.algebra_map_injective _ _) _ hf₂ }
end

end is_fraction_ring
