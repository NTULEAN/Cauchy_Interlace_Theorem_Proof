/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johan Commelin
-/
import data.polynomial.field_division
import ring_theory.integral_closure
import ring_theory.polynomial.gauss_lemma

/-!
# Minimal polynomials

This file defines the minimal polynomial of an element `x` of an `A`-algebra `B`,
under the assumption that x is integral over `A`.

After stating the defining property we specialize to the setting of field extensions
and derive some well-known properties, amongst which the fact that minimal polynomials
are irreducible, and uniquely determined by their defining property.

-/

open_locale classical polynomial
open polynomial set function

variables {A B : Type*}

section min_poly_def
variables (A) [comm_ring A] [ring B] [algebra A B]

/--
Suppose `x : B`, where `B` is an `A`-algebra.

The minimal polynomial `minpoly A x` of `x`
is a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,
if such exists (`is_integral A x`) or zero otherwise.

For example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then
the minimal polynomial of `f` is `minpoly 𝕜 f`.
-/
noncomputable def minpoly (x : B) : A[X] :=
if hx : is_integral A x then well_founded.min degree_lt_wf _ hx else 0

end min_poly_def

namespace minpoly

section ring
variables [comm_ring A] [ring B] [algebra A B]
variables {x : B}

/-- A minimal polynomial is monic. -/
lemma monic (hx : is_integral A x) : monic (minpoly A x) :=
by { delta minpoly, rw dif_pos hx, exact (well_founded.min_mem degree_lt_wf _ hx).1 }

/-- A minimal polynomial is nonzero. -/
lemma ne_zero [nontrivial A] (hx : is_integral A x) : minpoly A x ≠ 0 :=
ne_zero_of_monic (monic hx)

lemma eq_zero (hx : ¬ is_integral A x) : minpoly A x = 0 :=
dif_neg hx

variables (A x)

/-- An element is a root of its minimal polynomial. -/
@[simp] lemma aeval : aeval x (minpoly A x) = 0 :=
begin
  delta minpoly, split_ifs with hx,
  { exact (well_founded.min_mem degree_lt_wf _ hx).2 },
  { exact aeval_zero _ }
end

/-- A minimal polynomial is not `1`. -/
lemma ne_one [nontrivial B] : minpoly A x ≠ 1 :=
begin
  intro h,
  refine (one_ne_zero : (1 : B) ≠ 0) _,
  simpa using congr_arg (polynomial.aeval x) h
end

lemma map_ne_one [nontrivial B] {R : Type*} [semiring R] [nontrivial R] (f : A →+* R) :
  (minpoly A x).map f ≠ 1 :=
begin
  by_cases hx : is_integral A x,
  { exact mt ((monic hx).eq_one_of_map_eq_one f) (ne_one A x) },
  { rw [eq_zero hx, polynomial.map_zero], exact zero_ne_one },
end

/-- A minimal polynomial is not a unit. -/
lemma not_is_unit [nontrivial B] : ¬ is_unit (minpoly A x) :=
begin
  haveI : nontrivial A := (algebra_map A B).domain_nontrivial,
  by_cases hx : is_integral A x,
  { exact mt (eq_one_of_is_unit_of_monic (monic hx)) (ne_one A x) },
  { rw [eq_zero hx], exact not_is_unit_zero }
end

lemma mem_range_of_degree_eq_one (hx : (minpoly A x).degree = 1) : x ∈ (algebra_map A B).range :=
begin
  have h : is_integral A x,
  { by_contra h,
    rw [eq_zero h, degree_zero, ←with_bot.coe_one] at hx,
    exact (ne_of_lt (show ⊥ < ↑1, from with_bot.bot_lt_coe 1) hx) },
  have key := minpoly.aeval A x,
  rw [eq_X_add_C_of_degree_eq_one hx, (minpoly.monic h).leading_coeff, C_1, one_mul, aeval_add,
      aeval_C, aeval_X, ←eq_neg_iff_add_eq_zero, ←ring_hom.map_neg] at key,
  exact ⟨-(minpoly A x).coeff 0, key.symm⟩,
end

/-- The defining property of the minimal polynomial of an element `x`:
it is the monic polynomial with smallest degree that has `x` as its root. -/
lemma min {p : A[X]} (pmonic : p.monic) (hp : polynomial.aeval x p = 0) :
  degree (minpoly A x) ≤ degree p :=
begin
  delta minpoly, split_ifs with hx,
  { exact le_of_not_lt (well_founded.not_lt_min degree_lt_wf _ hx ⟨pmonic, hp⟩) },
  { simp only [degree_zero, bot_le] }
end

@[nontriviality] lemma subsingleton [subsingleton B] : minpoly A x = 1 :=
begin
  nontriviality A,
  have := minpoly.min A x monic_one (subsingleton.elim _ _),
  rw degree_one at this,
  cases le_or_lt (minpoly A x).degree 0 with h h,
  { rwa (monic ⟨1, monic_one, by simp⟩ : (minpoly A x).monic).degree_le_zero_iff_eq_one at h },
  { exact (this.not_lt h).elim },
end

end ring

section comm_ring

variables [comm_ring A]

section ring

variables [ring B] [algebra A B] [nontrivial B]
variables {x : B}

/-- The degree of a minimal polynomial, as a natural number, is positive. -/
lemma nat_degree_pos (hx : is_integral A x) : 0 < nat_degree (minpoly A x) :=
begin
  rw pos_iff_ne_zero,
  intro ndeg_eq_zero,
  have eq_one : minpoly A x = 1,
  { rw eq_C_of_nat_degree_eq_zero ndeg_eq_zero, convert C_1,
    simpa only [ndeg_eq_zero.symm] using (monic hx).leading_coeff },
  simpa only [eq_one, alg_hom.map_one, one_ne_zero] using aeval A x
end

/-- The degree of a minimal polynomial is positive. -/
lemma degree_pos (hx : is_integral A x) : 0 < degree (minpoly A x) :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos hx)

/-- If `B/A` is an injective ring extension, and `a` is an element of `A`,
then the minimal polynomial of `algebra_map A B a` is `X - C a`. -/
lemma eq_X_sub_C_of_algebra_map_inj [nontrivial A]
  (a : A) (hf : function.injective (algebra_map A B)) :
  minpoly A (algebra_map A B a) = X - C a :=
begin
  have hdegle : (minpoly A (algebra_map A B a)).nat_degree ≤ 1,
  { apply with_bot.coe_le_coe.1,
    rw [←degree_eq_nat_degree (ne_zero (@is_integral_algebra_map A B _ _ _ a)),
      with_top.coe_one, ←degree_X_sub_C a],
    refine min A (algebra_map A B a) (monic_X_sub_C a) _,
    simp only [aeval_C, aeval_X, alg_hom.map_sub, sub_self] },
  have hdeg : (minpoly A (algebra_map A B a)).degree = 1,
  { apply (degree_eq_iff_nat_degree_eq (ne_zero (@is_integral_algebra_map A B _ _ _ a))).2,
    apply le_antisymm hdegle (nat_degree_pos (@is_integral_algebra_map A B _ _ _ a)) },
  have hrw := eq_X_add_C_of_degree_eq_one hdeg,
  simp only [monic (@is_integral_algebra_map A B _ _ _ a), one_mul,
    monic.leading_coeff, ring_hom.map_one] at hrw,
  have h0 : (minpoly A (algebra_map A B a)).coeff 0 = -a,
  { have hroot := aeval A (algebra_map A B a),
    rw [hrw, add_comm] at hroot,
    simp only [aeval_C, aeval_X, aeval_add] at hroot,
    replace hroot := eq_neg_of_add_eq_zero hroot,
    rw [←ring_hom.map_neg _ a] at hroot,
    exact (hf hroot) },
  rw hrw,
  simp only [h0, ring_hom.map_neg, sub_eq_add_neg],
end

end ring

section is_domain

variables [is_domain A] [ring B] [algebra A B]
variables {x : B}

/-- If `a` strictly divides the minimal polynomial of `x`, then `x` cannot be a root for `a`. -/
lemma aeval_ne_zero_of_dvd_not_unit_minpoly {a : A[X]} (hx : is_integral A x)
  (hamonic : a.monic) (hdvd : dvd_not_unit a (minpoly A x)) :
  polynomial.aeval x a ≠ 0 :=
begin
  intro ha,
  refine not_lt_of_ge (minpoly.min A x hamonic ha) _,
  obtain ⟨hzeroa, b, hb_nunit, prod⟩ := hdvd,
  have hbmonic : b.monic,
  { rw monic.def,
    have := monic hx,
    rwa [monic.def, prod, leading_coeff_mul, monic.def.mp hamonic, one_mul] at this },
  have hzerob : b ≠ 0 := hbmonic.ne_zero,
  have degbzero : 0 < b.nat_degree,
  { apply nat.pos_of_ne_zero,
    intro h,
    have h₁ := eq_C_of_nat_degree_eq_zero h,
    rw [←h, ←leading_coeff, monic.def.1 hbmonic, C_1] at h₁,
    rw h₁ at hb_nunit,
    have := is_unit_one,
    contradiction },
  rw [prod, degree_mul, degree_eq_nat_degree hzeroa, degree_eq_nat_degree hzerob],
  exact_mod_cast lt_add_of_pos_right _ degbzero,
end

variables [is_domain B]

/-- A minimal polynomial is irreducible. -/
lemma irreducible (hx : is_integral A x) : irreducible (minpoly A x) :=
begin
  cases irreducible_or_factor (minpoly A x) (not_is_unit A x) with hirr hred,
  { exact hirr },
  exfalso,
  obtain ⟨a, b, ha_nunit, hb_nunit, hab_eq⟩ := hred,
  have coeff_prod : a.leading_coeff * b.leading_coeff = 1,
  { rw [←monic.def.1 (monic hx), ←hab_eq],
    simp only [leading_coeff_mul] },
  have hamonic : (a * C b.leading_coeff).monic,
  { rw monic.def,
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C] },
  have hbmonic : (b * C a.leading_coeff).monic,
  { rw [monic.def, mul_comm],
    simp only [coeff_prod, leading_coeff_mul, leading_coeff_C] },
  have prod : minpoly A x = (a * C b.leading_coeff) * (b * C a.leading_coeff),
  { symmetry,
    calc a * C b.leading_coeff * (b * C a.leading_coeff)
        = a * b * (C a.leading_coeff * C b.leading_coeff) : by ring
    ... = a * b * (C (a.leading_coeff * b.leading_coeff)) : by simp only [ring_hom.map_mul]
    ... = a * b : by rw [coeff_prod, C_1, mul_one]
    ... = minpoly A x : hab_eq },
  have hzero := aeval A x,
  rw [prod, aeval_mul, mul_eq_zero] at hzero,
  cases hzero,
  { refine aeval_ne_zero_of_dvd_not_unit_minpoly hx hamonic _ hzero,
    exact ⟨hamonic.ne_zero, _, mt is_unit_of_mul_is_unit_left hb_nunit, prod⟩ },
  { refine aeval_ne_zero_of_dvd_not_unit_minpoly hx hbmonic _ hzero,
    rw mul_comm at prod,
    exact ⟨hbmonic.ne_zero, _, mt is_unit_of_mul_is_unit_left ha_nunit, prod⟩ },
end

end is_domain

end comm_ring

section field
variables [field A]

section ring
variables [ring B] [algebra A B]
variables {x : B}

variables (A x)

/-- If an element `x` is a root of a nonzero polynomial `p`,
then the degree of `p` is at least the degree of the minimal polynomial of `x`. -/
lemma degree_le_of_ne_zero
  {p : A[X]} (pnz : p ≠ 0) (hp : polynomial.aeval x p = 0) :
  degree (minpoly A x) ≤ degree p :=
calc degree (minpoly A x) ≤ degree (p * C (leading_coeff p)⁻¹) :
    min A x (monic_mul_leading_coeff_inv pnz) (by simp [hp])
  ... = degree p : degree_mul_leading_coeff_inv p pnz

/-- The minimal polynomial of an element `x` is uniquely characterized by its defining property:
if there is another monic polynomial of minimal degree that has `x` as a root,
then this polynomial is equal to the minimal polynomial of `x`. -/
lemma unique {p : A[X]}
  (pmonic : p.monic) (hp : polynomial.aeval x p = 0)
  (pmin : ∀ q : A[X], q.monic → polynomial.aeval x q = 0 → degree p ≤ degree q) :
  p = minpoly A x :=
begin
  have hx : is_integral A x := ⟨p, pmonic, hp⟩,
  symmetry, apply eq_of_sub_eq_zero,
  by_contra hnz,
  have := degree_le_of_ne_zero A x hnz (by simp [hp]),
  contrapose! this,
  apply degree_sub_lt _ (ne_zero hx),
  { rw [(monic hx).leading_coeff, pmonic.leading_coeff] },
  { exact le_antisymm (min A x pmonic hp)
      (pmin (minpoly A x) (monic hx) (aeval A x)) }
end

/-- If an element `x` is a root of a polynomial `p`,
then the minimal polynomial of `x` divides `p`. -/
lemma dvd {p : A[X]} (hp : polynomial.aeval x p = 0) : minpoly A x ∣ p :=
begin
  by_cases hp0 : p = 0,
  { simp only [hp0, dvd_zero] },
  have hx : is_integral A x,
  { rw ← is_algebraic_iff_is_integral, exact ⟨p, hp0, hp⟩ },
  rw ← dvd_iff_mod_by_monic_eq_zero (monic hx),
  by_contra hnz,
  have := degree_le_of_ne_zero A x hnz _,
  { contrapose! this,
    exact degree_mod_by_monic_lt _ (monic hx) },
  { rw ← mod_by_monic_add_div p (monic hx) at hp,
    simpa using hp }
end

lemma dvd_map_of_is_scalar_tower (A K : Type*) {R : Type*} [comm_ring A] [field K] [comm_ring R]
  [algebra A K] [algebra A R] [algebra K R] [is_scalar_tower A K R] (x : R) :
  minpoly K x ∣ (minpoly A x).map (algebra_map A K) :=
by { refine minpoly.dvd K x _, rw [← is_scalar_tower.aeval_apply, minpoly.aeval] }

/-- If `y` is a conjugate of `x` over a field `K`, then it is a conjugate over a subring `R`. -/
lemma aeval_of_is_scalar_tower (R : Type*) {K T U : Type*} [comm_ring R] [field K] [comm_ring T]
  [algebra R K] [algebra K T] [algebra R T] [is_scalar_tower R K T]
  [comm_semiring U] [algebra K U] [algebra R U] [is_scalar_tower R K U]
  (x : T) (y : U)
  (hy : polynomial.aeval y (minpoly K x) = 0) : polynomial.aeval y (minpoly R x) = 0 :=
by { rw is_scalar_tower.aeval_apply R K,
     exact eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (algebra_map K U) y
        (minpoly.dvd_map_of_is_scalar_tower R K x) hy }

variables {A x}

theorem eq_of_irreducible_of_monic
  [nontrivial B] {p : A[X]} (hp1 : _root_.irreducible p)
  (hp2 : polynomial.aeval x p = 0) (hp3 : p.monic) : p = minpoly A x :=
let ⟨q, hq⟩ := dvd A x hp2 in
eq_of_monic_of_associated hp3 (monic ⟨p, ⟨hp3, hp2⟩⟩) $
mul_one (minpoly A x) ▸ hq.symm ▸ associated.mul_left _ $
associated_one_iff_is_unit.2 $ (hp1.is_unit_or_is_unit hq).resolve_left $ not_is_unit A x

lemma eq_of_irreducible [nontrivial B] {p : A[X]}
  (hp1 : _root_.irreducible p) (hp2 : polynomial.aeval x p = 0) :
  p * C p.leading_coeff⁻¹ = minpoly A x :=
begin
  have : p.leading_coeff ≠ 0 := leading_coeff_ne_zero.mpr hp1.ne_zero,
  apply eq_of_irreducible_of_monic,
  { exact associated.irreducible ⟨⟨C p.leading_coeff⁻¹, C p.leading_coeff,
      by rwa [←C_mul, inv_mul_cancel, C_1], by rwa [←C_mul, mul_inv_cancel, C_1]⟩, rfl⟩ hp1 },
  { rw [aeval_mul, hp2, zero_mul] },
  { rwa [polynomial.monic, leading_coeff_mul, leading_coeff_C, mul_inv_cancel] },
end

/-- If `y` is the image of `x` in an extension, their minimal polynomials coincide.

We take `h : y = algebra_map L T x` as an argument because `rw h` typically fails
since `is_integral R y` depends on y.
-/
lemma eq_of_algebra_map_eq {K S T : Type*} [field K] [comm_ring S] [comm_ring T]
  [algebra K S] [algebra K T] [algebra S T]
  [is_scalar_tower K S T] (hST : function.injective (algebra_map S T))
  {x : S} {y : T} (hx : is_integral K x) (h : y = algebra_map S T x) :
  minpoly K x = minpoly K y :=
minpoly.unique _ _ (minpoly.monic hx)
  (by rw [h, ← is_scalar_tower.algebra_map_aeval, minpoly.aeval, ring_hom.map_zero])
  (λ q q_monic root_q, minpoly.min _ _ q_monic
    (is_scalar_tower.aeval_eq_zero_of_aeval_algebra_map_eq_zero K S T hST
      (h ▸ root_q : polynomial.aeval (algebra_map S T x) q = 0)))

section gcd_domain

/-- For GCD domains, the minimal polynomial over the ring is the same as the minimal polynomial
over the fraction field. -/
lemma gcd_domain_eq_field_fractions {A R : Type*} (K : Type*) [comm_ring A] [is_domain A]
  [normalized_gcd_monoid A] [field K]
  [comm_ring R] [is_domain R] [algebra A K] [is_fraction_ring A K]
  [algebra K R] [algebra A R] [is_scalar_tower A K R] {x : R} (hx : is_integral A x) :
  minpoly K x = (minpoly A x).map (algebra_map A K) :=
begin
  symmetry,
  refine eq_of_irreducible_of_monic _ _ _,
  { exact (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map
      (polynomial.monic.is_primitive (monic hx))).1 (irreducible hx) },
  { have htower := is_scalar_tower.aeval_apply A K R x (minpoly A x),
    rwa [aeval, eq_comm] at htower },
  { exact monic_map _ (monic hx) }
end

/-- For GCD domains, the minimal polynomial divides any primitive polynomial that has the integral
element as root. -/
lemma gcd_domain_dvd {A R : Type*} (K : Type*)
  [comm_ring A] [is_domain A] [normalized_gcd_monoid A] [field K]
  [comm_ring R] [is_domain R] [algebra A K]
  [is_fraction_ring A K] [algebra K R] [algebra A R] [is_scalar_tower A K R]
  {x : R} (hx : is_integral A x)
  {P : A[X]} (hprim : is_primitive P) (hroot : polynomial.aeval x P = 0) :
  minpoly A x ∣ P :=
begin
  apply (is_primitive.dvd_iff_fraction_map_dvd_fraction_map K
    (monic.is_primitive (monic hx)) hprim).2,
  rw ← gcd_domain_eq_field_fractions K hx,
  refine dvd _ _ _,
  rwa ← is_scalar_tower.aeval_apply
end

end gcd_domain

variables (B) [nontrivial B]

/-- If `B/K` is a nontrivial algebra over a field, and `x` is an element of `K`,
then the minimal polynomial of `algebra_map K B x` is `X - C x`. -/
lemma eq_X_sub_C (a : A) : minpoly A (algebra_map A B a) = X - C a :=
eq_X_sub_C_of_algebra_map_inj a (algebra_map A B).injective

lemma eq_X_sub_C' (a : A) : minpoly A a = X - C a := eq_X_sub_C A a

variables (A)

/-- The minimal polynomial of `0` is `X`. -/
@[simp] lemma zero : minpoly A (0:B) = X :=
by simpa only [add_zero, C_0, sub_eq_add_neg, neg_zero, ring_hom.map_zero]
  using eq_X_sub_C B (0:A)

/-- The minimal polynomial of `1` is `X - 1`. -/
@[simp] lemma one : minpoly A (1:B) = X - 1 :=
by simpa only [ring_hom.map_one, C_1, sub_eq_add_neg] using eq_X_sub_C B (1:A)

end ring

section is_domain
variables [ring B] [is_domain B] [algebra A B]
variables {x : B}

/-- A minimal polynomial is prime. -/
lemma prime (hx : is_integral A x) : prime (minpoly A x) :=
begin
  refine ⟨ne_zero hx, not_is_unit A x, _⟩,
  rintros p q ⟨d, h⟩,
  have :    polynomial.aeval x (p*q) = 0 := by simp [h, aeval A x],
  replace : polynomial.aeval x p = 0 ∨ polynomial.aeval x q = 0 := by simpa,
  exact or.imp (dvd A x) (dvd A x) this
end

/-- If `L/K` is a field extension and an element `y` of `K` is a root of the minimal polynomial
of an element `x ∈ L`, then `y` maps to `x` under the field embedding. -/
lemma root {x : B} (hx : is_integral A x) {y : A} (h : is_root (minpoly A x) y) :
  algebra_map A B y = x :=
have key : minpoly A x = X - C y :=
eq_of_monic_of_associated (monic hx) (monic_X_sub_C y) (associated_of_dvd_dvd
  ((irreducible_X_sub_C y).dvd_symm (irreducible hx) (dvd_iff_is_root.2 h))
  (dvd_iff_is_root.2 h)),
by { have := aeval A x, rwa [key, alg_hom.map_sub, aeval_X, aeval_C, sub_eq_zero, eq_comm] at this }

/-- The constant coefficient of the minimal polynomial of `x` is `0` if and only if `x = 0`. -/
@[simp] lemma coeff_zero_eq_zero (hx : is_integral A x) : coeff (minpoly A x) 0 = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have zero_root := zero_is_root_of_coeff_zero_eq_zero h,
    rw ← root hx zero_root,
    exact ring_hom.map_zero _ },
  { rintro rfl, simp }
end

/-- The minimal polynomial of a nonzero element has nonzero constant coefficient. -/
lemma coeff_zero_ne_zero (hx : is_integral A x) (h : x ≠ 0) : coeff (minpoly A x) 0 ≠ 0 :=
by { contrapose! h, simpa only [hx, coeff_zero_eq_zero] using h }

end is_domain

end field

end minpoly
