/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import algebra.polynomial.big_operators
import analysis.complex.roots_of_unity
import data.polynomial.lifts
import field_theory.separable
import field_theory.splitting_field
import number_theory.arithmetic_function
import ring_theory.roots_of_unity
import field_theory.ratfunc
import algebra.ne_zero

/-!
# Cyclotomic polynomials.

For `n : ℕ` and an integral domain `R`, we define a modified version of the `n`-th cyclotomic
polynomial with coefficients in `R`, denoted `cyclotomic' n R`, as `∏ (X - μ)`, where `μ` varies
over the primitive `n`th roots of unity. If there is a primitive `n`th root of unity in `R` then
this the standard definition. We then define the standard cyclotomic polynomial `cyclotomic n R`
with coefficients in any ring `R`.

## Main definition

* `cyclotomic n R` : the `n`-th cyclotomic polynomial with coefficients in `R`.

## Main results

* `int_coeff_of_cycl` : If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K`
comes from a polynomial with integer coefficients.
* `deg_of_cyclotomic` : The degree of `cyclotomic n` is `totient n`.
* `prod_cyclotomic_eq_X_pow_sub_one` : `X ^ n - 1 = ∏ (cyclotomic i)`, where `i` divides `n`.
* `cyclotomic_eq_prod_X_pow_sub_one_pow_moebius` : The Möbius inversion formula for
  `cyclotomic n R` over an abstract fraction field for `polynomial R`.
* `cyclotomic.irreducible` : `cyclotomic n ℤ` is irreducible.

## Implementation details

Our definition of `cyclotomic' n R` makes sense in any integral domain `R`, but the interesting
results hold if there is a primitive `n`-th root of unity in `R`. In particular, our definition is
not the standard one unless there is a primitive `n`th root of unity in `R`. For example,
`cyclotomic' 3 ℤ = 1`, since there are no primitive cube roots of unity in `ℤ`. The main example is
`R = ℂ`, we decided to work in general since the difficulties are essentially the same.
To get the standard cyclotomic polynomials, we use `int_coeff_of_cycl`, with `R = ℂ`, to get a
polynomial with integer coefficients and then we map it to `polynomial R`, for any ring `R`.
To prove `cyclotomic.irreducible`, the irreducibility of `cyclotomic n ℤ`, we show in
`cyclotomic_eq_minpoly` that `cyclotomic n ℤ` is the minimal polynomial of any `n`-th primitive root
of unity `μ : K`, where `K` is a field of characteristic `0`.
-/

open_locale classical big_operators polynomial
noncomputable theory

universe u

namespace polynomial

section cyclotomic'

section is_domain

variables {R : Type*} [comm_ring R] [is_domain R]

/-- The modified `n`-th cyclotomic polynomial with coefficients in `R`, it is the usual cyclotomic
polynomial if there is a primitive `n`-th root of unity in `R`. -/
def cyclotomic' (n : ℕ) (R : Type*) [comm_ring R] [is_domain R] : R[X] :=
∏ μ in primitive_roots n R, (X - C μ)

/-- The zeroth modified cyclotomic polyomial is `1`. -/
@[simp] lemma cyclotomic'_zero
  (R : Type*) [comm_ring R] [is_domain R] : cyclotomic' 0 R = 1 :=
by simp only [cyclotomic', finset.prod_empty, is_primitive_root.primitive_roots_zero]

/-- The first modified cyclotomic polyomial is `X - 1`. -/
@[simp] lemma cyclotomic'_one
  (R : Type*) [comm_ring R] [is_domain R] : cyclotomic' 1 R = X - 1 :=
begin
  simp only [cyclotomic', finset.prod_singleton, ring_hom.map_one,
  is_primitive_root.primitive_roots_one]
end

/-- The second modified cyclotomic polyomial is `X + 1` if the characteristic of `R` is not `2`. -/
@[simp] lemma cyclotomic'_two
  (R : Type*) [comm_ring R] [is_domain R] (p : ℕ) [char_p R p] (hp : p ≠ 2) :
  cyclotomic' 2 R = X + 1 :=
begin
  rw [cyclotomic'],
  have prim_root_two : primitive_roots 2 R = {(-1 : R)},
  { apply finset.eq_singleton_iff_unique_mem.2,
    split,
    { simp only [is_primitive_root.neg_one p hp, nat.succ_pos', mem_primitive_roots] },
    { intros x hx,
      rw [mem_primitive_roots zero_lt_two] at hx,
      exact is_primitive_root.eq_neg_one_of_two_right hx } },
  simp only [prim_root_two, finset.prod_singleton, ring_hom.map_neg, ring_hom.map_one,
  sub_neg_eq_add]
end

/-- `cyclotomic' n R` is monic. -/
lemma cyclotomic'.monic
  (n : ℕ) (R : Type*) [comm_ring R] [is_domain R] : (cyclotomic' n R).monic :=
monic_prod_of_monic _ _ $ λ z hz, monic_X_sub_C _

/-- `cyclotomic' n R` is different from `0`. -/
lemma cyclotomic'_ne_zero
  (n : ℕ) (R : Type*) [comm_ring R] [is_domain R] : cyclotomic' n R ≠ 0 :=
(cyclotomic'.monic n R).ne_zero

/-- The natural degree of `cyclotomic' n R` is `totient n` if there is a primitive root of
unity in `R`. -/
lemma nat_degree_cyclotomic' {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) :
  (cyclotomic' n R).nat_degree = nat.totient n :=
begin
  rw [cyclotomic'],
  rw nat_degree_prod (primitive_roots n R) (λ (z : R), (X - C z)),
  simp only [is_primitive_root.card_primitive_roots h, mul_one,
  nat_degree_X_sub_C,
  nat.cast_id, finset.sum_const, nsmul_eq_mul],
  intros z hz,
  exact X_sub_C_ne_zero z
end

/-- The degree of `cyclotomic' n R` is `totient n` if there is a primitive root of unity in `R`. -/
lemma degree_cyclotomic' {ζ : R} {n : ℕ} (h : is_primitive_root ζ n) :
  (cyclotomic' n R).degree = nat.totient n :=
by simp only [degree_eq_nat_degree (cyclotomic'_ne_zero n R), nat_degree_cyclotomic' h]

/-- The roots of `cyclotomic' n R` are the primitive `n`-th roots of unity. -/
lemma roots_of_cyclotomic (n : ℕ) (R : Type*) [comm_ring R] [is_domain R] :
  (cyclotomic' n R).roots = (primitive_roots n R).val :=
by { rw cyclotomic', exact roots_prod_X_sub_C (primitive_roots n R) }

/-- If there is a primitive `n`th root of unity in `K`, then `X ^ n - 1 = ∏ (X - μ)`, where `μ`
varies over the `n`-th roots of unity. -/
lemma X_pow_sub_one_eq_prod {ζ : R} {n : ℕ} (hpos : 0 < n) (h : is_primitive_root ζ n) :
  X ^ n - 1 = ∏ ζ in nth_roots_finset n R, (X - C ζ) :=
begin
  rw [nth_roots_finset, ← multiset.to_finset_eq (is_primitive_root.nth_roots_nodup h)],
  simp only [finset.prod_mk, ring_hom.map_one],
  rw [nth_roots],
  have hmonic : (X ^ n - C (1 : R)).monic := monic_X_pow_sub_C (1 : R) (ne_of_lt hpos).symm,
  symmetry,
  apply prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic,
  rw [@nat_degree_X_pow_sub_C R _ _ n 1, ← nth_roots],
  exact is_primitive_root.card_nth_roots h
end

end is_domain

section field

variables {K : Type*} [field K]

/-- `cyclotomic' n K` splits. -/
lemma cyclotomic'_splits (n : ℕ) : splits (ring_hom.id K) (cyclotomic' n K) :=
begin
  apply splits_prod (ring_hom.id K),
  intros z hz,
  simp only [splits_X_sub_C (ring_hom.id K)]
end

/-- If there is a primitive `n`-th root of unity in `K`, then `X ^ n - 1`splits. -/
lemma X_pow_sub_one_splits {ζ : K} {n : ℕ} (h : is_primitive_root ζ n) :
  splits (ring_hom.id K) (X ^ n - C (1 : K)) :=
by rw [splits_iff_card_roots, ← nth_roots, is_primitive_root.card_nth_roots h,
    nat_degree_X_pow_sub_C]

/-- If there is a primitive `n`-th root of unity in `K`, then
`∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1`. -/
lemma prod_cyclotomic'_eq_X_pow_sub_one {K : Type*} [comm_ring K] [is_domain K] {ζ : K} {n : ℕ}
  (hpos : 0 < n) (h : is_primitive_root ζ n) : ∏ i in nat.divisors n, cyclotomic' i K = X ^ n - 1 :=
begin
  rw [X_pow_sub_one_eq_prod hpos h],
  have rwcyc : ∀ i ∈ nat.divisors n, cyclotomic' i K = ∏ μ in primitive_roots i K, (X - C μ),
  { intros i hi,
    simp only [cyclotomic'] },
  conv_lhs { apply_congr,
             skip,
             simp [rwcyc, H] },
  rw ← finset.prod_bUnion,
  { simp only [is_primitive_root.nth_roots_one_eq_bUnion_primitive_roots h] },
  intros x hx y hy hdiff,
  exact is_primitive_root.disjoint hdiff,
end

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic' n K = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic' i K)`. -/
lemma cyclotomic'_eq_X_pow_sub_one_div {K : Type*} [comm_ring K] [is_domain K] {ζ : K} {n : ℕ}
  (hpos : 0 < n) (h : is_primitive_root ζ n) :
  cyclotomic' n K = (X ^ n - 1) /ₘ (∏ i in nat.proper_divisors n, cyclotomic' i K) :=
begin
  rw [←prod_cyclotomic'_eq_X_pow_sub_one hpos h,
  nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
  finset.prod_insert nat.proper_divisors.not_self_mem],
  have prod_monic : (∏ i in nat.proper_divisors n, cyclotomic' i K).monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact cyclotomic'.monic i K },
  rw (div_mod_by_monic_unique (cyclotomic' n K) 0 prod_monic _).1,
  simp only [degree_zero, zero_add],
  refine ⟨by rw mul_comm, _⟩,
  rw [bot_lt_iff_ne_bot],
  intro h,
  exact monic.ne_zero prod_monic (degree_eq_bot.1 h)
end

/-- If there is a primitive `n`-th root of unity in `K`, then `cyclotomic' n K` comes from a
monic polynomial with integer coefficients. -/
lemma int_coeff_of_cyclotomic' {K : Type*} [comm_ring K] [is_domain K] {ζ : K} {n : ℕ}
  (h : is_primitive_root ζ n) :
  (∃ (P : ℤ[X]), map (int.cast_ring_hom K) P = cyclotomic' n K ∧
    P.degree = (cyclotomic' n K).degree ∧ P.monic) :=
begin
  refine lifts_and_degree_eq_and_monic _ (cyclotomic'.monic n K),
  induction n using nat.strong_induction_on with k hk generalizing ζ h,
  cases nat.eq_zero_or_pos k with hzero hpos,
  { use 1,
    simp only [hzero, cyclotomic'_zero, set.mem_univ, subsemiring.coe_top, eq_self_iff_true,
    coe_map_ring_hom, map_one, and_self] },
  let B : K[X] := ∏ i in nat.proper_divisors k, cyclotomic' i K,
  have Bmo : B.monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact (cyclotomic'.monic i K) },
  have Bint : B ∈ lifts (int.cast_ring_hom K),
  { refine subsemiring.prod_mem (lifts (int.cast_ring_hom K)) _,
    intros x hx,
    have xsmall := (nat.mem_proper_divisors.1 hx).2,
    obtain ⟨d, hd⟩ := (nat.mem_proper_divisors.1 hx).1,
    rw [mul_comm] at hd,
    exact hk x xsmall (is_primitive_root.pow hpos h hd) },
  replace Bint := lifts_and_degree_eq_and_monic Bint Bmo,
  obtain ⟨B₁, hB₁, hB₁deg, hB₁mo⟩ := Bint,
  let Q₁ : ℤ[X] := (X ^ k - 1) /ₘ B₁,
  have huniq : 0 + B * cyclotomic' k K = X ^ k - 1 ∧ (0 : K[X]).degree < B.degree,
  { split,
    { rw [zero_add, mul_comm, ←(prod_cyclotomic'_eq_X_pow_sub_one hpos h),
      nat.divisors_eq_proper_divisors_insert_self_of_pos hpos],
      simp only [true_and, finset.prod_insert, not_lt, nat.mem_proper_divisors, dvd_refl] },
    rw [degree_zero, bot_lt_iff_ne_bot],
    intro habs,
    exact (monic.ne_zero Bmo) (degree_eq_bot.1 habs) },
  replace huniq := div_mod_by_monic_unique (cyclotomic' k K) (0 : K[X]) Bmo huniq,
  simp only [lifts, ring_hom.mem_srange],
  use Q₁,
  rw [coe_map_ring_hom, (map_div_by_monic (int.cast_ring_hom K) hB₁mo), hB₁, ← huniq.1],
  simp
end

/-- If `K` is of characteristic `0` and there is a primitive `n`-th root of unity in `K`,
then `cyclotomic n K` comes from a unique polynomial with integer coefficients. -/
lemma unique_int_coeff_of_cycl {K : Type*} [comm_ring K] [is_domain K] [char_zero K] {ζ : K}
  {n : ℕ+} (h : is_primitive_root ζ n) :
  (∃! (P : ℤ[X]), map (int.cast_ring_hom K) P = cyclotomic' n K) :=
begin
  obtain ⟨P, hP⟩ := int_coeff_of_cyclotomic' h,
  refine ⟨P, hP.1, λ Q hQ, _⟩,
  apply (map_injective (int.cast_ring_hom K) int.cast_injective),
  rw [hP.1, hQ]
end

end field

end cyclotomic'

section cyclotomic

/-- The `n`-th cyclotomic polynomial with coefficients in `R`. -/
def cyclotomic (n : ℕ) (R : Type*) [ring R] : R[X] :=
if h : n = 0 then 1 else
  map (int.cast_ring_hom R) ((int_coeff_of_cyclotomic' (complex.is_primitive_root_exp n h)).some)

lemma int_cyclotomic_rw {n : ℕ} (h : n ≠ 0) :
  cyclotomic n ℤ = (int_coeff_of_cyclotomic' (complex.is_primitive_root_exp n h)).some :=
begin
  simp only [cyclotomic, h, dif_neg, not_false_iff],
  ext i,
  simp only [coeff_map, int.cast_id, ring_hom.eq_int_cast]
end

/-- `cyclotomic n R` comes from `cyclotomic n ℤ`. -/
lemma map_cyclotomic_int (n : ℕ) (R : Type*) [ring R] :
  map (int.cast_ring_hom R) (cyclotomic n ℤ) = cyclotomic n R :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, cyclotomic, dif_pos, map_one] },
  simp only [cyclotomic, int_cyclotomic_rw, hzero, ne.def, dif_neg, not_false_iff]
end

lemma int_cyclotomic_spec (n : ℕ) : map (int.cast_ring_hom ℂ) (cyclotomic n ℤ) = cyclotomic' n ℂ ∧
  (cyclotomic n ℤ).degree = (cyclotomic' n ℂ).degree ∧ (cyclotomic n ℤ).monic  :=
begin
  by_cases hzero : n = 0,
  { simp only [hzero, cyclotomic, degree_one, monic_one, cyclotomic'_zero, dif_pos,
  eq_self_iff_true, map_one, and_self] },
  rw int_cyclotomic_rw hzero,
  exact (int_coeff_of_cyclotomic' (complex.is_primitive_root_exp n hzero)).some_spec
end

lemma int_cyclotomic_unique {n : ℕ} {P : ℤ[X]} (h : map (int.cast_ring_hom ℂ) P =
  cyclotomic' n ℂ) : P = cyclotomic n ℤ :=
begin
  apply map_injective (int.cast_ring_hom ℂ) int.cast_injective,
  rw [h, (int_cyclotomic_spec n).1]
end

/-- The definition of `cyclotomic n R` commutes with any ring homomorphism. -/
@[simp] lemma map_cyclotomic (n : ℕ) {R S : Type*} [ring R] [ring S] (f : R →+* S) :
  map f (cyclotomic n R) = cyclotomic n S :=
begin
  rw [←map_cyclotomic_int n R, ←map_cyclotomic_int n S],
  ext i,
  simp only [coeff_map, ring_hom.eq_int_cast, ring_hom.map_int_cast]
end

/-- The zeroth cyclotomic polyomial is `1`. -/
@[simp] lemma cyclotomic_zero (R : Type*) [ring R] : cyclotomic 0 R = 1 :=
by simp only [cyclotomic, dif_pos]

/-- The first cyclotomic polyomial is `X - 1`. -/
@[simp] lemma cyclotomic_one (R : Type*) [ring R] : cyclotomic 1 R = X - 1 :=
begin
  have hspec : map (int.cast_ring_hom ℂ) (X - 1) = cyclotomic' 1 ℂ,
  { simp only [cyclotomic'_one, pnat.one_coe, map_X, map_one, map_sub] },
  symmetry,
  rw [←map_cyclotomic_int, ←(int_cyclotomic_unique hspec)],
  simp only [map_X, map_one, map_sub]
end

/-- The second cyclotomic polyomial is `X + 1`. -/
@[simp] lemma cyclotomic_two (R : Type*) [ring R] : cyclotomic 2 R = X + 1 :=
begin
  have hspec : map (int.cast_ring_hom ℂ) (X + 1) = cyclotomic' 2 ℂ,
  { simp only [cyclotomic'_two ℂ 0 two_ne_zero.symm, map_add, map_X, map_one] },
  symmetry,
  rw [←map_cyclotomic_int, ←(int_cyclotomic_unique hspec)],
  simp only [map_add, map_X, map_one]
end

/-- `cyclotomic n` is monic. -/
lemma cyclotomic.monic (n : ℕ) (R : Type*) [ring R] : (cyclotomic n R).monic :=
begin
  rw ←map_cyclotomic_int,
  apply monic_map,
  exact (int_cyclotomic_spec n).2.2
end

/-- `cyclotomic n` is primitive. -/
lemma cyclotomic.is_primitive (n : ℕ) (R : Type*) [comm_ring R] : (cyclotomic n R).is_primitive :=
(cyclotomic.monic n R).is_primitive

/-- `cyclotomic n R` is different from `0`. -/
lemma cyclotomic_ne_zero (n : ℕ) (R : Type*) [ring R] [nontrivial R] : cyclotomic n R ≠ 0 :=
monic.ne_zero (cyclotomic.monic n R)

/-- The degree of `cyclotomic n` is `totient n`. -/
lemma degree_cyclotomic (n : ℕ) (R : Type*) [ring R] [nontrivial R] :
  (cyclotomic n R).degree = nat.totient n :=
begin
  rw ←map_cyclotomic_int,
  rw degree_map_eq_of_leading_coeff_ne_zero (int.cast_ring_hom R) _,
  { cases n with k,
    { simp only [cyclotomic, degree_one, dif_pos, nat.totient_zero, with_top.coe_zero]},
      rw [←degree_cyclotomic' (complex.is_primitive_root_exp k.succ (nat.succ_ne_zero k))],
      exact (int_cyclotomic_spec k.succ).2.1 },
  simp only [(int_cyclotomic_spec n).right.right, ring_hom.eq_int_cast, monic.leading_coeff,
  int.cast_one, ne.def, not_false_iff, one_ne_zero]
end

/-- The natural degree of `cyclotomic n` is `totient n`. -/
lemma nat_degree_cyclotomic (n : ℕ) (R : Type*) [ring R] [nontrivial R] :
  (cyclotomic n R).nat_degree = nat.totient n :=
begin
  have hdeg := degree_cyclotomic n R,
  rw degree_eq_nat_degree (cyclotomic_ne_zero n R) at hdeg,
  exact_mod_cast hdeg
end

/-- The degree of `cyclotomic n R` is positive. -/
lemma degree_cyclotomic_pos (n : ℕ) (R : Type*) (hpos : 0 < n) [ring R] [nontrivial R] :
  0 < (cyclotomic n R).degree := by
{ rw degree_cyclotomic n R, exact_mod_cast (nat.totient_pos hpos) }

/-- `∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1`. -/
lemma prod_cyclotomic_eq_X_pow_sub_one {n : ℕ} (hpos : 0 < n) (R : Type*) [comm_ring R] :
  ∏ i in nat.divisors n, cyclotomic i R = X ^ n - 1 :=
begin
  have integer : ∏ i in nat.divisors n, cyclotomic i ℤ = X ^ n - 1,
  { apply map_injective (int.cast_ring_hom ℂ) int.cast_injective,
    rw map_prod (int.cast_ring_hom ℂ) (λ i, cyclotomic i ℤ),
    simp only [int_cyclotomic_spec, polynomial.map_pow, nat.cast_id, map_X, map_one, map_sub],
    exact prod_cyclotomic'_eq_X_pow_sub_one hpos
          (complex.is_primitive_root_exp n (ne_of_lt hpos).symm) },
  have coerc : X ^ n - 1 = map (int.cast_ring_hom R) (X ^ n - 1),
  { simp only [polynomial.map_pow, polynomial.map_X, polynomial.map_one, polynomial.map_sub] },
  have h : ∀ i ∈ n.divisors, cyclotomic i R = map (int.cast_ring_hom R) (cyclotomic i ℤ),
  { intros i hi,
    exact (map_cyclotomic_int i R).symm },
  rw [finset.prod_congr (refl n.divisors) h, coerc, ←map_prod (int.cast_ring_hom R)
                                                    (λ i, cyclotomic i ℤ), integer]
end

lemma cyclotomic.dvd_X_pow_sub_one (n : ℕ) (R : Type*) [comm_ring R] :
  (cyclotomic n R) ∣ X ^ n - 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { simp },
  refine ⟨∏ i in n.proper_divisors, cyclotomic i R, _⟩,
  rw [←prod_cyclotomic_eq_X_pow_sub_one hn,
      nat.divisors_eq_proper_divisors_insert_self_of_pos hn, finset.prod_insert],
  exact nat.proper_divisors.not_self_mem
end

lemma prod_cyclotomic_eq_geom_sum {n : ℕ} (h : 0 < n) (R) [comm_ring R] [is_domain R] :
  ∏ i in n.divisors \ {1}, cyclotomic i R = geom_sum X n :=
begin
  apply_fun (* cyclotomic 1 R) using mul_left_injective₀ (cyclotomic_ne_zero 1 R),
  have : ∏ i in {1}, cyclotomic i R = cyclotomic 1 R := finset.prod_singleton,
  simp_rw [←this, finset.prod_sdiff $ show {1} ⊆ n.divisors, by simp [h.ne'], this, cyclotomic_one,
           geom_sum_mul, prod_cyclotomic_eq_X_pow_sub_one h]
end

lemma _root_.is_root_of_unity_iff {n : ℕ} (h : 0 < n) (R : Type*) [comm_ring R] [is_domain R]
  {ζ : R} : ζ ^ n = 1 ↔ ∃ i ∈ n.divisors, (cyclotomic i R).is_root ζ :=
by rw [←mem_nth_roots h, nth_roots, mem_roots $ X_pow_sub_C_ne_zero h _,
       C_1, ←prod_cyclotomic_eq_X_pow_sub_one h, is_root_prod]; apply_instance

lemma is_root_of_unity_of_root_cyclotomic {n : ℕ} {R} [comm_ring R] {ζ : R} {i : ℕ}
  (hi : i ∈ n.divisors) (h : (cyclotomic i R).is_root ζ) : ζ ^ n = 1 :=
begin
  rcases n.eq_zero_or_pos with rfl | hn,
  { exact pow_zero _ },
  have := congr_arg (eval ζ) (prod_cyclotomic_eq_X_pow_sub_one hn R).symm,
  rw [eval_sub, eval_pow, eval_X, eval_one] at this,
  convert eq_add_of_sub_eq' this,
  convert (add_zero _).symm,
  apply eval_eq_zero_of_dvd_of_eval_eq_zero _ h,
  exact finset.dvd_prod_of_mem _ hi
end

section arithmetic_function
open nat.arithmetic_function
open_locale arithmetic_function

/-- `cyclotomic n R` can be expressed as a product in a fraction field of `polynomial R`
  using Möbius inversion. -/
lemma cyclotomic_eq_prod_X_pow_sub_one_pow_moebius {n : ℕ} (R : Type*) [comm_ring R] [is_domain R] :
  algebra_map _ (ratfunc R) (cyclotomic n R) =
    ∏ i in n.divisors_antidiagonal, (algebra_map R[X] _ (X ^ i.snd - 1)) ^ μ i.fst :=
begin
  rcases n.eq_zero_or_pos with rfl | hpos,
  { simp },
  have h : ∀ (n : ℕ), 0 < n →
    ∏ i in nat.divisors n, algebra_map _ (ratfunc R) (cyclotomic i R) = algebra_map _ _ (X ^ n - 1),
  { intros n hn,
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn R, ring_hom.map_prod] },
  rw (prod_eq_iff_prod_pow_moebius_eq_of_nonzero (λ n hn, _) (λ n hn, _)).1 h n hpos;
  rw [ne.def, is_fraction_ring.to_map_eq_zero_iff],
  { apply cyclotomic_ne_zero },
  { apply monic.ne_zero,
    apply monic_X_pow_sub_C _ (ne_of_gt hn) }
end

end arithmetic_function

/-- We have
`cyclotomic n R = (X ^ k - 1) /ₘ (∏ i in nat.proper_divisors k, cyclotomic i K)`. -/
lemma cyclotomic_eq_X_pow_sub_one_div {R : Type*} [comm_ring R] {n : ℕ}
  (hpos: 0 < n) : cyclotomic n R = (X ^ n - 1) /ₘ (∏ i in nat.proper_divisors n, cyclotomic i R) :=
begin
  nontriviality R,
  rw [←prod_cyclotomic_eq_X_pow_sub_one hpos,
  nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
  finset.prod_insert nat.proper_divisors.not_self_mem],
  have prod_monic : (∏ i in nat.proper_divisors n, cyclotomic i R).monic,
  { apply monic_prod_of_monic,
    intros i hi,
    exact cyclotomic.monic i R },
  rw (div_mod_by_monic_unique (cyclotomic n R) 0 prod_monic _).1,
  simp only [degree_zero, zero_add],
  split,
  { rw mul_comm },
  rw [bot_lt_iff_ne_bot],
  intro h,
  exact monic.ne_zero prod_monic (degree_eq_bot.1 h)
end

/-- If `m` is a proper divisor of `n`, then `X ^ m - 1` divides
`∏ i in nat.proper_divisors n, cyclotomic i R`. -/
lemma X_pow_sub_one_dvd_prod_cyclotomic (R : Type*) [comm_ring R] {n m : ℕ} (hpos : 0 < n)
  (hm : m ∣ n) (hdiff : m ≠ n) : X ^ m - 1 ∣ ∏ i in nat.proper_divisors n, cyclotomic i R :=
begin
  replace hm := nat.mem_proper_divisors.2 ⟨hm, lt_of_le_of_ne (nat.divisor_le (nat.mem_divisors.2
    ⟨hm, (ne_of_lt hpos).symm⟩)) hdiff⟩,
  rw [← finset.sdiff_union_of_subset (nat.divisors_subset_proper_divisors (ne_of_lt hpos).symm
    (nat.mem_proper_divisors.1 hm).1 (ne_of_lt (nat.mem_proper_divisors.1 hm).2)),
    finset.prod_union finset.sdiff_disjoint, prod_cyclotomic_eq_X_pow_sub_one
    (nat.pos_of_mem_proper_divisors hm)],
  exact ⟨(∏ (x : ℕ) in n.proper_divisors \ m.divisors, cyclotomic x R), by rw mul_comm⟩
end

/-- If there is a primitive `n`-th root of unity in `K`, then
`cyclotomic n K = ∏ μ in primitive_roots n R, (X - C μ)`. In particular,
`cyclotomic n K = cyclotomic' n K` -/
lemma cyclotomic_eq_prod_X_sub_primitive_roots {K : Type*} [comm_ring K] [is_domain K] {ζ : K}
  {n : ℕ} (hz : is_primitive_root ζ n) :
  cyclotomic n K = ∏ μ in primitive_roots n K, (X - C μ) :=
begin
  rw ←cyclotomic',
  induction n using nat.strong_induction_on with k hk generalizing ζ hz,
  obtain hzero | hpos := k.eq_zero_or_pos,
  { simp only [hzero, cyclotomic'_zero, cyclotomic_zero] },
  have h : ∀ i ∈ k.proper_divisors, cyclotomic i K = cyclotomic' i K,
  { intros i hi,
    obtain ⟨d, hd⟩ := (nat.mem_proper_divisors.1 hi).1,
    rw mul_comm at hd,
    exact hk i (nat.mem_proper_divisors.1 hi).2 (is_primitive_root.pow hpos hz hd) },
  rw [@cyclotomic_eq_X_pow_sub_one_div _ _ _ hpos,
      cyclotomic'_eq_X_pow_sub_one_div hpos hz, finset.prod_congr (refl k.proper_divisors) h]
end

section roots

variables {R : Type*} {n : ℕ} [comm_ring R] [is_domain R]

/-- Any `n`-th primitive root of unity is a root of `cyclotomic n K`.-/
lemma is_root_cyclotomic (hpos : 0 < n) {μ : R} (h : is_primitive_root μ n) :
  is_root (cyclotomic n R) μ :=
begin
  rw [← mem_roots (cyclotomic_ne_zero n R),
      cyclotomic_eq_prod_X_sub_primitive_roots h, roots_prod_X_sub_C, ← finset.mem_def],
  rwa [← mem_primitive_roots hpos] at h,
end

private lemma is_root_cyclotomic_iff' {n : ℕ} {K : Type*} [field K] {μ : K} [ne_zero (n : K)] :
  is_root (cyclotomic n K) μ ↔ is_primitive_root μ n :=
begin
  -- in this proof, `o` stands for `order_of μ`
  have hnpos : 0 < n := (ne_zero.of_ne_zero_coe K).out.bot_lt,
  refine ⟨λ hμ, _, is_root_cyclotomic hnpos⟩,
  have hμn : μ ^ n = 1,
  { rw is_root_of_unity_iff hnpos,
    exact ⟨n, n.mem_divisors_self hnpos.ne', hμ⟩ },
  by_contra hnμ,
  have ho : 0 < order_of μ,
  { apply order_of_pos',
    rw is_of_fin_order_iff_pow_eq_one,
    exact ⟨n, hnpos, hμn⟩ },
  have := pow_order_of_eq_one μ,
  rw is_root_of_unity_iff ho at this,
  obtain ⟨i, hio, hiμ⟩ := this,
  replace hio := nat.dvd_of_mem_divisors hio,
  rw is_primitive_root.not_iff at hnμ,
  rw ←order_of_dvd_iff_pow_eq_one at hμn,
  have key  : i < n := (nat.le_of_dvd ho hio).trans_lt ((nat.le_of_dvd hnpos hμn).lt_of_ne hnμ),
  have key' : i ∣ n := hio.trans hμn,
  rw ←polynomial.dvd_iff_is_root at hμ hiμ,
  have hni : {i, n} ⊆ n.divisors,
  { simpa [finset.insert_subset, key'] using hnpos.ne' },
  obtain ⟨k, hk⟩ := hiμ,
  obtain ⟨j, hj⟩ := hμ,
  have := prod_cyclotomic_eq_X_pow_sub_one hnpos K,
  rw [←finset.prod_sdiff hni, finset.prod_pair key.ne, hk, hj] at this,
  have hn := (X_pow_sub_one_separable_iff.mpr $ ne_zero.ne' n K).squarefree,
  rw [←this, squarefree] at hn,
  contrapose! hn,
  refine ⟨X - C μ, ⟨(∏ x in n.divisors \ {i, n}, cyclotomic x K) * k * j, by ring⟩, _⟩,
  simp [polynomial.is_unit_iff_degree_eq_zero]
end

lemma is_root_cyclotomic_iff [ne_zero (n : R)] {μ : R} :
  is_root (cyclotomic n R) μ ↔ is_primitive_root μ n :=
begin
  have hf : function.injective _ := is_fraction_ring.injective R (fraction_ring R),
  haveI : ne_zero (n : fraction_ring R) := ne_zero.nat_of_injective hf,
  rw [←is_root_map_iff hf, ←is_primitive_root.map_iff_of_injective hf, map_cyclotomic,
      ←is_root_cyclotomic_iff']
end

lemma roots_cyclotomic_nodup [ne_zero (n : R)] : (cyclotomic n R).roots.nodup :=
begin
  obtain h | ⟨ζ, hζ⟩ := (cyclotomic n R).roots.empty_or_exists_mem,
  { exact h.symm ▸ multiset.nodup_zero },
  rw [mem_roots $ cyclotomic_ne_zero n R, is_root_cyclotomic_iff] at hζ,
  refine multiset.nodup_of_le (roots.le_of_dvd (X_pow_sub_C_ne_zero
    (ne_zero.pos_of_ne_zero_coe R) 1) $ cyclotomic.dvd_X_pow_sub_one n R) hζ.nth_roots_nodup,
end

lemma cyclotomic.roots_to_finset_eq_primitive_roots [ne_zero (n : R)] :
    (⟨(cyclotomic n R).roots, roots_cyclotomic_nodup⟩ : finset _) = primitive_roots n R :=
by { ext, simp [cyclotomic_ne_zero n R, is_root_cyclotomic_iff,
                mem_primitive_roots, ne_zero.pos_of_ne_zero_coe R] }

lemma cyclotomic.roots_eq_primitive_roots_val [ne_zero (n : R)] :
  (cyclotomic n R).roots = (primitive_roots n R).val :=
by rw ←cyclotomic.roots_to_finset_eq_primitive_roots

end roots

/-- If `R` is of characteristic zero, then `ζ` is a root of `cyclotomic n R` if and only if it is a
primitive `n`-th root of unity. -/
lemma is_root_cyclotomic_iff_char_zero {n : ℕ} {R : Type*} [comm_ring R] [is_domain R]
  [char_zero R] {μ : R} (hn : 0 < n) :
  (polynomial.cyclotomic n R).is_root μ ↔ is_primitive_root μ n :=
by { letI := ne_zero.of_gt hn, exact is_root_cyclotomic_iff }

/-- Over a ring `R` of characteristic zero, `λ n, cyclotomic n R` is injective. -/
lemma cyclotomic_injective {R : Type*} [comm_ring R] [char_zero R] :
  function.injective (λ n, cyclotomic n R) :=
begin
  intros n m hnm,
  simp only at hnm,
  rcases eq_or_ne n 0 with rfl | hzero,
  { rw [cyclotomic_zero] at hnm,
    replace hnm := congr_arg nat_degree hnm,
    rw [nat_degree_one, nat_degree_cyclotomic] at hnm,
    by_contra,
    exact (nat.totient_pos (zero_lt_iff.2 (ne.symm h))).ne hnm },
  { haveI := ne_zero.mk hzero,
    rw [← map_cyclotomic_int _ R, ← map_cyclotomic_int _ R] at hnm,
    replace hnm := map_injective (int.cast_ring_hom R) int.cast_injective hnm,
    replace hnm := congr_arg (map (int.cast_ring_hom ℂ)) hnm,
    rw [map_cyclotomic_int, map_cyclotomic_int] at hnm,
    have hprim := complex.is_primitive_root_exp _ hzero,
    have hroot := is_root_cyclotomic_iff.2 hprim,
    rw hnm at hroot,
    haveI hmzero : ne_zero m := ⟨λ h, by simpa [h] using hroot⟩,
    rw is_root_cyclotomic_iff at hroot,
    replace hprim := hprim.eq_order_of,
    rwa [← is_primitive_root.eq_order_of hroot] at hprim}
end

lemma eq_cyclotomic_iff {R : Type*} [comm_ring R] {n : ℕ} (hpos: 0 < n)
  (P : R[X]) :
  P = cyclotomic n R ↔ P * (∏ i in nat.proper_divisors n, polynomial.cyclotomic i R) = X ^ n - 1 :=
begin
  nontriviality R,
  refine ⟨λ hcycl, _, λ hP, _⟩,
  { rw [hcycl, ← finset.prod_insert (@nat.proper_divisors.not_self_mem n),
      ← nat.divisors_eq_proper_divisors_insert_self_of_pos hpos],
    exact prod_cyclotomic_eq_X_pow_sub_one hpos R },
  { have prod_monic : (∏ i in nat.proper_divisors n, cyclotomic i R).monic,
    { apply monic_prod_of_monic,
      intros i hi,
      exact cyclotomic.monic i R },
    rw [@cyclotomic_eq_X_pow_sub_one_div R _ _ hpos,
      (div_mod_by_monic_unique P 0 prod_monic _).1],
    refine ⟨by rwa [zero_add, mul_comm], _⟩,
    rw [degree_zero, bot_lt_iff_ne_bot],
    intro h,
    exact monic.ne_zero prod_monic (degree_eq_bot.1 h) },
end

/-- If `p` is prime, then `cyclotomic p R = geom_sum X p`. -/
lemma cyclotomic_eq_geom_sum {R : Type*} [comm_ring R] {p : ℕ}
  (hp : nat.prime p) : cyclotomic p R = geom_sum X p :=
begin
  refine ((eq_cyclotomic_iff hp.pos _).mpr _).symm,
  simp only [nat.prime.proper_divisors hp, geom_sum_mul, finset.prod_singleton, cyclotomic_one],
end

lemma cyclotomic_prime_mul_X_sub_one (R : Type*) [comm_ring R] (p : ℕ) [hn : fact (nat.prime p)] :
  (cyclotomic p R) * (X - 1) = X ^ p - 1 :=
by rw [cyclotomic_eq_geom_sum hn.out, geom_sum_mul]

/-- If `p ^ k` is a prime power, then `cyclotomic (p ^ (n + 1)) R = geom_sum (X ^ p ^ n) p`. -/
lemma cyclotomic_prime_pow_eq_geom_sum {R : Type*} [comm_ring R] {p n : ℕ} (hp : nat.prime p) :
  cyclotomic (p ^ (n + 1)) R = geom_sum (X ^ p ^ n) p :=
begin
  have : ∀ m, cyclotomic (p ^ (m + 1)) R = geom_sum (X ^ (p ^ m)) p ↔
    geom_sum (X ^ p ^ m) p * ∏ (x : ℕ) in finset.range (m + 1),
      cyclotomic (p ^ x) R = X ^ p ^ (m + 1) - 1,
  { intro m,
    have := eq_cyclotomic_iff (pow_pos hp.pos (m + 1)) _,
    rw eq_comm at this,
    rw [this, nat.prod_proper_divisors_prime_pow hp], },
  induction n with n_n n_ih,
  { simp [cyclotomic_eq_geom_sum hp], },
  rw ((eq_cyclotomic_iff (pow_pos hp.pos (n_n.succ + 1)) _).mpr _).symm,
  rw [nat.prod_proper_divisors_prime_pow hp, finset.prod_range_succ, n_ih],
  rw this at n_ih,
  rw [mul_comm _ (geom_sum _ _), n_ih, geom_sum_mul, sub_left_inj, ← pow_mul, pow_add, pow_one],
end

/-- The constant term of `cyclotomic n R` is `1` if `2 ≤ n`. -/
lemma cyclotomic_coeff_zero (R : Type*) [comm_ring R] {n : ℕ} (hn : 2 ≤ n) :
  (cyclotomic n R).coeff 0 = 1 :=
begin
  induction n using nat.strong_induction_on with n hi,
  have hprod : (∏ i in nat.proper_divisors n, (polynomial.cyclotomic i R).coeff 0) = -1,
  { rw [←finset.insert_erase (nat.one_mem_proper_divisors_iff_one_lt.2
      (lt_of_lt_of_le one_lt_two hn)), finset.prod_insert (finset.not_mem_erase 1 _),
      cyclotomic_one R],
    have hleq : ∀ j ∈ n.proper_divisors.erase 1, 2 ≤ j,
    { intros j hj,
      apply nat.succ_le_of_lt,
      exact (ne.le_iff_lt ((finset.mem_erase.1 hj).1).symm).mp
              (nat.succ_le_of_lt (nat.pos_of_mem_proper_divisors (finset.mem_erase.1 hj).2)) },
    have hcongr : ∀ j ∈ n.proper_divisors.erase 1, (cyclotomic j R).coeff 0 = 1,
    { intros j hj,
      exact hi j (nat.mem_proper_divisors.1 (finset.mem_erase.1 hj).2).2 (hleq j hj) },
    have hrw : ∏ (x : ℕ) in n.proper_divisors.erase 1, (cyclotomic x R).coeff 0 = 1,
    { rw finset.prod_congr (refl (n.proper_divisors.erase 1)) hcongr,
      simp only [finset.prod_const_one] },
    simp only [hrw, mul_one, zero_sub, coeff_one_zero, coeff_X_zero, coeff_sub] },
  have heq : (X ^ n - 1).coeff 0 = -(cyclotomic n R).coeff 0,
  { rw [←prod_cyclotomic_eq_X_pow_sub_one (lt_of_lt_of_le zero_lt_two hn),
        nat.divisors_eq_proper_divisors_insert_self_of_pos (lt_of_lt_of_le zero_lt_two hn),
        finset.prod_insert nat.proper_divisors.not_self_mem, mul_coeff_zero, coeff_zero_prod, hprod,
        mul_neg, mul_one] },
  have hzero : (X ^ n - 1).coeff 0 = (-1 : R),
  { rw coeff_zero_eq_eval_zero _,
    simp only [zero_pow (lt_of_lt_of_le zero_lt_two hn), eval_X, eval_one, zero_sub, eval_pow,
              eval_sub] },
  rw hzero at heq,
  exact neg_inj.mp (eq.symm heq)
end

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, where `p` is a prime, then `a` and `p` are
coprime. -/
lemma coprime_of_root_cyclotomic {n : ℕ} (hpos : 0 < n) {p : ℕ} [hprime : fact p.prime] {a : ℕ}
  (hroot : is_root (cyclotomic n (zmod p)) (nat.cast_ring_hom (zmod p) a)) :
  a.coprime p :=
begin
  apply nat.coprime.symm,
  rw [hprime.1.coprime_iff_not_dvd],
  intro h,
  replace h := (zmod.nat_coe_zmod_eq_zero_iff_dvd a p).2 h,
  rw [is_root.def, eq_nat_cast, h, ← coeff_zero_eq_eval_zero] at hroot,
  by_cases hone : n = 1,
  { simp only [hone, cyclotomic_one, zero_sub, coeff_one_zero, coeff_X_zero, neg_eq_zero,
    one_ne_zero, coeff_sub] at hroot,
    exact hroot },
  rw [cyclotomic_coeff_zero (zmod p) (nat.succ_le_of_lt (lt_of_le_of_ne
        (nat.succ_le_of_lt hpos) (ne.symm hone)))] at hroot,
  exact one_ne_zero hroot
end

end cyclotomic

section order

/-- If `(a : ℕ)` is a root of `cyclotomic n (zmod p)`, then the multiplicative order of `a` modulo
`p` divides `n`. -/
lemma order_of_root_cyclotomic_dvd {n : ℕ} (hpos : 0 < n) {p : ℕ} [fact p.prime]
  {a : ℕ} (hroot : is_root (cyclotomic n (zmod p)) (nat.cast_ring_hom (zmod p) a)) :
  order_of (zmod.unit_of_coprime a (coprime_of_root_cyclotomic hpos hroot)) ∣ n :=
begin
  apply order_of_dvd_of_pow_eq_one,
  suffices hpow : eval (nat.cast_ring_hom (zmod p) a) (X ^ n - 1 : (zmod p)[X]) = 0,
  { simp only [eval_X, eval_one, eval_pow, eval_sub, eq_nat_cast] at hpow,
    apply units.coe_eq_one.1,
    simp only [sub_eq_zero.mp hpow, zmod.coe_unit_of_coprime, units.coe_pow] },
  rw [is_root.def] at hroot,
  rw [← prod_cyclotomic_eq_X_pow_sub_one hpos (zmod p),
    nat.divisors_eq_proper_divisors_insert_self_of_pos hpos,
    finset.prod_insert nat.proper_divisors.not_self_mem, eval_mul, hroot, zero_mul]
end

end order

section minpoly

open is_primitive_root complex

/-- The minimal polynomial of a primitive `n`-th root of unity `μ` divides `cyclotomic n ℤ`. -/
lemma _root_.is_primitive_root.minpoly_dvd_cyclotomic {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  minpoly ℤ μ ∣ cyclotomic n ℤ :=
begin
  apply minpoly.gcd_domain_dvd ℚ (is_integral h hpos) (cyclotomic.monic n ℤ).is_primitive,
  simpa [aeval_def, eval₂_eq_eval_map, is_root.def] using is_root_cyclotomic hpos h
end

lemma _root_.is_primitive_root.minpoly_eq_cyclotomic_of_irreducible {K : Type*} [field K]
  {R : Type*} [comm_ring R] [is_domain R] {μ : R} {n : ℕ} [algebra K R] (hμ : is_primitive_root μ n)
  (h : irreducible $ cyclotomic n K) [ne_zero (n : K)] : cyclotomic n K = minpoly K μ :=
begin
  haveI := ne_zero.of_no_zero_smul_divisors K R n,
  refine minpoly.eq_of_irreducible_of_monic h _ (cyclotomic.monic n K),
  rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic, ←is_root.def, is_root_cyclotomic_iff]
end

/-- `cyclotomic n ℤ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
lemma cyclotomic_eq_minpoly {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  cyclotomic n ℤ = minpoly ℤ μ :=
begin
  refine eq_of_monic_of_dvd_of_nat_degree_le (minpoly.monic (is_integral h hpos))
    (cyclotomic.monic n ℤ) (h.minpoly_dvd_cyclotomic hpos) _,
  simpa [nat_degree_cyclotomic n ℤ] using totient_le_degree_minpoly h
end

/-- `cyclotomic n ℚ` is the minimal polynomial of a primitive `n`-th root of unity `μ`. -/
lemma cyclotomic_eq_minpoly_rat {n : ℕ} {K : Type*} [field K] {μ : K}
  (h : is_primitive_root μ n) (hpos : 0 < n) [char_zero K] :
  cyclotomic n ℚ = minpoly ℚ μ :=
begin
  rw [← map_cyclotomic_int, cyclotomic_eq_minpoly h hpos],
  exact (minpoly.gcd_domain_eq_field_fractions _ (is_integral h hpos)).symm
end

/-- `cyclotomic n ℤ` is irreducible. -/
lemma cyclotomic.irreducible {n : ℕ} (hpos : 0 < n) : irreducible (cyclotomic n ℤ) :=
begin
  rw [cyclotomic_eq_minpoly (is_primitive_root_exp n hpos.ne') hpos],
  apply minpoly.irreducible,
  exact (is_primitive_root_exp n hpos.ne').is_integral hpos,
end

/-- `cyclotomic n ℚ` is irreducible. -/
lemma cyclotomic.irreducible_rat {n : ℕ} (hpos : 0 < n) : irreducible (cyclotomic n ℚ) :=
begin
  rw [← map_cyclotomic_int],
  exact (is_primitive.int.irreducible_iff_irreducible_map_cast (cyclotomic.is_primitive n ℤ)).1
    (cyclotomic.irreducible hpos),
end

/-- If `n ≠ m`, then `(cyclotomic n ℚ)` and `(cyclotomic m ℚ)` are coprime. -/
lemma cyclotomic.is_coprime_rat {n m : ℕ} (h : n ≠ m) :
  is_coprime (cyclotomic n ℚ) (cyclotomic m ℚ) :=
begin
  rcases n.eq_zero_or_pos with rfl | hnzero,
  { exact is_coprime_one_left },
  rcases m.eq_zero_or_pos with rfl | hmzero,
  { exact is_coprime_one_right },
  rw (irreducible.coprime_iff_not_dvd $ cyclotomic.irreducible_rat $ hnzero),
  exact (λ hdiv, h $ cyclotomic_injective $ eq_of_monic_of_associated (cyclotomic.monic n ℚ)
    (cyclotomic.monic m ℚ) $ irreducible.associated_of_dvd (cyclotomic.irreducible_rat
    hnzero) (cyclotomic.irreducible_rat hmzero) hdiv),
end

end minpoly

section expand

/-- If `p` is a prime such that `¬ p ∣ n`, then
`expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R)`. -/
@[simp] lemma cyclotomic_expand_eq_cyclotomic_mul {p n : ℕ} (hp : nat.prime p) (hdiv : ¬p ∣ n)
  (R : Type*) [comm_ring R] :
  expand R p (cyclotomic n R) = (cyclotomic (n * p) R) * (cyclotomic n R) :=
begin
  rcases nat.eq_zero_or_pos n with rfl | hnpos,
  { simp },
  haveI := ne_zero.of_pos hnpos,
  suffices : expand ℤ p (cyclotomic n ℤ) = (cyclotomic (n * p) ℤ) * (cyclotomic n ℤ),
  { rw [← map_cyclotomic_int, ← map_expand, this, map_mul, map_cyclotomic_int] },
  refine eq_of_monic_of_dvd_of_nat_degree_le (monic_mul (cyclotomic.monic _ _)
    (cyclotomic.monic _ _)) ((cyclotomic.monic n ℤ).expand hp.pos) _ _,
  { refine (is_primitive.int.dvd_iff_map_cast_dvd_map_cast _ _ (is_primitive.mul
      (cyclotomic.is_primitive (n * p) ℤ) (cyclotomic.is_primitive n ℤ))
      ((cyclotomic.monic n ℤ).expand hp.pos).is_primitive).2 _,
    rw [map_mul, map_cyclotomic_int, map_cyclotomic_int, map_expand, map_cyclotomic_int],
    refine is_coprime.mul_dvd (cyclotomic.is_coprime_rat (λ h, _)) _ _,
    { replace h : n * p = n * 1 := by simp [h],
      exact nat.prime.ne_one hp (nat.eq_of_mul_eq_mul_left hnpos h) },
    { have hpos : 0 < n * p := mul_pos hnpos hp.pos,
      have hprim := complex.is_primitive_root_exp _ hpos.ne',
      rw [cyclotomic_eq_minpoly_rat hprim hpos],
      refine @minpoly.dvd ℚ ℂ _ _ algebra_rat _ _ _,
      rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval, ← is_root.def,
        is_root_cyclotomic_iff],
      convert is_primitive_root.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n),
      rw [nat.mul_div_cancel _ (nat.prime.pos hp)] },
    { have hprim := complex.is_primitive_root_exp _ hnpos.ne.symm,
      rw [cyclotomic_eq_minpoly_rat hprim hnpos],
      refine @minpoly.dvd ℚ ℂ _ _ algebra_rat _ _ _,
      rw [aeval_def, ← eval_map, map_expand, expand_eval, ← is_root.def,
        ← cyclotomic_eq_minpoly_rat hprim hnpos, map_cyclotomic, is_root_cyclotomic_iff],
      exact is_primitive_root.pow_of_prime hprim hp hdiv,} },
  { rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_mul (cyclotomic_ne_zero _ ℤ)
      (cyclotomic_ne_zero _ ℤ), nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
      nat.totient_mul ((nat.prime.coprime_iff_not_dvd hp).2 hdiv),
      nat.totient_prime hp, mul_comm (p - 1), ← nat.mul_succ, nat.sub_one,
      nat.succ_pred_eq_of_pos hp.pos] }
end

/-- If `p` is a prime such that `p ∣ n`, then
`expand R p (cyclotomic n R) = cyclotomic (p * n) R`. -/
@[simp] lemma cyclotomic_expand_eq_cyclotomic {p n : ℕ} (hp : nat.prime p) (hdiv : p ∣ n)
  (R : Type*) [comm_ring R] : expand R p (cyclotomic n R) = cyclotomic (n * p) R :=
begin
  rcases n.eq_zero_or_pos with rfl | hzero,
  { simp },
  haveI := ne_zero.of_pos hzero,
  suffices : expand ℤ p (cyclotomic n ℤ) = cyclotomic (n * p) ℤ,
  { rw [← map_cyclotomic_int, ← map_expand, this, map_cyclotomic_int] },
  refine eq_of_monic_of_dvd_of_nat_degree_le (cyclotomic.monic _ _)
    ((cyclotomic.monic n ℤ).expand hp.pos) _ _,
  { have hpos := nat.mul_pos hzero hp.pos,
    have hprim := complex.is_primitive_root_exp _ hpos.ne.symm,
    rw [cyclotomic_eq_minpoly hprim hpos],
    refine @minpoly.gcd_domain_dvd ℤ ℂ ℚ _ _ _ _ _ _ _ _ complex.algebra (algebra_int ℂ) _ _
      (is_primitive_root.is_integral hprim hpos) _ ((cyclotomic.monic n ℤ).expand
      hp.pos).is_primitive _,
    rw [aeval_def, ← eval_map, map_expand, map_cyclotomic, expand_eval,
        ← is_root.def, is_root_cyclotomic_iff],
    { convert is_primitive_root.pow_of_dvd hprim hp.ne_zero (dvd_mul_left p n),
      rw [nat.mul_div_cancel _ hp.pos] } },
  { rw [nat_degree_expand, nat_degree_cyclotomic, nat_degree_cyclotomic, mul_comm n,
        nat.totient_mul_of_prime_of_dvd hp hdiv, mul_comm] }
end

end expand

section char_p

/-- If `R` is of characteristic `p` and `¬p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1)`. -/
lemma cyclotomic_mul_prime_eq_pow_of_not_dvd (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)]
  [ring R] [char_p R p] (hn : ¬p ∣ n) : cyclotomic (n * p) R = (cyclotomic n R) ^ (p - 1) :=
begin
  suffices : cyclotomic (n * p) (zmod p) = (cyclotomic n (zmod p)) ^ (p - 1),
  { rw [← map_cyclotomic _ (algebra_map (zmod p) R), ← map_cyclotomic _ (algebra_map (zmod p) R),
      this, polynomial.map_pow] },
  apply mul_right_injective₀ (cyclotomic_ne_zero n $ zmod p),
  rw [←pow_succ, tsub_add_cancel_of_le hp.out.one_lt.le, mul_comm, ← zmod.expand_card],
  nth_rewrite 2 [← map_cyclotomic_int],
  rw [← map_expand, cyclotomic_expand_eq_cyclotomic_mul hp.out hn, polynomial.map_mul,
    map_cyclotomic, map_cyclotomic]
end

/-- If `R` is of characteristic `p` and `p ∣ n`, then
`cyclotomic (n * p) R = (cyclotomic n R) ^ p`. -/
lemma cyclotomic_mul_prime_dvd_eq_pow (R : Type*) {p n : ℕ} [hp : fact (nat.prime p)] [ring R]
  [char_p R p] (hn : p ∣ n) : cyclotomic (n * p) R = (cyclotomic n R) ^ p :=
begin
  suffices : cyclotomic (n * p) (zmod p) = (cyclotomic n (zmod p)) ^ p,
  { rw [← map_cyclotomic _ (algebra_map (zmod p) R), ← map_cyclotomic _ (algebra_map (zmod p) R),
      this, polynomial.map_pow] },
  rw [← zmod.expand_card, ← map_cyclotomic_int n, ← map_expand, cyclotomic_expand_eq_cyclotomic
    hp.out hn, map_cyclotomic, mul_comm]
end

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then
`cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))`. -/
lemma cyclotomic_mul_prime_pow_eq (R : Type*) {p m : ℕ} [fact (nat.prime p)]
  [ring R] [char_p R p] (hm : ¬p ∣ m) :
  ∀ {k}, 0 < k → cyclotomic (p ^ k * m) R = (cyclotomic m R) ^ (p ^ k - p ^ (k - 1))
| 1 _ := by rw [pow_one, nat.sub_self, pow_zero, mul_comm,
  cyclotomic_mul_prime_eq_pow_of_not_dvd R hm]
| (a + 2) _ :=
begin
  have hdiv : p ∣ p ^ a.succ * m := ⟨p ^ a * m, by rw [← mul_assoc, pow_succ]⟩,
  rw [pow_succ, mul_assoc, mul_comm, cyclotomic_mul_prime_dvd_eq_pow R hdiv,
      cyclotomic_mul_prime_pow_eq a.succ_pos, ← pow_mul],
  congr' 1,
  simp only [tsub_zero, nat.succ_sub_succ_eq_sub],
  rw [nat.mul_sub_right_distrib, mul_comm, pow_succ']
end

/-- If `R` is of characteristic `p` and `¬p ∣ m`, then `ζ` is a root of `cyclotomic (p ^ k * m) R`
 if and only if it is a primitive `m`-th root of unity. -/
lemma is_root_cyclotomic_prime_pow_mul_iff_of_char_p {m k p : ℕ} {R : Type*} [comm_ring R]
  [is_domain R] [hp : fact (nat.prime p)] [hchar : char_p R p] {μ : R} [ne_zero (m : R)] :
  (polynomial.cyclotomic (p ^ k * m) R).is_root μ ↔ is_primitive_root μ m :=
begin
  rcases k.eq_zero_or_pos with rfl | hk,
  { rw [pow_zero, one_mul, is_root_cyclotomic_iff] },
  refine ⟨λ h, _, λ h, _⟩,
  { rw [is_root.def, cyclotomic_mul_prime_pow_eq R (ne_zero.not_char_dvd R p m) hk, eval_pow] at h,
    replace h := pow_eq_zero h,
    rwa [← is_root.def, is_root_cyclotomic_iff] at h },
  { rw [← is_root_cyclotomic_iff, is_root.def] at h,
    rw [cyclotomic_mul_prime_pow_eq R (ne_zero.not_char_dvd R p m) hk,
        is_root.def, eval_pow, h, zero_pow],
    simp only [tsub_pos_iff_lt],
    apply strict_mono_pow hp.out.one_lt (nat.pred_lt hk.ne') }
end

end char_p

end polynomial
