/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import number_theory.cyclotomic.primitive_roots
import field_theory.polynomial_galois_group

/-!
# Galois group of cyclotomic extensions

In this file, we show the relationship between the Galois group of `K(ζₙ)` and `(zmod n)ˣ`;
it is always a subgroup, and if the `n`th cyclotomic polynomial is irreducible, they are isomorphic.

## Main results

* `is_primitive_root.aut_to_pow_injective`: `is_primitive_root.aut_to_pow` is injective
  in the case that it's considered over a cyclotomic field extension, where `n` does not divide
  the characteristic of K.
* `is_cyclotomic_extension.aut_equiv_pow`: If, additionally, the `n`th cyclotomic polynomial is
  irreducible in K, then `aut_to_pow` is a `mul_equiv` (for example, in ℚ and certain 𝔽ₚ).
* `gal_X_pow_equiv_units_zmod`, `gal_cyclotomic_equiv_units_zmod`: Repackage `aut_equiv_pow` in
  terms of `polynomial.gal`.
* `is_cyclotomic_extension.aut.comm_group`: Cyclotomic extensions are abelian.

## References

* https://kconrad.math.uconn.edu/blurbs/galoistheory/cyclotomic.pdf

## TODO

* `zeta_pow_power_basis` is not sufficiently general; the correct solution is some
  `power_basis.map_conjugate`, but figuring out the exact correct assumptions + proof for this is
  mathematically nontrivial. (Current thoughts: the ideal of polynomials with α as a root is equal
  to the ideal of polynomials with β as a root, which, in an integrally closed domain, reduces
  to the usual condition that they are the roots of each others' minimal polynomials.)

-/

local attribute [instance] pnat.fact_pos

variables {n : ℕ+} (K : Type*) [field K] {L : Type*} [field L] {μ : L} (hμ : is_primitive_root μ n)
          [algebra K L] [is_cyclotomic_extension {n} K L]

open polynomial ne_zero is_cyclotomic_extension

namespace is_primitive_root

/-- `is_primitive_root.aut_to_pow` is injective in the case that it's considered over a cyclotomic
field extension, where `n` does not divide the characteristic of K. -/
lemma aut_to_pow_injective : function.injective $ hμ.aut_to_pow K :=
begin
  intros f g hfg,
  apply_fun units.val at hfg,
  simp only [is_primitive_root.coe_aut_to_pow_apply, units.val_eq_coe] at hfg,
  generalize_proofs hf' hg' at hfg,
  have hf := hf'.some_spec,
  have hg := hg'.some_spec,
  generalize_proofs hζ at hf hg,
  suffices : f hμ.to_roots_of_unity = g hμ.to_roots_of_unity,
  { apply alg_equiv.coe_alg_hom_injective,
    apply (hμ.power_basis K).alg_hom_ext,
    exact this },
  rw zmod.eq_iff_modeq_nat at hfg,
  refine (hf.trans _).trans hg.symm,
  rw [←roots_of_unity.coe_pow _ hf'.some, ←roots_of_unity.coe_pow _ hg'.some],
  congr' 1,
  rw [pow_eq_pow_iff_modeq],
  convert hfg,
  rw [hμ.eq_order_of],
  rw [←hμ.coe_to_roots_of_unity_coe] {occs := occurrences.pos [2]},
  rw [order_of_units, order_of_subgroup]
end

end is_primitive_root

namespace is_cyclotomic_extension

/-- Cyclotomic extensions are abelian. -/
noncomputable def aut.comm_group [ne_zero ((n : ℕ) : K)] : comm_group (L ≃ₐ[K] L) :=
let _ := of_no_zero_smul_divisors K L n in by exactI
((zeta_primitive_root n K L).aut_to_pow_injective K).comm_group _
  (map_one _) (map_mul _) (map_inv _) (map_div _)

variables (h : irreducible (cyclotomic n K)) {K} (L)

include h

/-- The `mul_equiv` that takes an automorphism `f` to the element `k : (zmod n)ˣ` such that
  `f μ = μ ^ k`. A stronger version of `is_primitive_root.aut_to_pow`. -/
@[simps] noncomputable def aut_equiv_pow [ne_zero ((n : ℕ) : K)] : (L ≃ₐ[K] L) ≃* (zmod n)ˣ :=
let hn := of_no_zero_smul_divisors K L n in
by exactI
let hζ := zeta_primitive_root n K L,
    hμ := λ t, hζ.pow_of_coprime _ (zmod.val_coe_unit_coprime t) in
{ inv_fun := λ t, (hζ.power_basis K).equiv_of_minpoly ((hμ t).power_basis K)
  begin
    simp only [is_primitive_root.power_basis_gen],
    have hr := is_primitive_root.minpoly_eq_cyclotomic_of_irreducible
               ((zeta_primitive_root n K L).pow_of_coprime _ (zmod.val_coe_unit_coprime t)) h,
    exact ((zeta_primitive_root n K L).minpoly_eq_cyclotomic_of_irreducible h).symm.trans hr
  end,
  left_inv := λ f, begin
    simp only [monoid_hom.to_fun_eq_coe],
    apply alg_equiv.coe_alg_hom_injective,
    apply (hζ.power_basis K).alg_hom_ext,
    simp only [alg_equiv.coe_alg_hom, alg_equiv.map_pow],
    rw power_basis.equiv_of_minpoly_gen,
    simp only [is_primitive_root.power_basis_gen, is_primitive_root.aut_to_pow_spec],
  end,
  right_inv := λ x, begin
    simp only [monoid_hom.to_fun_eq_coe],
    generalize_proofs _ _ _ h,
    have key := hζ.aut_to_pow_spec K ((hζ.power_basis K).equiv_of_minpoly
                                      ((hμ x).power_basis K) h),
    have := (hζ.power_basis K).equiv_of_minpoly_gen ((hμ x).power_basis K) h,
    rw hζ.power_basis_gen K at this,
    rw [this, is_primitive_root.power_basis_gen] at key,
    rw ← hζ.coe_to_roots_of_unity_coe at key {occs := occurrences.pos [1, 5]},
    simp only [←coe_coe, ←roots_of_unity.coe_pow] at key,
    replace key := roots_of_unity.coe_injective key,
    rw [pow_eq_pow_iff_modeq, ←order_of_subgroup, ←order_of_units, hζ.coe_to_roots_of_unity_coe,
        ←(zeta_primitive_root n K L).eq_order_of, ←zmod.eq_iff_modeq_nat] at key,
    simp only [zmod.nat_cast_val, zmod.cast_id', id.def] at key,
    exact units.ext key
  end,
  .. (zeta_primitive_root n K L).aut_to_pow K }

include hμ

variables {L}

/-- Maps `μ` to the `alg_equiv` that sends `is_cyclotomic_extension.zeta` to `μ`. -/
noncomputable def from_zeta_aut [ne_zero ((n : ℕ) : K)] : L ≃ₐ[K] L :=
have _ := of_no_zero_smul_divisors K L n, by exactI
let hζ := (zeta_primitive_root n K L).eq_pow_of_pow_eq_one hμ.pow_eq_one n.pos in
(aut_equiv_pow L h).symm $ zmod.unit_of_coprime hζ.some $
((zeta_primitive_root n K L).pow_iff_coprime n.pos hζ.some).mp $ hζ.some_spec.some_spec.symm ▸ hμ

lemma from_zeta_aut_spec [ne_zero ((n : ℕ) : K)] : from_zeta_aut hμ h (zeta n K L) = μ :=
begin
  simp_rw [from_zeta_aut, aut_equiv_pow_symm_apply],
  generalize_proofs _ hζ h _ hμ _,
  rw [←hζ.power_basis_gen K] {occs := occurrences.pos [4]},
  rw [power_basis.equiv_of_minpoly_gen, hμ.power_basis_gen K],
  convert h.some_spec.some_spec,
  exact zmod.val_cast_of_lt h.some_spec.some
end

end is_cyclotomic_extension

section gal

variables (h : irreducible (cyclotomic n K)) {K}

local attribute [instance] splitting_field_X_pow_sub_one splitting_field_cyclotomic

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`. Asserts that the
Galois group of `cyclotomic n K` is equivalent to `(zmod n)ˣ` if `n` does not divide the
characteristic of `K`, and `cyclotomic n K` is irreducible in the base field. -/
noncomputable def gal_cyclotomic_equiv_units_zmod [ne_zero ((n : ℕ) : K)] :
  (cyclotomic n K).gal ≃* (zmod n)ˣ :=
(alg_equiv.aut_congr (is_splitting_field.alg_equiv _ _)).symm.trans
(is_cyclotomic_extension.aut_equiv_pow L h)

/-- `is_cyclotomic_extension.aut_equiv_pow` repackaged in terms of `gal`. Asserts that the
Galois group of `X ^ n - 1` is equivalent to `(zmod n)ˣ` if `n` does not divide the characteristic
of `K`, and `cyclotomic n K` is irreducible in the base field. -/
noncomputable def gal_X_pow_equiv_units_zmod [ne_zero ((n : ℕ) : K)] :
  (X ^ (n : ℕ) - 1).gal ≃* (zmod n)ˣ :=
(alg_equiv.aut_congr (is_splitting_field.alg_equiv _ _)).symm.trans
(is_cyclotomic_extension.aut_equiv_pow L h)

end gal
