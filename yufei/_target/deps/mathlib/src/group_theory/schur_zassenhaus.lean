/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.complement
import group_theory.group_action.basic
import group_theory.sylow

/-!
# The Schur-Zassenhaus Theorem

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement'_of_coprime` : The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement'_of_coprime`  The **Schur-Zassenhaus** theorem:
  If `H : subgroup G` is normal and has order coprime to its index,
  then there exists a subgroup `K` which is a (left) complement of `H`.
-/

open_locale big_operators

namespace subgroup

section schur_zassenhaus_abelian

variables {G : Type*} [group G] {H : subgroup G}

@[to_additive] instance : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨_, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

lemma smul_symm_apply_eq_mul_symm_apply_inv_smul
  (g : G) (α : left_transversals (H : set G)) (q : G ⧸ H) :
  ↑((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
    g * ((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm
      (g⁻¹ • q : G ⧸ H)) :=
begin
  let w := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)),
  let y := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)),
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • α).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w (w.symm (g⁻¹ • q : G ⧸ H))),
  rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul],
end

variables [is_commutative H] [fintype (G ⧸ H)]

variables (α β γ : left_transversals (H : set G))

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff [hH : normal H] : H :=
let α' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm,
    β' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm in
∏ (q : G ⧸ H), ⟨(α' q) * (β' q)⁻¹,
  hH.mem_comm (quotient.exact' ((β'.symm_apply_apply q).trans (α'.symm_apply_apply q).symm))⟩

@[to_additive] lemma diff_mul_diff [normal H] : diff α β * diff β γ = diff α γ :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ x hx, subtype.ext
  (by rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assoc, inv_mul_cancel_left])))

@[to_additive] lemma diff_self [normal H] : diff α α = 1 :=
mul_right_eq_self.mp (diff_mul_diff α α α)

@[to_additive] lemma diff_inv [normal H]: (diff α β)⁻¹ = diff β α :=
inv_eq_of_mul_eq_one ((diff_mul_diff α β α).trans (diff_self α))

lemma smul_diff_smul [hH : normal H] (g : G) :
  diff (g • α) (g • β) = ⟨g * diff α β * g⁻¹, hH.conj_mem (diff α β).1 (diff α β).2 g⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g * h * g⁻¹, hH.conj_mem h.1 h.2 g⟩,
    map_one' := subtype.ext (by rw [coe_mk, coe_one, mul_one, mul_inv_self]),
    map_mul' := λ h₁ h₂, subtype.ext (by rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, inv_mul_cancel_left]) },
  refine eq.trans (finset.prod_bij' (λ q _, (↑g)⁻¹ * q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, ↑g * q) (λ _ _, finset.mem_univ _)
    (λ q _, mul_inv_cancel_left g q) (λ q _, inv_mul_cancel_left g q)) (ϕ.map_prod _ _).symm,
  change _ * _ = g * (_ * _) * g⁻¹,
  simp_rw [smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc],
  refl,
end

lemma smul_diff [H.normal] (h : H) :
  diff (h • α) β = h ^ H.index * diff α β :=
begin
  rw [diff, diff, index_eq_card, ←finset.card_univ, ←finset.prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl (λ q _, _),
  rw [subtype.ext_iff, coe_mul, coe_mk, coe_mk, ←mul_assoc, mul_right_cancel_iff],
  rw [show h • α = (h : G) • α, from rfl, smul_symm_apply_eq_mul_symm_apply_inv_smul],
  rw [mul_left_cancel_iff, ←subtype.ext_iff, equiv.apply_eq_iff_eq, inv_smul_eq_iff],
  exact self_eq_mul_left.mpr ((quotient_group.eq_one_iff _).mpr h.2),
end

variables (H)

instance setoid_diff [H.normal] : setoid (left_transversals (H : set G)) :=
setoid.mk (λ α β, diff α β = 1) ⟨λ α, diff_self α, λ α β h₁,
  by rw [←diff_inv, h₁, one_inv], λ α β γ h₁ h₂, by rw [←diff_mul_diff, h₁, h₂, one_mul]⟩

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation -/
def quotient_diff [H.normal] :=
quotient H.setoid_diff

instance [H.normal] : inhabited H.quotient_diff := quotient.inhabited _

variables {H}

instance [H.normal] : mul_action G H.quotient_diff :=
{ smul := λ g, quotient.map (λ α, g • α) (λ α β h, (smul_diff_smul α β g).trans
    (subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (subtype.ext_iff.mp h))))),
  mul_smul := λ g₁ g₂ q, quotient.induction_on q (λ α, congr_arg quotient.mk (mul_smul g₁ g₂ α)),
  one_smul := λ q, quotient.induction_on q (λ α, congr_arg quotient.mk (one_smul G α)) }

variables [fintype H]

lemma exists_smul_eq [H.normal] (α β : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) H.index) :
  ∃ h : H, h • α = β :=
quotient.induction_on α (quotient.induction_on β
  (λ β α, exists_imp_exists (λ n, quotient.sound)
    ⟨(pow_coprime hH).symm (diff α β)⁻¹, by
    { change diff ((_ : H) • _) _ = 1,
      rw smul_diff,
      change pow_coprime hH ((pow_coprime hH).symm (diff α β)⁻¹) * (diff α β) = 1,
      rw [equiv.apply_symm_apply, inv_mul_self] }⟩))

lemma smul_left_injective [H.normal] (α : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) H.index) :
  function.injective (λ h : H, h • α) :=
λ h₁ h₂, begin
  refine quotient.induction_on α (λ α hα, _),
  replace hα : diff (h₁ • α) (h₂ • α) = 1 := quotient.exact hα,
  rw [smul_diff, ←diff_inv, smul_diff, diff_self, mul_one, mul_inv_eq_one] at hα,
  exact (pow_coprime hH).injective hα,
end

lemma is_complement'_stabilizer_of_coprime [fintype G] [H.normal] {α : H.quotient_diff}
  (hH : nat.coprime (fintype.card H) H.index) :
  is_complement' H (mul_action.stabilizer G α) :=
begin
  classical,
  let ϕ : H ≃ mul_action.orbit G α := equiv.of_bijective (λ h, ⟨h • α, h, rfl⟩)
    ⟨λ h₁ h₂ hh, smul_left_injective α hH (subtype.ext_iff.mp hh),
      λ β, exists_imp_exists (λ h hh, subtype.ext hh) (exists_smul_eq α β hH)⟩,
  have key := card_eq_card_quotient_mul_card_subgroup (mul_action.stabilizer G α),
  rw ← fintype.card_congr (ϕ.trans (mul_action.orbit_equiv_quotient_stabilizer G α)) at key,
  apply is_complement'_of_coprime key.symm,
  rw [card_eq_card_quotient_mul_card_subgroup H, mul_comm, mul_right_inj'] at key,
  { rwa [←key, ←index_eq_card] },
  { rw [←pos_iff_ne_zero, fintype.card_pos_iff],
    apply_instance },
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma exists_right_complement'_of_coprime_aux [fintype G] [H.normal]
  (hH : nat.coprime (fintype.card H) H.index) :
  ∃ K : subgroup G, is_complement' H K :=
nonempty_of_inhabited.elim
  (λ α : H.quotient_diff, ⟨mul_action.stabilizer G α, is_complement'_stabilizer_of_coprime hH⟩)

end schur_zassenhaus_abelian

open_locale classical

universe u

namespace schur_zassenhaus_induction

/-! ## Proof of the Schur-Zassenhaus theorem

In this section, we prove the Schur-Zassenhaus theorem.
The proof is by contradiction. We assume that `G` is a minimal counterexample to the theorem.
-/

variables {G : Type u} [group G] [fintype G] {N : subgroup G} [normal N]
  (h1 : nat.coprime (fintype.card N) N.index)
  (h2 : ∀ (G' : Type u) [group G'] [fintype G'], by exactI
    ∀ (hG'3 : fintype.card G' < fintype.card G)
    {N' : subgroup G'} [N'.normal] (hN : nat.coprime (fintype.card N') N'.index),
    ∃ H' : subgroup G', is_complement' N' H')
  (h3 : ∀ H : subgroup G, ¬ is_complement' N H)

include h1 h2 h3

/-! We will arrive at a contradiction via the following steps:
 * step 0: `N` (the normal Hall subgroup) is nontrivial.
 * step 1: If `K` is a subgroup of `G` with `K ⊔ N = ⊤`, then `K = ⊤`.
 * step 2: `N` is a minimal normal subgroup, phrased in terms of subgroups of `G`.
 * step 3: `N` is a minimal normal subgroup, phrased in terms of subgroups of `N`.
 * step 4: `p` (`min_fact (fintype.card N)`) is prime (follows from step0).
 * step 5: `P` (a Sylow `p`-subgroup of `N`) is nontrivial.
 * step 6: `N` is a `p`-group (applies step 1 to the normalizer of `P` in `G`).
 * step 7: `N` is abelian (applies step 3 to the center of `N`).
-/

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
@[nolint unused_arguments] private lemma step0 : N ≠ ⊥ :=
begin
  unfreezingI { rintro rfl },
  exact h3 ⊤ is_complement'_bot_top,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step1 (K : subgroup G) (hK : K ⊔ N = ⊤) : K = ⊤ :=
begin
  contrapose! h3,
  have h4 : (N.comap K.subtype).index = N.index,
  { rw [←N.relindex_top_right, ←hK],
    exact relindex_eq_relindex_sup K N },
  have h5 : fintype.card K < fintype.card G,
  { rw ← K.index_mul_card,
    exact lt_mul_of_one_lt_left fintype.card_pos (one_lt_index_of_ne_top h3) },
  have h6 : nat.coprime (fintype.card (N.comap K.subtype)) (N.comap K.subtype).index,
  { rw h4,
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype subtype.coe_injective) },
  obtain ⟨H, hH⟩ := h2 K h5 h6,
  replace hH : fintype.card (H.map K.subtype) = N.index :=
  ((set.card_image_of_injective _ subtype.coe_injective).trans (nat.mul_left_injective
    fintype.card_pos (hH.symm.card_mul.trans (N.comap K.subtype).index_mul_card.symm))).trans h4,
  have h7 : fintype.card N * fintype.card (H.map K.subtype) = fintype.card G,
  { rw [hH, ←N.index_mul_card, mul_comm] },
  have h8 : (fintype.card N).coprime (fintype.card (H.map K.subtype)),
  { rwa hH },
  exact ⟨H.map K.subtype, is_complement'_of_coprime h7 h8⟩,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step2 (K : subgroup G) [K.normal] (hK : K ≤ N) : K = ⊥ ∨ K = N :=
begin
  have : function.surjective (quotient_group.mk' K) := quotient.surjective_quotient_mk',
  have h4 := step1 h1 h2 h3,
  contrapose! h4,
  have h5 : fintype.card (G ⧸ K) < fintype.card G,
  { rw [←index_eq_card, ←K.index_mul_card],
    refine lt_mul_of_one_lt_right (nat.pos_of_ne_zero index_ne_zero_of_fintype)
      (K.one_lt_card_iff_ne_bot.mpr h4.1) },
  have h6 : nat.coprime (fintype.card (N.map (quotient_group.mk' K)))
    (N.map (quotient_group.mk' K)).index,
  { have index_map := N.index_map_eq this (by rwa quotient_group.ker_mk),
    have index_pos : 0 < N.index := nat.pos_of_ne_zero index_ne_zero_of_fintype,
    rw index_map,
    refine h1.coprime_dvd_left _,
    rw [←nat.mul_dvd_mul_iff_left index_pos, index_mul_card, ←index_map, index_mul_card],
    exact K.card_quotient_dvd_card },
  obtain ⟨H, hH⟩ := h2 (G ⧸ K) h5 h6,
  refine ⟨H.comap (quotient_group.mk' K), _, _⟩,
  { have key : (N.map (quotient_group.mk' K)).comap (quotient_group.mk' K) = N,
    { refine comap_map_eq_self _,
      rwa quotient_group.ker_mk },
    rwa [←key, comap_sup_eq, hH.symm.sup_eq_top, comap_top] },
  { rw ← comap_top (quotient_group.mk' K),
    intro hH',
    rw [comap_injective this hH', is_complement'_top_right,
        map_eq_bot_iff, quotient_group.ker_mk] at hH,
    { exact h4.2 (le_antisymm hK hH) } },
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step3 (K : subgroup N) [(K.map N.subtype).normal] : K = ⊥ ∨ K = ⊤ :=
begin
  have key := step2 h1 h2 h3 (K.map N.subtype) K.map_subtype_le,
  rw ← map_bot N.subtype at key,
  conv at key { congr, skip, to_rhs, rw [←N.subtype_range, N.subtype.range_eq_map] },
  have inj := map_injective (show function.injective N.subtype, from subtype.coe_injective),
  rwa [inj.eq_iff, inj.eq_iff] at key,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step4 : (fintype.card N).min_fac.prime :=
(nat.min_fac_prime (N.one_lt_card_iff_ne_bot.mpr (step0 h1 h2 h3)).ne')

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step5 {P : sylow (fintype.card N).min_fac N} : P.1 ≠ ⊥ :=
begin
  haveI : fact ((fintype.card N).min_fac.prime) := ⟨step4 h1 h2 h3⟩,
  exact P.ne_bot_of_dvd_card (fintype.card N).min_fac_dvd,
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma step6 : is_p_group (fintype.card N).min_fac N :=
begin
  haveI : fact ((fintype.card N).min_fac.prime) := ⟨step4 h1 h2 h3⟩,
  refine sylow.nonempty.elim (λ P, P.2.of_surjective P.1.subtype _),
  rw [←monoid_hom.range_top_iff_surjective, subtype_range],
  haveI : (P.1.map N.subtype).normal := normalizer_eq_top.mp
    (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top),
  exact (step3 h1 h2 h3 P.1).resolve_left (step5 h1 h2 h3),
end

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
lemma step7 : is_commutative N :=
begin
  haveI := N.bot_or_nontrivial.resolve_left (step0 h1 h2 h3),
  haveI : fact ((fintype.card N).min_fac.prime) := ⟨step4 h1 h2 h3⟩,
  exact ⟨⟨λ g h, eq_top_iff.mp ((step3 h1 h2 h3 N.center).resolve_left
    (step6 h1 h2 h3).bot_lt_center.ne') (mem_top h) g⟩⟩,
end

end schur_zassenhaus_induction

variables {n : ℕ} {G : Type u} [group G]

/-- Do not use this lemma: It is made obsolete by `exists_right_complement'_of_coprime` -/
private lemma exists_right_complement'_of_coprime_aux' [fintype G] (hG : fintype.card G = n)
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement' N H :=
begin
  unfreezingI { revert G },
  apply nat.strong_induction_on n,
  rintros n ih G _ _ rfl N _ hN,
  refine not_forall_not.mp (λ h3, _),
  haveI := by exactI
    schur_zassenhaus_induction.step7 hN (λ G' _ _ hG', by { apply ih _ hG', refl }) h3,
  exact not_exists_of_forall_not h3 (exists_right_complement'_of_coprime_aux hN),
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime_of_fintype [fintype G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement' N H :=
exists_right_complement'_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement'_of_coprime
  {N : subgroup G} [N.normal] (hN : nat.coprime (nat.card N) N.index) :
  ∃ H : subgroup G, is_complement' N H :=
begin
  by_cases hN1 : nat.card N = 0,
  { rw [hN1, nat.coprime_zero_left, index_eq_one] at hN,
    rw hN,
    exact ⟨⊥, is_complement'_top_bot⟩ },
  by_cases hN2 : N.index = 0,
  { rw [hN2, nat.coprime_zero_right] at hN,
    haveI := (cardinal.to_nat_eq_one_iff_unique.mp hN).1,
    rw N.eq_bot_of_subsingleton,
    exact ⟨⊤, is_complement'_bot_top⟩ },
  have hN3 : nat.card G ≠ 0,
  { rw ← N.card_mul_index,
    exact mul_ne_zero hN1 hN2 },
  haveI := (cardinal.lt_omega_iff_fintype.mp
    (lt_of_not_ge (mt cardinal.to_nat_apply_of_omega_le hN3))).some,
  rw nat.card_eq_fintype_card at hN,
  exact exists_right_complement'_of_coprime_of_fintype hN,
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime_of_fintype
  [fintype G] {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement' H N :=
Exists.imp (λ _, is_complement'.symm) (exists_right_complement'_of_coprime_of_fintype hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists a
  subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement'_of_coprime
  {N : subgroup G} [N.normal] (hN : nat.coprime (nat.card N) N.index) :
  ∃ H : subgroup G, is_complement' H N :=
Exists.imp (λ _, is_complement'.symm) (exists_right_complement'_of_coprime hN)

end subgroup
