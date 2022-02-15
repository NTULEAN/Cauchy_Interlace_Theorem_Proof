/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/

import data.nat.factorization
import data.set_like.fintype
import group_theory.group_action.conj_act
import group_theory.p_group

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

## Main definitions

* `sylow p G` : The type of Sylow `p`-subgroups of `G`.

## Main statements

* `exists_subgroup_card_pow_prime`: A generalization of Sylow's first theorem:
  For every prime power `pⁿ` dividing the cardinality of `G`,
  there exists a subgroup of `G` of order `pⁿ`.
* `is_p_group.exists_le_sylow`: A generalization of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `sylow_conjugate`: A generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modeq_one`: A generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/

open fintype mul_action subgroup

section infinite_sylow

variables (p : ℕ) (G : Type*) [group G]

/-- A Sylow `p`-subgroup is a maximal `p`-subgroup. -/
structure sylow extends subgroup G :=
(is_p_group' : is_p_group p to_subgroup)
(is_maximal' : ∀ {Q : subgroup G}, is_p_group p Q → to_subgroup ≤ Q → Q = to_subgroup)

variables {p} {G}

namespace sylow

instance : has_coe (sylow p G) (subgroup G) := ⟨sylow.to_subgroup⟩

@[simp] lemma to_subgroup_eq_coe {P : sylow p G} : P.to_subgroup = ↑P := rfl

@[ext] lemma ext {P Q : sylow p G} (h : (P : subgroup G) = Q) : P = Q :=
by cases P; cases Q; congr'

lemma ext_iff {P Q : sylow p G} : P = Q ↔ (P : subgroup G) = Q :=
⟨congr_arg coe, ext⟩

instance : set_like (sylow p G) G :=
{ coe := coe,
  coe_injective' := λ P Q h, ext (set_like.coe_injective h) }

end sylow

/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
lemma is_p_group.exists_le_sylow {P : subgroup G} (hP : is_p_group p P) :
  ∃ Q : sylow p G, P ≤ Q :=
exists.elim (zorn.zorn_nonempty_partial_order₀ {Q : subgroup G | is_p_group p Q} (λ c hc1 hc2 Q hQ,
⟨ { carrier := ⋃ (R : c), R,
    one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩,
    inv_mem' := λ g ⟨_, ⟨R, rfl⟩, hg⟩, ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩,
    mul_mem' := λ g h ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩, (hc2.total_of_refl R.2 S.2).elim
      (λ T, ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) (λ T, ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩) },
  λ ⟨g, _, ⟨S, rfl⟩, hg⟩, by
  { refine exists_imp_exists (λ k hk, _) (hc1 S.2 ⟨g, hg⟩),
    rwa [subtype.ext_iff, coe_pow] at hk ⊢ },
  λ M hM g hg, ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩) P hP) (λ Q ⟨hQ1, hQ2, hQ3⟩, ⟨⟨Q, hQ1, hQ3⟩, hQ2⟩)

instance sylow.nonempty : nonempty (sylow p G) :=
nonempty_of_exists is_p_group.of_bot.exists_le_sylow

noncomputable instance sylow.inhabited : inhabited (sylow p G) :=
classical.inhabited_of_nonempty sylow.nonempty

lemma sylow.exists_comap_eq_of_ker_is_p_group {H : Type*} [group H] (P : sylow p H)
  {f : H →* G} (hf : is_p_group p f.ker) : ∃ Q : sylow p G, Q.1.comap f = P :=
exists_imp_exists (λ Q hQ, P.3 (Q.2.comap_of_ker_is_p_group f hf) (map_le_iff_le_comap.mp hQ))
  (P.2.map f).exists_le_sylow

lemma sylow.exists_comap_eq_of_injective {H : Type*} [group H] (P : sylow p H)
  {f : H →* G} (hf : function.injective f) : ∃ Q : sylow p G, Q.1.comap f = P :=
P.exists_comap_eq_of_ker_is_p_group (is_p_group.ker_is_p_group_of_injective hf)

lemma sylow.exists_comap_subtype_eq {H : subgroup G} (P : sylow p H) :
  ∃ Q : sylow p G, Q.1.comap H.subtype = P :=
P.exists_comap_eq_of_injective subtype.coe_injective

/-- If the kernel of `f : H →* G` is a `p`-group,
  then `fintype (sylow p G)` implies `fintype (sylow p H)`. -/
noncomputable def sylow.fintype_of_ker_is_p_group {H : Type*} [group H]
  {f : H →* G} (hf : is_p_group p f.ker) [fintype (sylow p G)] : fintype (sylow p H) :=
let h_exists := λ P : sylow p H, P.exists_comap_eq_of_ker_is_p_group hf,
  g : sylow p H → sylow p G := λ P, classical.some (h_exists P),
  hg : ∀ P : sylow p H, (g P).1.comap f = P := λ P, classical.some_spec (h_exists P) in
fintype.of_injective g (λ P Q h, sylow.ext (by simp only [←hg, h]))

/-- If `f : H →* G` is injective, then `fintype (sylow p G)` implies `fintype (sylow p H)`. -/
noncomputable def sylow.fintype_of_injective {H : Type*} [group H]
  {f : H →* G} (hf : function.injective f) [fintype (sylow p G)] : fintype (sylow p H) :=
sylow.fintype_of_ker_is_p_group (is_p_group.ker_is_p_group_of_injective hf)

/-- If `H` is a subgroup of `G`, then `fintype (sylow p G)` implies `fintype (sylow p H)`. -/
noncomputable instance (H : subgroup G) [fintype (sylow p G)] : fintype (sylow p H) :=
sylow.fintype_of_injective (show function.injective H.subtype, from subtype.coe_injective)

open_locale pointwise

/-- `subgroup.pointwise_mul_action` preserves Sylow subgroups. -/
instance sylow.pointwise_mul_action {α : Type*} [group α] [mul_distrib_mul_action α G] :
  mul_action α (sylow p G) :=
{ smul := λ g P, ⟨g • P, P.2.map _, λ Q hQ hS, inv_smul_eq_iff.mp (P.3 (hQ.map _)
    (λ s hs, (congr_arg (∈ g⁻¹ • Q) (inv_smul_smul g s)).mp
      (smul_mem_pointwise_smul (g • s) g⁻¹ Q (hS (smul_mem_pointwise_smul s g P hs)))))⟩,
  one_smul := λ P, sylow.ext (one_smul α P),
  mul_smul := λ g h P, sylow.ext (mul_smul g h P) }

lemma sylow.pointwise_smul_def {α : Type*} [group α] [mul_distrib_mul_action α G]
  {g : α} {P : sylow p G} : ↑(g • P) = g • (P : subgroup G) := rfl

instance sylow.mul_action : mul_action G (sylow p G) :=
comp_hom _ mul_aut.conj

lemma sylow.smul_def {g : G} {P : sylow p G} : g • P = mul_aut.conj g • P := rfl

lemma sylow.coe_subgroup_smul {g : G} {P : sylow p G} :
  ↑(g • P) = mul_aut.conj g • (P : subgroup G) := rfl

lemma sylow.coe_smul {g : G} {P : sylow p G} :
  ↑(g • P) = mul_aut.conj g • (P : set G) := rfl

lemma sylow.smul_eq_iff_mem_normalizer {g : G} {P : sylow p G} :
  g • P = P ↔ g ∈ (P : subgroup G).normalizer :=
begin
  rw [eq_comm, set_like.ext_iff, ←inv_mem_iff, mem_normalizer_iff, inv_inv],
  exact forall_congr (λ h, iff_congr iff.rfl ⟨λ ⟨a, b, c⟩, (congr_arg _ c).mp
    ((congr_arg (∈ P.1) (mul_aut.inv_apply_self G (mul_aut.conj g) a)).mpr b),
    λ hh, ⟨(mul_aut.conj g)⁻¹ h, hh, mul_aut.apply_inv_self G (mul_aut.conj g) h⟩⟩),
end

lemma sylow.smul_eq_of_normal {g : G} {P : sylow p G} [h : (P : subgroup G).normal] :
  g • P = P :=
by simp only [sylow.smul_eq_iff_mem_normalizer, normalizer_eq_top.mpr h, mem_top]

lemma subgroup.sylow_mem_fixed_points_iff (H : subgroup G) {P : sylow p G} :
  P ∈ fixed_points H (sylow p G) ↔ H ≤ (P : subgroup G).normalizer :=
by simp_rw [set_like.le_def, ←sylow.smul_eq_iff_mem_normalizer]; exact subtype.forall

lemma is_p_group.inf_normalizer_sylow {P : subgroup G} (hP : is_p_group p P) (Q : sylow p G) :
  P ⊓ (Q : subgroup G).normalizer = P ⊓ Q :=
le_antisymm (le_inf inf_le_left (sup_eq_right.mp (Q.3 (hP.to_inf_left.to_sup_of_normal_right'
  Q.2 inf_le_right) le_sup_right))) (inf_le_inf_left P le_normalizer)

lemma is_p_group.sylow_mem_fixed_points_iff
  {P : subgroup G} (hP : is_p_group p P) {Q : sylow p G} :
  Q ∈ fixed_points P (sylow p G) ↔ P ≤ Q :=
by rw [P.sylow_mem_fixed_points_iff, ←inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]

/-- A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
instance [hp : fact p.prime] [fintype (sylow p G)] : is_pretransitive G (sylow p G) :=
⟨λ P Q, by
{ classical,
  have H := λ {R : sylow p G} {S : orbit G P},
  calc S ∈ fixed_points R (orbit G P)
      ↔ S.1 ∈ fixed_points R (sylow p G) : forall_congr (λ a, subtype.ext_iff)
  ... ↔ R.1 ≤ S : R.2.sylow_mem_fixed_points_iff
  ... ↔ S.1.1 = R : ⟨λ h, R.3 S.1.2 h, ge_of_eq⟩,
  suffices : set.nonempty (fixed_points Q (orbit G P)),
  { exact exists.elim this (λ R hR, (congr_arg _ (sylow.ext (H.mp hR))).mp R.2) },
  apply Q.2.nonempty_fixed_point_of_prime_not_dvd_card,
  refine λ h, hp.out.not_dvd_one (nat.modeq_zero_iff_dvd.mp _),
  calc 1 = card (fixed_points P (orbit G P)) : _
     ... ≡ card (orbit G P) [MOD p] : (P.2.card_modeq_card_fixed_points (orbit G P)).symm
     ... ≡ 0 [MOD p] : nat.modeq_zero_iff_dvd.mpr h,
  rw ← set.card_singleton (⟨P, mem_orbit_self P⟩ : orbit G P),
  refine card_congr' (congr_arg _ (eq.symm _)),
  rw set.eq_singleton_iff_unique_mem,
  exact ⟨H.mpr rfl, λ R h, subtype.ext (sylow.ext (H.mp h))⟩ }⟩

variables (p) (G)

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
lemma card_sylow_modeq_one [fact p.prime] [fintype (sylow p G)] : card (sylow p G) ≡ 1 [MOD p] :=
begin
  refine sylow.nonempty.elim (λ P : sylow p G, _),
  have : fixed_points P.1 (sylow p G) = {P} :=
  set.ext (λ Q : sylow p G, calc Q ∈ fixed_points P (sylow p G)
      ↔ P.1 ≤ Q : P.2.sylow_mem_fixed_points_iff
  ... ↔ Q.1 = P.1 : ⟨P.3 Q.2, ge_of_eq⟩
  ... ↔ Q ∈ {P} : sylow.ext_iff.symm.trans set.mem_singleton_iff.symm),
  haveI : fintype (fixed_points P.1 (sylow p G)), { rw this, apply_instance },
  have : card (fixed_points P.1 (sylow p G)) = 1, { simp [this] },
  exact (P.2.card_modeq_card_fixed_points (sylow p G)).trans (by rw this),
end

variables {p} {G}

/-- Sylow subgroups are isomorphic -/
def sylow.equiv_smul (P : sylow p G) (g : G) : P ≃* (g • P : sylow p G) :=
equiv_smul (mul_aut.conj g) P.1

/-- Sylow subgroups are isomorphic -/
noncomputable def sylow.equiv [fact p.prime] [fintype (sylow p G)] (P Q : sylow p G) :
  P ≃* Q :=
begin
  rw ← classical.some_spec (exists_smul_eq G P Q),
  exact P.equiv_smul (classical.some (exists_smul_eq G P Q)),
end

@[simp] lemma sylow.orbit_eq_top [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
  orbit G P = ⊤ :=
top_le_iff.mp (λ Q hQ, exists_smul_eq G P Q)

lemma sylow.stabilizer_eq_normalizer (P : sylow p G) : stabilizer G P = P.1.normalizer :=
ext (λ g, sylow.smul_eq_iff_mem_normalizer)

/-- Sylow `p`-subgroups are in bijection with cosets of the normalizer of a Sylow `p`-subgroup -/
noncomputable def sylow.equiv_quotient_normalizer [fact p.prime] [fintype (sylow p G)]
  (P : sylow p G) : sylow p G ≃ G ⧸ P.1.normalizer :=
calc sylow p G ≃ (⊤ : set (sylow p G)) : (equiv.set.univ (sylow p G)).symm
... ≃ orbit G P : by rw P.orbit_eq_top
... ≃ G ⧸ (stabilizer G P) : orbit_equiv_quotient_stabilizer G P
... ≃ G ⧸ P.1.normalizer : by rw P.stabilizer_eq_normalizer

noncomputable instance [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
  fintype (G ⧸ P.1.normalizer) :=
of_equiv (sylow p G) P.equiv_quotient_normalizer

lemma card_sylow_eq_card_quotient_normalizer [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
  card (sylow p G) = card (G ⧸ P.1.normalizer) :=
card_congr P.equiv_quotient_normalizer

lemma card_sylow_eq_index_normalizer [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
  card (sylow p G) = P.1.normalizer.index :=
(card_sylow_eq_card_quotient_normalizer P).trans P.1.normalizer.index_eq_card.symm

lemma card_sylow_dvd_index [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
  card (sylow p G) ∣ P.1.index :=
((congr_arg _ (card_sylow_eq_index_normalizer P)).mp dvd_rfl).trans (index_dvd_of_le le_normalizer)

/-- Frattini's Argument: If `N` is a normal subgroup of `G`, and if `P` is a Sylow `p`-subgroup
  of `N`, then `N_G(P) ⊔ N = G`. -/
lemma sylow.normalizer_sup_eq_top {p : ℕ} [fact p.prime] {N : subgroup G} [N.normal]
  [fintype (sylow p N)] (P : sylow p N) : ((↑P : subgroup N).map N.subtype).normalizer ⊔ N = ⊤ :=
begin
  refine top_le_iff.mp (λ g hg, _),
  obtain ⟨n, hn⟩ := exists_smul_eq N ((mul_aut.conj_normal g : mul_aut N) • P) P,
  rw [←inv_mul_cancel_left ↑n g, sup_comm],
  apply mul_mem_sup (N.inv_mem n.2),
  rw [sylow.smul_def, ←mul_smul, ←mul_aut.conj_normal_coe, ←mul_aut.conj_normal.map_mul,
      sylow.ext_iff, sylow.pointwise_smul_def, pointwise_smul_def] at hn,
  refine λ x, (mem_map_iff_mem (show function.injective (mul_aut.conj (↑n * g)).to_monoid_hom,
    from (mul_aut.conj (↑n * g)).injective)).symm.trans _,
  rw [map_map, ←(congr_arg (map N.subtype) hn), map_map],
  refl,
end

end infinite_sylow

open equiv equiv.perm finset function list quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

lemma quotient_group.card_preimage_mk [fintype G] (s : subgroup G)
  (t : set (G ⧸ s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

open subgroup submonoid mul_action

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : subgroup G}
  [fintype ((H : set G) : Type u)] {x : G} :
  (x : G ⧸ H) ∈ fixed_points H (G ⧸ H) ↔ x ∈ normalizer H :=
⟨λ hx, have ha : ∀ {y : G ⧸ H}, y ∈ orbit H (x : G ⧸ H) → y = x,
  from λ _, ((mem_fixed_points' _).1 hx _),
  (inv_mem_iff _).1 (@mem_normalizer_fintype _ _ _ _inst_2 _ (λ n (hn : n ∈ H),
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient_group.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩)),
    show _ ∈ H, by {rw [mul_inv_rev, inv_inv] at this, convert this, rw inv_inv}
    )),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H),
(mem_fixed_points' _).2 $ λ y, quotient.induction_on' y $ λ y hy, quotient_group.eq.2
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient_group.eq.1 hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_left H (H.inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

def fixed_points_mul_left_cosets_equiv_quotient (H : subgroup G) [fintype (H : set G)] :
  mul_action.fixed_points H (G ⧸ H) ≃
  normalizer H ⧸ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
@subtype_quotient_equiv_quotient_subtype G (normalizer H : set G) (id _) (id _) (fixed_points _ _)
  (λ a, (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
  (by intros; refl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
lemma card_quotient_normalizer_modeq_card_quotient [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (normalizer H ⧸ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H))
  ≡ card (G ⧸ H) [MOD p] :=
begin
  rw [← fintype.card_congr (fixed_points_mul_left_cosets_equiv_quotient H)],
  exact ((is_p_group.of_card hH).card_modeq_card_fixed_points _).symm
end

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
lemma card_normalizer_modeq_card [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (normalizer H) ≡ card G [MOD p ^ (n + 1)] :=
have subgroup.comap ((normalizer H).subtype : normalizer H →* G) H ≃ H,
  from set.bij_on.equiv (normalizer H).subtype
    ⟨λ _, id, λ _ _ _ _ h, subtype.val_injective h,
      λ x hx, ⟨⟨x, le_normalizer hx⟩, hx, rfl⟩⟩,
begin
  rw [card_eq_card_quotient_mul_card_subgroup H,
      card_eq_card_quotient_mul_card_subgroup
        (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H),
      fintype.card_congr this, hH, pow_succ],
  exact (card_quotient_normalizer_modeq_card_quotient hH).mul_right' _
end

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
lemma prime_dvd_card_quotient_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ∣ card (normalizer H ⧸ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (G ⧸ H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (normalizer H ⧸ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  hcard ▸ (card_quotient_normalizer_modeq_card_quotient hH).symm,
nat.dvd_of_mod_eq_zero
  (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
lemma prime_pow_dvd_card_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ^ (n + 1) ∣ card (normalizer H) :=
nat.modeq_zero_iff_dvd.1 ((card_normalizer_modeq_card hH).trans
  hdvd.modeq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  ∃ K : subgroup G, fintype.card K = p ^ (n + 1) ∧ H ≤ K :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (G ⧸ H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (normalizer H ⧸ (subgroup.comap (normalizer H).subtype H)) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸ hcard ▸
    (is_p_group.of_card hH).card_modeq_card_fixed_points _,
have hm' : p ∣ card (normalizer H ⧸ (subgroup.comap (normalizer H).subtype H)) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (quotient_group.quotient.group _) _ _ hp hm' in
have hequiv : H ≃ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  ⟨λ a, ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, λ a, ⟨a.1.1, a.2⟩,
    λ ⟨_, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩,
⟨subgroup.map ((normalizer H).subtype) (subgroup.comap
  (quotient_group.mk' (comap H.normalizer.subtype H)) (zpowers x)),
begin
  show card ↥(map H.normalizer.subtype
    (comap (mk' (comap H.normalizer.subtype H)) (subgroup.zpowers x))) = p ^ (n + 1),
  suffices : card ↥(subtype.val '' ((subgroup.comap (mk' (comap H.normalizer.subtype H))
    (zpowers x)) : set (↥(H.normalizer)))) = p^(n+1),
  { convert this using 2 },
  rw [set.card_image_of_injective
        (subgroup.comap (mk' (comap H.normalizer.subtype H)) (zpowers x) : set (H.normalizer))
        subtype.val_injective,
      pow_succ', ← hH, fintype.card_congr hequiv, ← hx, order_eq_card_zpowers,
      ← fintype.card_prod],
  exact @fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _)
end,
begin
  assume y hy,
  simp only [exists_prop, subgroup.coe_subtype, mk'_apply, subgroup.mem_map, subgroup.mem_comap],
  refine ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩,
  rw [zpow_zero, eq_comm, quotient_group.eq_one_iff],
  simpa using hy
end⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [fintype G] (p : ℕ) : ∀ {n m : ℕ} [hp : fact p.prime]
  (hdvd : p ^ m ∣ card G) (H : subgroup G) (hH : card H = p ^ n) (hnm : n ≤ m),
  ∃ K : subgroup G, card K = p ^ m ∧ H ≤ K
| n m := λ hp hdvd H hH hnm,
  (lt_or_eq_of_le hnm).elim
    (λ hnm : n < m,
      have h0m : 0 < m, from (lt_of_le_of_lt n.zero_le hnm),
      have wf : m - 1 < m,  from nat.sub_lt h0m zero_lt_one,
      have hnm1 : n ≤ m - 1, from le_tsub_of_add_le_right hnm,
      let ⟨K, hK⟩ := @exists_subgroup_card_pow_prime_le n (m - 1) hp
        (nat.pow_dvd_of_le_of_pow_dvd tsub_le_self hdvd) H hH hnm1 in
      have hdvd' : p ^ ((m - 1) + 1) ∣ card G, by rwa [tsub_add_cancel_of_le h0m.nat_succ_le],
      let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ hp hdvd' K hK.1 in
      ⟨K', by rw [hK'.1, tsub_add_cancel_of_le h0m.nat_succ_le], le_trans hK.2 hK'.2⟩)
    (λ hnm : n = m, ⟨H, by simp [hH, hnm]⟩)

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [fintype G] (p : ℕ) {n : ℕ} [fact p.prime]
  (hdvd : p ^ n ∣ card G) : ∃ K : subgroup G, fintype.card K = p ^ n :=
let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥ (by simp) n.zero_le in
⟨K, hK.1⟩

lemma pow_dvd_card_of_pow_dvd_card [fintype G] {p n : ℕ} [fact p.prime] (P : sylow p G)
  (hdvd : p ^ n ∣ card G) : p ^ n ∣ card P :=
begin
  obtain ⟨Q, hQ⟩ := exists_subgroup_card_pow_prime p hdvd,
  obtain ⟨R, hR⟩ := (is_p_group.of_card hQ).exists_le_sylow,
  obtain ⟨g, rfl⟩ := exists_smul_eq G R P,
  calc p ^ n = card Q : hQ.symm
  ... ∣ card R : card_dvd_of_le hR
  ... = card (g • R) : card_congr (R.equiv_smul g).to_equiv
end

lemma dvd_card_of_dvd_card [fintype G] {p : ℕ} [fact p.prime] (P : sylow p G)
  (hdvd : p ∣ card G) : p ∣ card P :=
begin
  rw ← pow_one p at hdvd,
  have key := P.pow_dvd_card_of_pow_dvd_card hdvd,
  rwa pow_one at key,
end

lemma ne_bot_of_dvd_card [fintype G] {p : ℕ} [hp : fact p.prime] (P : sylow p G)
  (hdvd : p ∣ card G) : (P : subgroup G) ≠ ⊥ :=
begin
  refine λ h, hp.out.not_dvd_one _,
  have key : p ∣ card (P : subgroup G) := P.dvd_card_of_dvd_card hdvd,
  rwa [h, card_bot] at key,
end

/-- The cardinality of a Sylow group is `p ^ n`
 where `n` is the multiplicity of `p` in the group order. -/
lemma card_eq_multiplicity [fintype G] {p : ℕ} [hp : fact p.prime] (P : sylow p G) :
  card P = p ^ nat.factorization (card G) p :=
begin
  obtain ⟨n, heq : card P = _⟩ := is_p_group.iff_card.mp (P.is_p_group'),
  refine nat.dvd_antisymm _ (P.pow_dvd_card_of_pow_dvd_card (nat.pow_factorization_dvd _ p)),
  rw [heq, ←hp.out.pow_dvd_iff_dvd_pow_factorization (show card G ≠ 0, from card_ne_zero), ←heq],
  exact P.1.card_subgroup_dvd_card,
end

lemma subsingleton_of_normal {p : ℕ} [fact p.prime] [fintype (sylow p G)] (P : sylow p G)
  (h : (P : subgroup G).normal) : subsingleton (sylow p G) :=
begin
  apply subsingleton.intro,
  intros Q R,
  obtain ⟨x, h1⟩ := exists_smul_eq G P Q,
  obtain ⟨x, h2⟩ := exists_smul_eq G P R,
  rw sylow.smul_eq_of_normal at h1 h2,
  rw [← h1, ← h2],
end

section pointwise

open_locale pointwise

lemma characteristic_of_normal {p : ℕ} [fact p.prime] [fintype (sylow p G)] (P : sylow p G)
  (h : (P : subgroup G).normal) :
  (P : subgroup G).characteristic :=
begin
  haveI := sylow.subsingleton_of_normal P h,
  rw characteristic_iff_map_eq,
  intros Φ,
  show (Φ • P).to_subgroup = P.to_subgroup,
  congr,
end

end pointwise

/-- The preimage of a Sylow subgroup under a homomorphism with p-group-kernel is a Sylow subgroup -/
def comap_of_ker_is_p_group {p : ℕ} (P : sylow p G)
  {K : Type*} [group K] (ϕ : K →* G) (hϕ : is_p_group p ϕ.ker) (h : P.1 ≤ ϕ.range) :
  sylow p K :=
{ P.1.comap ϕ with
  is_p_group' := P.2.comap_of_ker_is_p_group ϕ hϕ,
  is_maximal' := λ Q hQ hle, by
  { rw ← P.3 (hQ.map ϕ) (le_trans (ge_of_eq (map_comap_eq_self h)) (map_mono hle)),
    exact (comap_map_eq_self ((P.1.ker_le_comap ϕ).trans hle)).symm }, }

@[simp]
lemma coe_comap_of_ker_is_p_group {p : ℕ} {P : sylow p G}
  {K : Type*} [group K] (ϕ : K →* G) (hϕ : is_p_group p ϕ.ker) (h : P.1 ≤ ϕ.range) :
  ↑(P.comap_of_ker_is_p_group ϕ hϕ h) = subgroup.comap ϕ ↑P := rfl

/-- The preimage of a Sylow subgroup under an injective homomorphism is a Sylow subgroup -/
def comap_of_injective {p : ℕ} (P : sylow p G)
  {K : Type*} [group K] (ϕ : K →* G) (hϕ : function.injective ϕ) (h : P.1 ≤ ϕ.range) :
  sylow p K :=
P.comap_of_ker_is_p_group ϕ (is_p_group.ker_is_p_group_of_injective hϕ) h

@[simp]
lemma coe_comap_of_injective {p : ℕ} {P : sylow p G}
  {K : Type*} [group K] (ϕ : K →* G) (hϕ : function.injective ϕ) (h : P.1 ≤ ϕ.range)  :
  ↑(P.comap_of_injective ϕ hϕ h) = subgroup.comap ϕ ↑P := rfl

/-- A sylow subgroup in G is also a sylow subgroup in a subgroup of G. -/
def subtype {p : ℕ} (P : sylow p G) (N : subgroup G) (h : ↑P ≤ N) : sylow p N :=
P.comap_of_injective N.subtype subtype.coe_injective (by simp [h])

@[simp]
lemma coe_subtype {p : ℕ} {P : sylow p G} {N : subgroup G} {h : P.1 ≤ N} :
  ↑(P.subtype N h) = subgroup.comap N.subtype ↑P := rfl

lemma normal_of_normalizer_normal {p : ℕ} [fact p.prime] [fintype (sylow p G)]
  (P : sylow p G) (hn : (↑P : subgroup G).normalizer.normal) :
  (↑P : subgroup G).normal :=
by rw [←normalizer_eq_top, ←normalizer_sup_eq_top (P.subtype _ le_normalizer), coe_subtype,
  map_comap_eq_self (le_normalizer.trans (ge_of_eq (subtype_range _))), sup_idem]

@[simp] lemma normalizer_normalizer {p : ℕ} [fact p.prime] [fintype (sylow p G)]
 (P : sylow p G) :
 (↑P : subgroup G).normalizer.normalizer = (↑P : subgroup G).normalizer :=
begin
  have := normal_of_normalizer_normal (P.subtype _ (le_normalizer.trans le_normalizer)),
  simp_rw [←normalizer_eq_top, coe_subtype, ←comap_subtype_normalizer_eq le_normalizer,
    ←comap_subtype_normalizer_eq le_rfl, comap_subtype_self_eq_top] at this,
  rw [←subtype_range (P : subgroup G).normalizer.normalizer, monoid_hom.range_eq_map, ←this rfl],
  exact map_comap_eq_self (le_normalizer.trans (ge_of_eq (subtype_range _))),
end

lemma normal_of_all_max_subgroups_normal [fintype G]
  (hnc : ∀ (H : subgroup G), is_coatom H → H.normal)
  {p : ℕ} [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
  (↑P : subgroup G).normal :=
normalizer_eq_top.mp begin
  rcases eq_top_or_exists_le_coatom ((↑P : subgroup G).normalizer) with heq | ⟨K, hK, hNK⟩,
  { exact heq },
  { haveI := hnc _ hK,
    have hPK := le_trans le_normalizer hNK,
    let P' := P.subtype K hPK,
    exfalso,
    apply hK.1,
    calc K = (↑P : subgroup G).normalizer ⊔ K : by { rw sup_eq_right.mpr, exact hNK }
    ... = (map K.subtype (↑P' : subgroup K)).normalizer ⊔ K : by simp [map_comap_eq_self, hPK]
    ... = ⊤ : normalizer_sup_eq_top P' },
end

lemma normal_of_normalizer_condition (hnc : normalizer_condition G)
 {p : ℕ} [fact p.prime] [fintype (sylow p G)] (P : sylow p G) :
 (↑P : subgroup G).normal :=
normalizer_eq_top.mp $ normalizer_condition_iff_only_full_group_self_normalizing.mp hnc _ $
  normalizer_normalizer _

end sylow
