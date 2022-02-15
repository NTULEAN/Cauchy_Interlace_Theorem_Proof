/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import measure_theory.group.measurable_equiv
import measure_theory.measure.regular
import dynamics.ergodic.measure_preserving
import dynamics.minimal

/-!
# Measures invariant under group actions

A measure `μ : measure α` is said to be *invariant* under an action of a group `G` if scalar
multiplication by `c : G` is a measure preserving map for all `c`. In this file we define a
typeclass for measures invariant under action of an (additive or multiplicative) group and prove
some basic properties of such measures.
-/

open_locale ennreal nnreal pointwise topological_space
open measure_theory measure_theory.measure set function

namespace measure_theory

variables {G M α : Type*}

/-- A measure `μ : measure α` is invariant under an additive action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c +ᵥ x` is equal to
the measure of `s`. -/
class vadd_invariant_measure (M α : Type*) [has_vadd M α] {_ : measurable_space α}
  (μ : measure α) : Prop :=
(measure_preimage_vadd [] : ∀ (c : M) ⦃s : set α⦄, measurable_set s → μ ((λ x, c +ᵥ x) ⁻¹' s) = μ s)

/-- A measure `μ : measure α` is invariant under a multiplicative action of `M` on `α` if for any
measurable set `s : set α` and `c : M`, the measure of its preimage under `λ x, c • x` is equal to
the measure of `s`. -/
@[to_additive] class smul_invariant_measure (M α : Type*) [has_scalar M α] {_ : measurable_space α}
  (μ : measure α) : Prop :=
(measure_preimage_smul [] : ∀ (c : M) ⦃s : set α⦄, measurable_set s → μ ((λ x, c • x) ⁻¹' s) = μ s)

namespace smul_invariant_measure

@[to_additive] instance zero [measurable_space α] [has_scalar M α] : smul_invariant_measure M α 0 :=
⟨λ _ _ _, rfl⟩

variables [has_scalar M α] {m : measurable_space α} {μ ν : measure α}

@[to_additive] instance add [smul_invariant_measure M α μ] [smul_invariant_measure M α ν] :
  smul_invariant_measure M α (μ + ν) :=
⟨λ c s hs, show _ + _ = _ + _,
  from congr_arg2 (+) (measure_preimage_smul μ c hs) (measure_preimage_smul ν c hs)⟩

@[to_additive] instance smul [smul_invariant_measure M α μ] (c : ℝ≥0∞) :
  smul_invariant_measure M α (c • μ) :=
⟨λ a s hs, show c • _ = c • _, from congr_arg ((•) c) (measure_preimage_smul μ a hs)⟩

@[to_additive] instance smul_nnreal [smul_invariant_measure M α μ] (c : ℝ≥0) :
  smul_invariant_measure M α (c • μ) :=
smul_invariant_measure.smul c

end smul_invariant_measure

variables (G) {m : measurable_space α} [group G] [mul_action G α] [measurable_space G]
  [has_measurable_smul G α] (c : G) (μ : measure α)

/-- Equivalent definitions of a measure invariant under a multiplicative action of a group.

- 0: `smul_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under scalar
     multiplication by `c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c • s` of `s` under
     scalar multiplication by `c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, scalar multiplication by `c` maps `μ` to `μ`;

- 6: for any `c : G`, scalar multiplication by `c` is a measure preserving map. -/
@[to_additive] lemma smul_invariant_measure_tfae :
  tfae [smul_invariant_measure G α μ,
    ∀ (c : G) s, measurable_set s → μ (((•) c) ⁻¹' s) = μ s,
    ∀ (c : G) s, measurable_set s → μ (c • s) = μ s,
    ∀ (c : G) s, μ (((•) c) ⁻¹' s) = μ s,
    ∀ (c : G) s, μ (c • s) = μ s,
    ∀ c : G, measure.map ((•) c) μ = μ,
    ∀ c : G, measure_preserving ((•) c) μ μ] :=
begin
  tfae_have : 1 ↔ 2, from ⟨λ h, h.1, λ h, ⟨h⟩⟩,
  tfae_have : 2 → 6,
    from λ H c, ext (λ s hs, by rw [map_apply (measurable_const_smul c) hs, H _ _ hs]),
  tfae_have : 6 → 7, from λ H c, ⟨measurable_const_smul c, H c⟩,
  tfae_have : 7 → 4, from λ H c, (H c).measure_preimage_emb (measurable_embedding_const_smul c),
  tfae_have : 4 → 5, from λ H c s, by { rw [← preimage_smul_inv], apply H },
  tfae_have : 5 → 3, from λ H c s hs, H c s,
  tfae_have : 3 → 2, { intros H c s hs, rw preimage_smul, exact H c⁻¹ s hs },
  tfae_finish
end

/-- Equivalent definitions of a measure invariant under an additive action of a group.

- 0: `vadd_invariant_measure G α μ`;

- 1: for every `c : G` and a measurable set `s`, the measure of the preimage of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 2: for every `c : G` and a measurable set `s`, the measure of the image `c +ᵥ s` of `s` under
     vector addition `(+ᵥ) c` is equal to the measure of `s`;

- 3, 4: properties 2, 3 for any set, including non-measurable ones;

- 5: for any `c : G`, vector addition of `c` maps `μ` to `μ`;

- 6: for any `c : G`, vector addition of `c` is a measure preserving map. -/
add_decl_doc vadd_invariant_measure_tfae

variables {G} [smul_invariant_measure G α μ]

@[to_additive] lemma measure_preserving_smul : measure_preserving ((•) c) μ μ :=
((smul_invariant_measure_tfae G μ).out 0 6).mp ‹_› c

@[simp, to_additive] lemma map_smul : map ((•) c) μ = μ :=
(measure_preserving_smul c μ).map_eq

@[simp, to_additive] lemma measure_preimage_smul (s : set α) : μ ((•) c ⁻¹' s) = μ s :=
((smul_invariant_measure_tfae G μ).out 0 3).mp ‹_› c s

@[simp, to_additive] lemma measure_smul_set (s : set α) : μ (c • s) = μ s :=
((smul_invariant_measure_tfae G μ).out 0 4).mp ‹_› c s

section is_minimal

variables (G) {μ} [topological_space G] [topological_space α] [has_continuous_smul G α]
  [mul_action.is_minimal G α] {K U : set α}

/-- If measure `μ` is invariant under a group action and is nonzero on a compact set `K`, then it is
positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0` instead of
`μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_smul_invariant_of_ne_zero`. -/
@[to_additive] lemma measure_is_open_pos_of_smul_invariant_of_compact_ne_zero (hK : is_compact K)
  (hμK : μ K ≠ 0) (hU : is_open U) (hne : U.nonempty) : 0 < μ U :=
let ⟨t, ht⟩ := hK.exists_finite_cover_smul G hU hne
in pos_iff_ne_zero.2 $ λ hμU, hμK $ measure_mono_null ht $
  (measure_bUnion_null_iff t.countable_to_set).2 $ λ _ _, by rwa measure_smul_set

/-- If measure `μ` is invariant under an additive group action and is nonzero on a compact set `K`,
then it is positive on any nonempty open set. In case of a regular measure, one can assume `μ ≠ 0`
instead of `μ K ≠ 0`, see `measure_theory.measure_is_open_pos_of_vadd_invariant_of_ne_zero`. -/
add_decl_doc measure_is_open_pos_of_vadd_invariant_of_compact_ne_zero

@[to_additive] lemma is_locally_finite_measure_of_smul_invariant (hU : is_open U) (hne : U.nonempty)
  (hμU : μ U ≠ ∞) : is_locally_finite_measure μ :=
⟨λ x, let ⟨g, hg⟩ := hU.exists_smul_mem G x hne in
  ⟨(•) g ⁻¹' U, (hU.preimage (continuous_id.const_smul _)).mem_nhds hg, ne.lt_top $
    by rwa [measure_preimage_smul]⟩⟩

variables [measure.regular μ]

@[to_additive] lemma measure_is_open_pos_of_smul_invariant_of_ne_zero (hμ : μ ≠ 0) (hU : is_open U)
  (hne : U.nonempty) : 0 < μ U :=
let ⟨K, hK, hμK⟩ := regular.exists_compact_not_null.mpr hμ
in measure_is_open_pos_of_smul_invariant_of_compact_ne_zero G hK hμK hU hne

@[to_additive] lemma measure_pos_iff_nonempty_of_smul_invariant (hμ : μ ≠ 0) (hU : is_open U) :
  0 < μ U ↔ U.nonempty :=
⟨λ h, nonempty_of_measure_ne_zero h.ne', measure_is_open_pos_of_smul_invariant_of_ne_zero G hμ hU⟩

include G

@[to_additive] lemma measure_eq_zero_iff_eq_empty_of_smul_invariant (hμ : μ ≠ 0) (hU : is_open U) :
  μ U = 0 ↔ U = ∅ :=
by rw [← not_iff_not, ← ne.def, ← pos_iff_ne_zero,
  measure_pos_iff_nonempty_of_smul_invariant G hμ hU, ← ne_empty_iff_nonempty]

end is_minimal

end measure_theory
