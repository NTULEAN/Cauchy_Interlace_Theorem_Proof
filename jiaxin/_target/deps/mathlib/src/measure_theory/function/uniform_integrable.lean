/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import measure_theory.integral.set_integral

/-!
# Uniform integrability

This file will be used in the future to define uniform integrability. Uniform integrability
is an important notion in both measure theory as well as probability theory. So far this file
only contains the Egorov theorem which will be used to prove the Vitali convergence theorem
which is one of the main results about uniform integrability.

## Main results

* `measure_theory.egorov`: Egorov's theorem which shows that a sequence of almost everywhere
  convergent functions converges uniformly except on an arbitrarily small set.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal topological_space

namespace measure_theory

open set filter topological_space

variables {α β ι : Type*} {m : measurable_space α} [metric_space β] {μ : measure α}

section

/-! We will in this section prove Egorov's theorem. -/

namespace egorov

/-- Given a sequence of functions `f` and a function `g`, `not_convergent_seq f g i j` is the
set of elements such that `f k x` and `g x` are separated by at least `1 / (i + 1)` for some
`k ≥ j`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq (f : ℕ → α → β) (g : α → β) (i j : ℕ) : set α :=
⋃ k (hk : j ≤ k), {x | (1 / (i + 1 : ℝ)) < dist (f k x) (g x)}

variables {i j : ℕ} {s : set α} {ε : ℝ} {f : ℕ → α → β} {g : α → β}

lemma mem_not_convergent_seq_iff {x : α} : x ∈ not_convergent_seq f g i j ↔
  ∃ k (hk : j ≤ k), (1 / (i + 1 : ℝ)) < dist (f k x) (g x) :=
by { simp_rw [not_convergent_seq, mem_Union], refl }

lemma not_convergent_seq_antitone :
  antitone (not_convergent_seq f g i) :=
λ j k hjk, Union₂_mono' $ λ l hl, ⟨l, le_trans hjk hl, subset.rfl⟩

lemma measure_inter_not_convergent_seq_eq_zero
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  μ (s ∩ ⋂ j, not_convergent_seq f g i j) = 0 :=
begin
  simp_rw [metric.tendsto_at_top, ae_iff] at hfg,
  rw [← nonpos_iff_eq_zero, ← hfg],
  refine measure_mono (λ x, _),
  simp only [mem_inter_eq, mem_Inter, ge_iff_le, mem_not_convergent_seq_iff],
  push_neg,
  rintro ⟨hmem, hx⟩,
  refine ⟨hmem, 1 / (i + 1 : ℝ), nat.one_div_pos_of_nat, λ N, _⟩,
  obtain ⟨n, hn₁, hn₂⟩ := hx N,
  exact ⟨n, hn₁, hn₂.le⟩
end

variables [second_countable_topology β] [measurable_space β] [borel_space β]

lemma not_convergent_seq_measurable_set
  (hf : ∀ n, measurable[m] (f n)) (hg : measurable g) :
  measurable_set (not_convergent_seq f g i j) :=
measurable_set.Union (λ k, measurable_set.Union_Prop $ λ hk,
  measurable_set_lt measurable_const $ (hf k).dist hg)

lemma measure_not_convergent_seq_tendsto_zero
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  tendsto (λ j, μ (s ∩ not_convergent_seq f g i j)) at_top (𝓝 0) :=
begin
  rw [← measure_inter_not_convergent_seq_eq_zero hfg, inter_Inter],
  exact tendsto_measure_Inter (λ n, hsm.inter $ not_convergent_seq_measurable_set hf hg)
    (λ k l hkl, inter_subset_inter_right _ $ not_convergent_seq_antitone hkl)
    ⟨0, (lt_of_le_of_lt (measure_mono $ inter_subset_left _ _) (lt_top_iff_ne_top.2 hs)).ne⟩
end

lemma exists_not_convergent_seq_lt (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  ∃ j : ℕ, μ (s ∩ not_convergent_seq f g i j) ≤ ennreal.of_real (ε * 2⁻¹ ^ i) :=
begin
  obtain ⟨N, hN⟩ := (ennreal.tendsto_at_top ennreal.zero_ne_top).1
    (measure_not_convergent_seq_tendsto_zero hf hg hsm hs hfg i)
    (ennreal.of_real (ε * 2⁻¹ ^ i)) _,
  { rw zero_add at hN,
    exact ⟨N, (hN N le_rfl).2⟩ },
  { rw [gt_iff_lt, ennreal.of_real_pos],
    exact mul_pos hε (pow_pos (by norm_num) _) }
end

/-- Given some `ε > 0`, `not_convergent_seq_lt_index` provides the index such that
`not_convergent_seq` (intersected with a set of finite measure) has measure less than
`ε * 2⁻¹ ^ i`.

This definition is useful for Egorov's theorem. -/
def not_convergent_seq_lt_index (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) : ℕ :=
classical.some $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

lemma not_convergent_seq_lt_index_spec (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) (i : ℕ) :
  μ (s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index hε hf hg hsm hs hfg i)) ≤
  ennreal.of_real (ε * 2⁻¹ ^ i) :=
classical.some_spec $ exists_not_convergent_seq_lt hε hf hg hsm hs hfg i

/-- Given some `ε > 0`, `Union_not_convergent_seq` is the union of `not_convergent_seq` with
specific indicies such that `Union_not_convergent_seq` has measure less equal than `ε`.

This definition is useful for Egorov's theorem. -/
def Union_not_convergent_seq (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) : set α :=
⋃ i, s ∩ not_convergent_seq f g i (not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg i)

lemma Union_not_convergent_seq_measurable_set (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  measurable_set $ Union_not_convergent_seq hε hf hg hsm hs hfg :=
measurable_set.Union (λ n, hsm.inter $ not_convergent_seq_measurable_set hf hg)

lemma measure_Union_not_convergent_seq (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  μ (Union_not_convergent_seq hε hf hg hsm hs hfg) ≤ ennreal.of_real ε :=
begin
  refine le_trans (measure_Union_le _)
    (le_trans (ennreal.tsum_le_tsum $ not_convergent_seq_lt_index_spec
    (half_pos hε) hf hg hsm hs hfg) _),
  simp_rw [ennreal.of_real_mul (half_pos hε).le],
  rw [ennreal.tsum_mul_left, ← ennreal.of_real_tsum_of_nonneg, inv_eq_one_div,
      tsum_geometric_two, ← ennreal.of_real_mul (half_pos hε).le, div_mul_cancel ε two_ne_zero],
  { exact le_rfl },
  { exact λ n, pow_nonneg (by norm_num) _ },
  { rw [inv_eq_one_div],
    exact summable_geometric_two },
end

lemma Union_not_convergent_seq_subset (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  Union_not_convergent_seq hε hf hg hsm hs hfg ⊆ s :=
begin
  rw [Union_not_convergent_seq, ← inter_Union],
  exact inter_subset_left _ _,
end

lemma tendsto_uniformly_on_diff_Union_not_convergent_seq (hε : 0 < ε)
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) :
  tendsto_uniformly_on f g at_top (s \ egorov.Union_not_convergent_seq hε hf hg hsm hs hfg) :=
begin
  rw metric.tendsto_uniformly_on_iff,
  intros δ hδ,
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ,
  rw eventually_at_top,
  refine ⟨egorov.not_convergent_seq_lt_index (half_pos hε) hf hg hsm hs hfg N, λ n hn x hx, _⟩,
  simp only [mem_diff, egorov.Union_not_convergent_seq, not_exists, mem_Union, mem_inter_eq,
    not_and, exists_and_distrib_left] at hx,
  obtain ⟨hxs, hx⟩ := hx,
  specialize hx hxs N,
  rw egorov.mem_not_convergent_seq_iff at hx,
  push_neg at hx,
  rw dist_comm,
  exact lt_of_le_of_lt (hx n hn) hN,
end

end egorov

variables [second_countable_topology β] [measurable_space β] [borel_space β]
  {f : ℕ → α → β} {g : α → β} {s : set α}


/-- **Egorov's theorem**: If `f : ℕ → α → β` is a sequence of measurable functions that converges
to `g : α → β` almost everywhere on a measurable set `s` of finite measure, then for all `ε > 0`,
there exists a subset `t ⊆ s` such that `μ t ≤ ε` and `f` converges to `g` uniformly on `s \ t`.

In other words, a sequence of almost everywhere convergent functions converges uniformly except on
an arbitrarily small set. -/
theorem tendsto_uniformly_on_of_ae_tendsto
  (hf : ∀ n, measurable (f n)) (hg : measurable g) (hsm : measurable_set s) (hs : μ s ≠ ∞)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → tendsto (λ n, f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
  ∃ t ⊆ s, measurable_set t ∧ μ t ≤ ennreal.of_real ε ∧ tendsto_uniformly_on f g at_top (s \ t) :=
⟨egorov.Union_not_convergent_seq hε hf hg hsm hs hfg,
 egorov.Union_not_convergent_seq_subset hε hf hg hsm hs hfg,
 egorov.Union_not_convergent_seq_measurable_set hε hf hg hsm hs hfg,
 egorov.measure_Union_not_convergent_seq hε hf hg hsm hs hfg,
 egorov.tendsto_uniformly_on_diff_Union_not_convergent_seq hε hf hg hsm hs hfg⟩

/-- Egorov's theorem for finite measure spaces. -/
lemma tendsto_uniformly_on_of_ae_tendsto' [is_finite_measure μ]
  (hf : ∀ n, measurable (f n)) (hg : measurable g)
  (hfg : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 (g x))) {ε : ℝ} (hε : 0 < ε) :
  ∃ t, measurable_set t ∧ μ t ≤ ennreal.of_real ε ∧ tendsto_uniformly_on f g at_top tᶜ :=
begin
  obtain ⟨t, _, ht, htendsto⟩ :=
    tendsto_uniformly_on_of_ae_tendsto hf hg measurable_set.univ (measure_ne_top μ univ) _ hε,
  { refine ⟨_, ht, _⟩,
    rwa compl_eq_univ_diff },
  { filter_upwards [hfg] with _ htendsto _ using htendsto, },
end

end

end measure_theory
