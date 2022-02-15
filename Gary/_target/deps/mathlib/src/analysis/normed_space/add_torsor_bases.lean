/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed_space.banach
import analysis.normed_space.finite_dimension
import analysis.convex.combination
import linear_algebra.affine_space.basis
import linear_algebra.affine_space.finite_dimensional

/-!
# Bases in normed affine spaces.

This file contains results about bases in normed affine spaces.

## Main definitions:

 * `continuous_barycentric_coord`
 * `is_open_map_barycentric_coord`
 * `interior_convex_hull_aff_basis`
 * `exists_subset_affine_independent_span_eq_top_of_open`
 * `interior_convex_hull_nonempty_iff_aff_span_eq_top`
-/

section barycentric

variables {ι 𝕜 E P : Type*} [nondiscrete_normed_field 𝕜] [complete_space 𝕜]
variables [normed_group E] [normed_space 𝕜 E] [finite_dimensional 𝕜 E]
variables [metric_space P] [normed_add_torsor E P]
variables (b : affine_basis ι 𝕜 P)

@[continuity]
lemma continuous_barycentric_coord (i : ι) : continuous (b.coord i) :=
(b.coord i).continuous_of_finite_dimensional

local attribute [instance] finite_dimensional.complete

lemma is_open_map_barycentric_coord [nontrivial ι] (i : ι) :
  is_open_map (b.coord i) :=
(b.coord i).is_open_map (continuous_barycentric_coord b i) (b.surjective_coord i)

end barycentric

open set

/-- Given a finite-dimensional normed real vector space, the interior of the convex hull of an
affine basis is the set of points whose barycentric coordinates are strictly positive with respect
to this basis.

TODO Restate this result for affine spaces (instead of vector spaces) once the definition of
convexity is generalised to this setting. -/
lemma interior_convex_hull_aff_basis {ι E : Type*} [fintype ι] [normed_group E] [normed_space ℝ E]
  (b : affine_basis ι ℝ E) :
  interior (convex_hull ℝ (range b.points)) = { x | ∀ i, 0 < b.coord i x } :=
begin
  cases subsingleton_or_nontrivial ι with h h,
  { -- The zero-dimensional case.
    haveI := h,
    suffices : range (b.points) = univ, { simp [this], },
    refine affine_subspace.eq_univ_of_subsingleton_span_eq_top _ b.tot,
    rw ← image_univ,
    exact subsingleton.image subsingleton_of_subsingleton b.points, },
  { -- The positive-dimensional case.
    haveI : finite_dimensional ℝ E,
    { classical,
      obtain ⟨i⟩ := (infer_instance : nonempty ι),
      exact finite_dimensional.of_fintype_basis (b.basis_of i), },
    have : convex_hull ℝ (range b.points) = ⋂ i, (b.coord i)⁻¹' Ici 0,
    { rw convex_hull_affine_basis_eq_nonneg_barycentric b, ext, simp, },
    ext,
    simp only [this, interior_Inter_of_fintype, ← is_open_map.preimage_interior_eq_interior_preimage
      (is_open_map_barycentric_coord b _) (continuous_barycentric_coord b _),
      interior_Ici, mem_Inter, mem_set_of_eq, mem_Ioi, mem_preimage], },
end

variables {V P : Type*} [normed_group V] [normed_space ℝ V] [metric_space P] [normed_add_torsor V P]
include V

open affine_map

/-- Given a set `s` of affine-independent points belonging to an open set `u`, we may extend `s` to
an affine basis, all of whose elements belong to `u`. -/
lemma exists_subset_affine_independent_span_eq_top_of_open {s u : set P} (hu : is_open u)
  (hsu : s ⊆ u) (hne : s.nonempty) (h : affine_independent ℝ (coe : s → P)) :
  ∃ t : set P, s ⊆ t ∧ t ⊆ u ∧ affine_independent ℝ (coe : t → P) ∧ affine_span ℝ t = ⊤ :=
begin
  obtain ⟨q, hq⟩ := hne,
  obtain ⟨ε, hε, hεu⟩ := metric.is_open_iff.mp hu q (hsu hq),
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := exists_subset_affine_independent_affine_span_eq_top h,
  let f : P → P := λ y, line_map q y (ε / 2 / (dist y q)),
  have hf : ∀ y, f y ∈ u,
  { intros y,
    apply hεu,
    simp only [metric.mem_ball, f, line_map_apply, dist_vadd_left, norm_smul, real.norm_eq_abs,
      dist_eq_norm_vsub V y q],
    cases eq_or_ne (∥y -ᵥ q∥) 0 with hyq hyq, { rwa [hyq, mul_zero], },
    rw [← norm_pos_iff, norm_norm] at hyq,
    calc abs (ε / 2 / ∥y -ᵥ q∥) * ∥y -ᵥ q∥
          = ε / 2 / ∥y -ᵥ q∥ * ∥y -ᵥ q∥ : by rw [abs_div, abs_of_pos (half_pos hε), abs_of_pos hyq]
      ... = ε / 2 : div_mul_cancel _ (ne_of_gt hyq)
      ... < ε : half_lt_self hε, },
  have hεyq : ∀ (y ∉ s), ε / 2 / dist y q ≠ 0,
  { simp only [ne.def, div_eq_zero_iff, or_false, dist_eq_zero, bit0_eq_zero, one_ne_zero,
      not_or_distrib, ne_of_gt hε, true_and, not_false_iff],
    exact λ y h1 h2, h1 (h2.symm ▸ hq) },
  classical,
  let w : t → ℝˣ := λ p, if hp : (p : P) ∈ s then 1 else units.mk0 _ (hεyq ↑p hp),
  refine ⟨set.range (λ (p : t), line_map q p (w p : ℝ)), _, _, _, _⟩,
  { intros p hp, use ⟨p, ht₁ hp⟩, simp [w, hp], },
  { intros y hy,
    simp only [set.mem_range, set_coe.exists, subtype.coe_mk] at hy,
    obtain ⟨p, hp, hyq⟩ := hy,
    by_cases hps : p ∈ s;
    simp only [w, hps, line_map_apply_one, units.coe_mk0, dif_neg, dif_pos, not_false_iff,
      units.coe_one, subtype.coe_mk] at hyq;
    rw ← hyq;
    [exact hsu hps, exact hf p], },
  { exact (ht₂.units_line_map ⟨q, ht₁ hq⟩ w).range, },
  { rw [affine_span_eq_affine_span_line_map_units (ht₁ hq) w, ht₃], },
end

lemma interior_convex_hull_nonempty_iff_aff_span_eq_top [finite_dimensional ℝ V] {s : set V} :
  (interior (convex_hull ℝ s)).nonempty ↔ affine_span ℝ s = ⊤ :=
begin
  split,
  { rintros ⟨x, hx⟩,
    obtain ⟨u, hu₁, hu₂, hu₃⟩ := mem_interior.mp hx,
    let t : set V := {x},
    obtain ⟨b, hb₁, hb₂, hb₃, hb₄⟩ := exists_subset_affine_independent_span_eq_top_of_open hu₂
      (singleton_subset_iff.mpr hu₃) (singleton_nonempty x)
      (affine_independent_of_subsingleton ℝ (coe : t → V)),
    rw [eq_top_iff, ← hb₄, ← affine_span_convex_hull s],
    mono,
    exact hb₂.trans hu₁, },
  { intros h,
    obtain ⟨t, hts, h_tot, h_ind⟩ := exists_affine_independent ℝ V s,
    suffices : (interior (convex_hull ℝ (range (coe : t → V)))).nonempty,
    { rw [subtype.range_coe_subtype, set_of_mem_eq] at this,
      apply nonempty.mono _ this,
      mono* },
    haveI : fintype t := fintype_of_fin_dim_affine_independent ℝ h_ind,
    use finset.centroid ℝ (finset.univ : finset t) (coe : t → V),
    rw [h, ← @set_of_mem_eq V t, ← subtype.range_coe_subtype] at h_tot,
    let b : affine_basis t ℝ V := ⟨coe, h_ind, h_tot⟩,
    rw interior_convex_hull_aff_basis b,
    have htne : (finset.univ : finset t).nonempty,
    { simpa [finset.univ_nonempty_iff] using
        affine_subspace.nonempty_of_affine_span_eq_top ℝ V V h_tot, },
    simp [finset.centroid_def, b.coord_apply_combination_of_mem (finset.mem_univ _)
      (finset.sum_centroid_weights_eq_one_of_nonempty ℝ (finset.univ : finset t) htne),
      finset.centroid_weights_apply, nat.cast_pos, inv_pos, finset.card_pos.mpr htne], },
end
