/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import analysis.convex.jensen
import analysis.normed_space.finite_dimension
import topology.path_connected
import topology.algebra.affine

/-!
# Topological and metric properties of convex sets

We prove the following facts:

* `convex.interior` : interior of a convex set is convex;
* `convex.closure` : closure of a convex set is convex;
* `set.finite.compact_convex_hull` : convex hull of a finite set is compact;
* `set.finite.is_closed_convex_hull` : convex hull of a finite set is closed;
* `convex_on_dist` : distance to a fixed point is convex on any convex set;
* `convex_hull_ediam`, `convex_hull_diam` : convex hull of a set has the same (e)metric diameter
  as the original set;
* `bounded_convex_hull` : convex hull of a set is bounded if and only if the original set
  is bounded.
* `bounded_std_simplex`, `is_closed_std_simplex`, `compact_std_simplex`: topological properties
  of the standard simplex;
-/

variables {ι : Type*} {E : Type*}

open set
open_locale pointwise

lemma real.convex_iff_is_preconnected {s : set ℝ} : convex ℝ s ↔ is_preconnected s :=
convex_iff_ord_connected.trans is_preconnected_iff_ord_connected.symm

alias real.convex_iff_is_preconnected ↔ convex.is_preconnected is_preconnected.convex

/-! ### Standard simplex -/

section std_simplex

variables [fintype ι]

/-- Every vector in `std_simplex 𝕜 ι` has `max`-norm at most `1`. -/
lemma std_simplex_subset_closed_ball :
  std_simplex ℝ ι ⊆ metric.closed_ball 0 1 :=
begin
  assume f hf,
  rw [metric.mem_closed_ball, dist_zero_right],
  refine (nnreal.coe_one ▸ nnreal.coe_le_coe.2 $ finset.sup_le $ λ x hx, _),
  change |f x| ≤ 1,
  rw [abs_of_nonneg $ hf.1 x],
  exact (mem_Icc_of_mem_std_simplex hf x).2
end

variable (ι)

/-- `std_simplex ℝ ι` is bounded. -/
lemma bounded_std_simplex : metric.bounded (std_simplex ℝ ι) :=
(metric.bounded_iff_subset_ball 0).2 ⟨1, std_simplex_subset_closed_ball⟩

/-- `std_simplex ℝ ι` is closed. -/
lemma is_closed_std_simplex : is_closed (std_simplex ℝ ι) :=
(std_simplex_eq_inter ℝ ι).symm ▸ is_closed.inter
  (is_closed_Inter $ λ i, is_closed_le continuous_const (continuous_apply i))
  (is_closed_eq (continuous_finset_sum _ $ λ x _, continuous_apply x) continuous_const)

/-- `std_simplex ℝ ι` is compact. -/
lemma compact_std_simplex : is_compact (std_simplex ℝ ι) :=
metric.compact_iff_closed_bounded.2 ⟨is_closed_std_simplex ι, bounded_std_simplex ι⟩

end std_simplex

/-! ### Topological vector space -/

section has_continuous_smul

variables [add_comm_group E] [module ℝ E] [topological_space E]
  [topological_add_group E] [has_continuous_smul ℝ E]

lemma convex.combo_interior_self_subset_interior {s : set E} (hs : convex ℝ s) {a b : ℝ}
  (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • interior s + b • s ⊆ interior s :=
interior_smul₀ ha.ne' s ▸
  calc interior (a • s) + b • s ⊆ interior (a • s + b • s) : subset_interior_add_left
  ... ⊆ interior s : interior_mono $ hs.set_combo_subset ha.le hb hab

lemma convex.combo_self_interior_subset_interior {s : set E} (hs : convex ℝ s) {a b : ℝ}
  (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
  a • s + b • interior s ⊆ interior s :=
by { rw add_comm, exact hs.combo_interior_self_subset_interior hb ha (add_comm a b ▸ hab) }

lemma convex.combo_mem_interior_left {s : set E} (hs : convex ℝ s) {x y : E} (hx : x ∈ interior s)
  (hy : y ∈ s) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
  a • x + b • y ∈ interior s :=
hs.combo_interior_self_subset_interior ha hb hab $
  add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

lemma convex.combo_mem_interior_right {s : set E} (hs : convex ℝ s) {x y : E} (hx : x ∈ s)
  (hy : y ∈ interior s) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1) :
  a • x + b • y ∈ interior s :=
hs.combo_self_interior_subset_interior ha hb hab $
  add_mem_add (smul_mem_smul_set hx) (smul_mem_smul_set hy)

lemma convex.open_segment_subset_interior_left {s : set E} (hs : convex ℝ s) {x y : E}
  (hx : x ∈ interior s) (hy : y ∈ s) : open_segment ℝ x y ⊆ interior s :=
by { rintro _ ⟨a, b, ha, hb, hab, rfl⟩, exact hs.combo_mem_interior_left hx hy ha hb.le hab }

lemma convex.open_segment_subset_interior_right {s : set E} (hs : convex ℝ s) {x y : E}
  (hx : x ∈ s) (hy : y ∈ interior s) : open_segment ℝ x y ⊆ interior s :=
by { rintro _ ⟨a, b, ha, hb, hab, rfl⟩, exact hs.combo_mem_interior_right hx hy ha.le hb hab }

/-- If `x ∈ s` and `y ∈ interior s`, then the segment `(x, y]` is included in `interior s`. -/
lemma convex.add_smul_sub_mem_interior {s : set E} (hs : convex ℝ s)
  {x y : E} (hx : x ∈ s) (hy : y ∈ interior s) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
  x + t • (y - x) ∈ interior s :=
by simpa only [sub_smul, smul_sub, one_smul, add_sub, add_comm]
  using hs.combo_mem_interior_left hy hx ht.1 (sub_nonneg.mpr ht.2) (add_sub_cancel'_right _ _)

/-- If `x ∈ s` and `x + y ∈ interior s`, then `x + t y ∈ interior s` for `t ∈ (0, 1]`. -/
lemma convex.add_smul_mem_interior {s : set E} (hs : convex ℝ s)
  {x y : E} (hx : x ∈ s) (hy : x + y ∈ interior s) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
  x + t • y ∈ interior s :=
by { convert hs.add_smul_sub_mem_interior hx hy ht, abel }

/-- In a topological vector space, the interior of a convex set is convex. -/
lemma convex.interior {s : set E} (hs : convex ℝ s) : convex ℝ (interior s) :=
convex_iff_open_segment_subset.mpr $ λ x y hx hy,
  hs.open_segment_subset_interior_left hx (interior_subset hy)

/-- In a topological vector space, the closure of a convex set is convex. -/
lemma convex.closure {s : set E} (hs : convex ℝ s) : convex ℝ (closure s) :=
λ x y hx hy a b ha hb hab,
let f : E → E → E := λ x' y', a • x' + b • y' in
have hf : continuous (λ p : E × E, f p.1 p.2), from
  (continuous_const.smul continuous_fst).add (continuous_const.smul continuous_snd),
show f x y ∈ closure s, from
  mem_closure_of_continuous2 hf hx hy (λ x' hx' y' hy', subset_closure
  (hs hx' hy' ha hb hab))

/-- Convex hull of a finite set is compact. -/
lemma set.finite.compact_convex_hull {s : set E} (hs : finite s) :
  is_compact (convex_hull ℝ s) :=
begin
  rw [hs.convex_hull_eq_image],
  apply (compact_std_simplex _).image,
  haveI := hs.fintype,
  apply linear_map.continuous_on_pi
end

/-- Convex hull of a finite set is closed. -/
lemma set.finite.is_closed_convex_hull [t2_space E] {s : set E} (hs : finite s) :
  is_closed (convex_hull ℝ s) :=
hs.compact_convex_hull.is_closed

open affine_map

/-- If we dilate a convex set about a point in its interior by a scale `t > 1`, the interior of
the result contains the original set.

TODO Generalise this from convex sets to sets that are balanced / star-shaped about `x`. -/
lemma convex.subset_interior_image_homothety_of_one_lt
  {s : set E} (hs : convex ℝ s) {x : E} (hx : x ∈ interior s) (t : ℝ) (ht : 1 < t) :
  s ⊆ interior (image (homothety x t) s) :=
begin
  intros y hy,
  let I := { z | ∃ (u : ℝ), u ∈ Ioc (0 : ℝ) 1 ∧ z = y + u • (x - y) },
  have hI : I ⊆ interior s,
  { rintros z ⟨u, hu, rfl⟩, exact hs.add_smul_sub_mem_interior hy hx hu, },
  let z := homothety x t⁻¹ y,
  have hz₁ : z ∈ interior s,
  { suffices : z ∈ I, { exact hI this, },
    use 1 - t⁻¹,
    split,
    { simp only [mem_Ioc, sub_le_self_iff, inv_nonneg, sub_pos, inv_lt_one ht, true_and],
      linarith, },
    { simp only [z, homothety_apply, sub_smul, smul_sub, vsub_eq_sub, vadd_eq_add, one_smul],
      abel, }, },
  have ht' : t ≠ 0, { linarith, },
  have hz₂ : y = homothety x t z, { simp [z, ht', homothety_apply, smul_smul], },
  rw hz₂,
  rw mem_interior at hz₁ ⊢,
  obtain ⟨U, hU₁, hU₂, hU₃⟩ := hz₁,
  exact ⟨image (homothety x t) U,
         image_subset ⇑(homothety x t) hU₁,
         homothety_is_open_map x t ht' U hU₂,
         mem_image_of_mem ⇑(homothety x t) hU₃⟩,
end

lemma convex.is_path_connected {s : set E} (hconv : convex ℝ s) (hne : s.nonempty) :
  is_path_connected s :=
begin
  refine is_path_connected_iff.mpr ⟨hne, _⟩,
  intros x x_in y y_in,
  have H := hconv.segment_subset x_in y_in,
  rw segment_eq_image_line_map at H,
  exact joined_in.of_line affine_map.line_map_continuous.continuous_on (line_map_apply_zero _ _)
    (line_map_apply_one _ _) H
end

@[priority 100]
instance topological_add_group.path_connected : path_connected_space E :=
path_connected_space_iff_univ.mpr $ convex_univ.is_path_connected ⟨(0 : E), trivial⟩

end has_continuous_smul

/-! ### Normed vector space -/

section normed_space
variables [normed_group E] [normed_space ℝ E]

lemma convex_on_dist (z : E) (s : set E) (hs : convex ℝ s) :
  convex_on ℝ s (λz', dist z' z) :=
and.intro hs $
assume x y hx hy a b ha hb hab,
calc
  dist (a • x + b • y) z = ∥ (a • x + b • y) - (a + b) • z ∥ :
    by rw [hab, one_smul, normed_group.dist_eq]
  ... = ∥a • (x - z) + b • (y - z)∥ :
    by rw [add_smul, smul_sub, smul_sub, sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, neg_add,
           ←add_assoc, add_assoc (a • x), add_comm (b • y)]; simp only [add_assoc]
  ... ≤ ∥a • (x - z)∥ + ∥b • (y - z)∥ :
    norm_add_le (a • (x - z)) (b • (y - z))
  ... = a * dist x z + b * dist y z :
    by simp [norm_smul, normed_group.dist_eq, real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]

lemma convex_ball (a : E) (r : ℝ) : convex ℝ (metric.ball a r) :=
by simpa only [metric.ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_lt r

lemma convex_closed_ball (a : E) (r : ℝ) : convex ℝ (metric.closed_ball a r) :=
by simpa only [metric.closed_ball, sep_univ] using (convex_on_dist a _ convex_univ).convex_le r

/-- Given a point `x` in the convex hull of `s` and a point `y`, there exists a point
of `s` at distance at least `dist x y` from `y`. -/
lemma convex_hull_exists_dist_ge {s : set E} {x : E} (hx : x ∈ convex_hull ℝ s) (y : E) :
  ∃ x' ∈ s, dist x y ≤ dist x' y :=
(convex_on_dist y _ (convex_convex_hull ℝ _)).exists_ge_of_mem_convex_hull hx

/-- Given a point `x` in the convex hull of `s` and a point `y` in the convex hull of `t`,
there exist points `x' ∈ s` and `y' ∈ t` at distance at least `dist x y`. -/
lemma convex_hull_exists_dist_ge2 {s t : set E} {x y : E}
  (hx : x ∈ convex_hull ℝ s) (hy : y ∈ convex_hull ℝ t) :
  ∃ (x' ∈ s) (y' ∈ t), dist x y ≤ dist x' y' :=
begin
  rcases convex_hull_exists_dist_ge hx y with ⟨x', hx', Hx'⟩,
  rcases convex_hull_exists_dist_ge hy x' with ⟨y', hy', Hy'⟩,
  use [x', hx', y', hy'],
  exact le_trans Hx' (dist_comm y x' ▸ dist_comm y' x' ▸ Hy')
end

/-- Emetric diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] lemma convex_hull_ediam (s : set E) :
  emetric.diam (convex_hull ℝ s) = emetric.diam s :=
begin
  refine (emetric.diam_le $ λ x hx y hy, _).antisymm (emetric.diam_mono $ subset_convex_hull ℝ s),
  rcases convex_hull_exists_dist_ge2 hx hy with ⟨x', hx', y', hy', H⟩,
  rw edist_dist,
  apply le_trans (ennreal.of_real_le_of_real H),
  rw ← edist_dist,
  exact emetric.edist_le_diam_of_mem hx' hy'
end

/-- Diameter of the convex hull of a set `s` equals the emetric diameter of `s. -/
@[simp] lemma convex_hull_diam (s : set E) :
  metric.diam (convex_hull ℝ s) = metric.diam s :=
by simp only [metric.diam, convex_hull_ediam]

/-- Convex hull of `s` is bounded if and only if `s` is bounded. -/
@[simp] lemma bounded_convex_hull {s : set E} :
  metric.bounded (convex_hull ℝ s) ↔ metric.bounded s :=
by simp only [metric.bounded_iff_ediam_ne_top, convex_hull_ediam]

@[priority 100]
instance normed_space.loc_path_connected : loc_path_connected_space E :=
loc_path_connected_of_bases (λ x, metric.nhds_basis_ball)
  (λ x r r_pos, (convex_ball x r).is_path_connected $ by simp [r_pos])

end normed_space
