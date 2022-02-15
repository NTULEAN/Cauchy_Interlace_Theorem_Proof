/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed.group.basic
import topology.metric_space.hausdorff_distance

/-!
# Properties of pointwise addition of sets in normed groups.

We explore the relationships between pointwise addition of sets in normed groups, and the norm.
Notably, we show that the sum of bounded sets remain bounded.
-/

open metric set
open_locale pointwise topological_space

section semi_normed_group

variables {E : Type*} [semi_normed_group E]

lemma bounded_iff_exists_norm_le {s : set E} :
  bounded s ↔ ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
by simp [subset_def, bounded_iff_subset_ball (0 : E)]

alias bounded_iff_exists_norm_le ↔ metric.bounded.exists_norm_le _

lemma metric.bounded.exists_pos_norm_le {s : set E} (hs : metric.bounded s) :
  ∃ R > 0, ∀ x ∈ s, ∥x∥ ≤ R :=
begin
  obtain ⟨R₀, hR₀⟩ := hs.exists_norm_le,
  refine ⟨max R₀ 1, _, _⟩,
  { exact (by norm_num : (0:ℝ) < 1).trans_le (le_max_right R₀ 1) },
  intros x hx,
  exact (hR₀ x hx).trans (le_max_left _ _),
end

lemma metric.bounded.add
  {s t : set E} (hs : bounded s) (ht : bounded t) :
  bounded (s + t) :=
begin
  obtain ⟨Rs, hRs⟩ : ∃ (R : ℝ), ∀ x ∈ s, ∥x∥ ≤ R := hs.exists_norm_le,
  obtain ⟨Rt, hRt⟩ : ∃ (R : ℝ), ∀ x ∈ t, ∥x∥ ≤ R := ht.exists_norm_le,
  refine (bounded_iff_exists_norm_le).2 ⟨Rs + Rt, _⟩,
  rintros z ⟨x, y, hx, hy, rfl⟩,
  calc ∥x + y∥ ≤ ∥x∥ + ∥y∥ : norm_add_le _ _
  ... ≤ Rs + Rt : add_le_add (hRs x hx) (hRt y hy)
end

@[simp] lemma singleton_add_ball (x y : E) (r : ℝ) :
  {x} + ball y r = ball (x + y) r :=
by simp only [preimage_add_ball, image_add_left, singleton_add, sub_neg_eq_add, add_comm y x]

@[simp] lemma ball_add_singleton (x y : E) (r : ℝ) :
  ball x r + {y} = ball (x + y) r :=
by simp [add_comm _ {y}, add_comm y]

lemma singleton_add_ball_zero (x : E) (r : ℝ) :
  {x} + ball 0 r = ball x r :=
by simp

lemma ball_zero_add_singleton (x : E) (r : ℝ) :
  ball 0 r + {x} = ball x r :=
by simp

@[simp] lemma singleton_add_closed_ball (x y : E) (r : ℝ) :
  {x} + closed_ball y r = closed_ball (x + y) r :=
by simp only [add_comm y x, preimage_add_closed_ball, image_add_left, singleton_add, sub_neg_eq_add]

@[simp] lemma closed_ball_add_singleton (x y : E) (r : ℝ) :
  closed_ball x r + {y} = closed_ball (x + y) r :=
by simp [add_comm _ {y}, add_comm y]

lemma singleton_add_closed_ball_zero (x : E) (r : ℝ) :
  {x} + closed_ball 0 r = closed_ball x r :=
by simp

lemma closed_ball_zero_add_singleton (x : E) (r : ℝ) :
  closed_ball 0 r + {x} = closed_ball x r :=
by simp

lemma is_compact.cthickening_eq_add_closed_ball
  {s : set E} (hs : is_compact s) {r : ℝ} (hr : 0 ≤ r) :
  cthickening r s = s + closed_ball 0 r :=
begin
  rw hs.cthickening_eq_bUnion_closed_ball hr,
  ext x,
  simp only [mem_add, dist_eq_norm, exists_prop, mem_Union, mem_closed_ball,
    exists_and_distrib_left, mem_closed_ball_zero_iff, ← eq_sub_iff_add_eq', exists_eq_right],
end

end semi_normed_group
