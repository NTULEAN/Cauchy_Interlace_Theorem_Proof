/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import analysis.normed_space.continuous_affine_map
import analysis.calculus.times_cont_diff

/-!
# Smooth affine maps

This file contains results about smoothness of affine maps.

## Main definitions:

 * `continuous_affine_map.times_cont_diff`: a continuous affine map is smooth

-/

namespace continuous_affine_map

variables {𝕜 V W : Type*} [nondiscrete_normed_field 𝕜]
variables [normed_group V] [normed_space 𝕜 V]
variables [normed_group W] [normed_space 𝕜 W]

/-- A continuous affine map between normed vector spaces is smooth. -/
lemma times_cont_diff {n : with_top ℕ} (f : V →A[𝕜] W) :
  times_cont_diff 𝕜 n f :=
begin
  rw f.decomp,
  apply f.cont_linear.times_cont_diff.add,
  simp only,
  exact times_cont_diff_const,
end

end continuous_affine_map
