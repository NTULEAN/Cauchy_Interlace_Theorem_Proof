/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
import analysis.convex.cone
import analysis.normed_space.is_R_or_C
import analysis.normed_space.extend

/-!
# Hahn-Banach theorem

In this file we prove a version of Hahn-Banach theorem for continuous linear
functions on normed spaces over `ℝ` and `ℂ`.

In order to state and prove its corollaries uniformly, we prove the statements for a field `𝕜`
satisfying `is_R_or_C 𝕜`.

In this setting, `exists_dual_vector` states that, for any nonzero `x`, there exists a continuous
linear form `g` of norm `1` with `g x = ∥x∥` (where the norm has to be interpreted as an element
of `𝕜`).

-/

universes u v

namespace real
variables {E : Type*} [semi_normed_group E] [normed_space ℝ E]

/-- Hahn-Banach theorem for continuous linear functions over `ℝ`. -/
theorem exists_extension_norm_eq (p : subspace ℝ E) (f : p →L[ℝ] ℝ) :
  ∃ g : E →L[ℝ] ℝ, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  rcases exists_extension_of_le_sublinear ⟨p, f⟩ (λ x, ∥f∥ * ∥x∥)
    (λ c hc x, by simp only [norm_smul c x, real.norm_eq_abs, abs_of_pos hc, mul_left_comm])
    (λ x y, _) (λ x, le_trans (le_abs_self _) (f.le_op_norm _))
    with ⟨g, g_eq, g_le⟩,
  set g' := g.mk_continuous (∥f∥)
    (λ x, abs_le.2 ⟨neg_le.1 $ g.map_neg x ▸ norm_neg x ▸ g_le (-x), g_le x⟩),
  { refine ⟨g', g_eq, _⟩,
    { apply le_antisymm (g.mk_continuous_norm_le (norm_nonneg f) _),
      refine f.op_norm_le_bound (norm_nonneg _) (λ x, _),
      dsimp at g_eq,
      rw ← g_eq,
      apply g'.le_op_norm } },
  { simp only [← mul_add],
    exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg f) }
end

end real

section is_R_or_C
open is_R_or_C

variables {𝕜 : Type*} [is_R_or_C 𝕜] {F : Type*} [semi_normed_group F] [normed_space 𝕜 F]

/-- Hahn-Banach theorem for continuous linear functions over `𝕜` satisyfing `is_R_or_C 𝕜`. -/
theorem exists_extension_norm_eq (p : subspace 𝕜 F) (f : p →L[𝕜] 𝕜) :
  ∃ g : F →L[𝕜] 𝕜, (∀ x : p, g x = f x) ∧ ∥g∥ = ∥f∥ :=
begin
  letI : module ℝ F := restrict_scalars.module ℝ 𝕜 F,
  letI : is_scalar_tower ℝ 𝕜 F := restrict_scalars.is_scalar_tower _ _ _,
  letI : normed_space ℝ F := normed_space.restrict_scalars _ 𝕜 _,
  -- Let `fr: p →L[ℝ] ℝ` be the real part of `f`.
  let fr := re_clm.comp (f.restrict_scalars ℝ),
  have fr_apply : ∀ x, fr x = re (f x), by { assume x, refl },
  -- Use the real version to get a norm-preserving extension of `fr`, which
  -- we'll call `g : F →L[ℝ] ℝ`.
  rcases real.exists_extension_norm_eq (p.restrict_scalars ℝ) fr with ⟨g, ⟨hextends, hnormeq⟩⟩,
  -- Now `g` can be extended to the `F →L[𝕜] 𝕜` we need.
  refine ⟨g.extend_to_𝕜, _⟩,
  -- It is an extension of `f`.
  have h : ∀ x : p, g.extend_to_𝕜 x = f x,
  { assume x,
    rw [continuous_linear_map.extend_to_𝕜_apply, ←submodule.coe_smul, hextends, hextends],
    have : (fr x : 𝕜) - I * ↑(fr (I • x)) = (re (f x) : 𝕜) - (I : 𝕜) * (re (f ((I : 𝕜) • x))),
      by refl,
    rw this,
    apply ext,
    { simp only [add_zero, algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add,
        zero_sub, I_im', zero_mul, of_real_re, eq_self_iff_true, sub_zero, mul_neg,
        of_real_neg, mul_re, mul_zero, sub_neg_eq_add, continuous_linear_map.map_smul] },
    { simp only [algebra.id.smul_eq_mul, I_re, of_real_im, add_monoid_hom.map_add, zero_sub, I_im',
        zero_mul, of_real_re, mul_neg, mul_im, zero_add, of_real_neg, mul_re,
        sub_neg_eq_add, continuous_linear_map.map_smul] } },
  -- And we derive the equality of the norms by bounding on both sides.
  refine ⟨h, le_antisymm _ _⟩,
  { calc ∥g.extend_to_𝕜∥
        ≤ ∥g∥ : g.extend_to_𝕜.op_norm_le_bound g.op_norm_nonneg (norm_bound _)
    ... = ∥fr∥ : hnormeq
    ... ≤ ∥re_clm∥ * ∥f∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = ∥f∥ : by rw [re_clm_norm, one_mul] },
  { exact f.op_norm_le_bound g.extend_to_𝕜.op_norm_nonneg (λ x, h x ▸ g.extend_to_𝕜.le_op_norm x) }
end

end is_R_or_C

section dual_vector
variables (𝕜 : Type v) [is_R_or_C 𝕜]
variables {E : Type u} [normed_group E] [normed_space 𝕜 E]

open continuous_linear_equiv submodule
open_locale classical

lemma coord_norm' {x : E} (h : x ≠ 0) : ∥(∥x∥ : 𝕜) • coord 𝕜 x h∥ = 1 :=
by rw [norm_smul, is_R_or_C.norm_coe_norm, coord_norm, mul_inv_cancel (mt norm_eq_zero.mp h)]

/-- Corollary of Hahn-Banach.  Given a nonzero element `x` of a normed space, there exists an
    element of the dual space, of norm `1`, whose value on `x` is `∥x∥`. -/
theorem exists_dual_vector (x : E) (h : x ≠ 0) : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  let p : submodule 𝕜 E := 𝕜 ∙ x,
  let f := (∥x∥ : 𝕜) • coord 𝕜 x h,
  obtain ⟨g, hg⟩ := exists_extension_norm_eq p f,
  refine ⟨g, _, _⟩,
  { rw [hg.2, coord_norm'] },
  { calc g x = g (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw coe_mk
    ... = ((∥x∥ : 𝕜) • coord 𝕜 x h) (⟨x, mem_span_singleton_self x⟩ : 𝕜 ∙ x) : by rw ← hg.1
    ... = ∥x∥ : by simp }
end

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, and choosing
    the dual element arbitrarily when `x = 0`. -/
theorem exists_dual_vector' [nontrivial E] (x : E) :
  ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g x = ∥x∥ :=
begin
  by_cases hx : x = 0,
  { obtain ⟨y, hy⟩ := exists_ne (0 : E),
    obtain ⟨g, hg⟩ : ∃ g : E →L[𝕜] 𝕜, ∥g∥ = 1 ∧ g y = ∥y∥ := exists_dual_vector 𝕜 y hy,
    refine ⟨g, hg.left, _⟩,
    simp [hx] },
  { exact exists_dual_vector 𝕜 x hx }
end

/-- Variant of Hahn-Banach, eliminating the hypothesis that `x` be nonzero, but only ensuring that
    the dual element has norm at most `1` (this can not be improved for the trivial
    vector space). -/
theorem exists_dual_vector'' (x : E) :
  ∃ g : E →L[𝕜] 𝕜, ∥g∥ ≤ 1 ∧ g x = ∥x∥ :=
begin
  by_cases hx : x = 0,
  { refine ⟨0, by simp, _⟩,
    symmetry,
    simp [hx], },
  { rcases exists_dual_vector 𝕜 x hx with ⟨g, g_norm, g_eq⟩,
    exact ⟨g, g_norm.le, g_eq⟩ }
end

end dual_vector
