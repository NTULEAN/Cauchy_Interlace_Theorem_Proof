/-
Copyright (c) 2020 Heather Macbeth, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Patrick Massot
-/
import algebra.order.archimedean
import group_theory.subgroup.basic

/-!
# Archimedean groups

This file proves a few facts about ordered groups which satisfy the `archimedean` property, that is:
`class archimedean (α) [ordered_add_comm_monoid α] : Prop :=`
`(arch : ∀ (x : α) {y}, 0 < y → ∃ n : ℕ, x ≤ n • y)`

They are placed here in a separate file (rather than incorporated as a continuation of
`algebra.order.archimedean`) because they rely on some imports from `group_theory` -- bundled
subgroups in particular.

The main result is `add_subgroup.cyclic_of_min`:  a subgroup of a decidable archimedean abelian
group is cyclic, if its set of positive elements has a minimal element.

This result is used in this file to deduce `int.subgroup_cyclic`, proving that every subgroup of `ℤ`
is cyclic.  (There are several other methods one could use to prove this fact, including more purely
algebraic methods, but none seem to exist in mathlib as of writing.  The closest is
`subgroup.is_cyclic`, but that has not been transferred to `add_subgroup`.)

The result is also used in `topology.instances.real` as an ingredient in the classification of
subgroups of `ℝ`.
-/

variables {G : Type*} [linear_ordered_add_comm_group G] [archimedean G]
open linear_ordered_add_comm_group

/-- Given a subgroup `H` of a decidable linearly ordered archimedean abelian group `G`, if there
exists a minimal element `a` of `H ∩ G_{>0}` then `H` is generated by `a`. -/
lemma add_subgroup.cyclic_of_min {H : add_subgroup G} {a : G}
  (ha : is_least {g : G | g ∈ H ∧ 0 < g} a) : H = add_subgroup.closure {a} :=
begin
  obtain ⟨⟨a_in, a_pos⟩, a_min⟩ := ha,
  refine le_antisymm _ (H.closure_le.mpr $ by simp [a_in]),
  intros g g_in,
  obtain ⟨k, ⟨nonneg, lt⟩, _⟩ : ∃! k, 0 ≤ g - k • a ∧ g - k • a < a :=
    exists_unique_zsmul_near_of_pos' a_pos g,
  have h_zero : g - k • a = 0,
  { by_contra h,
    have h : a ≤ g - k • a,
    { refine a_min ⟨_, _⟩,
      { exact add_subgroup.sub_mem H g_in (add_subgroup.zsmul_mem H a_in k) },
      { exact lt_of_le_of_ne nonneg (ne.symm h) } },
    have h' : ¬ (a ≤ g - k • a) := not_le.mpr lt,
    contradiction },
  simp [sub_eq_zero.mp h_zero, add_subgroup.mem_closure_singleton],
end

/-- Every subgroup of `ℤ` is cyclic. -/
lemma int.subgroup_cyclic (H : add_subgroup ℤ) : ∃ a, H = add_subgroup.closure {a} :=
begin
  cases add_subgroup.bot_or_exists_ne_zero H with h h,
  { use 0,
    rw h,
    exact add_subgroup.closure_singleton_zero.symm },
  let s := {g : ℤ | g ∈ H ∧ 0 < g},
  have h_bdd : ∀ g ∈ s, (0 : ℤ) ≤ g := λ _ h, le_of_lt h.2,
  obtain ⟨g₀, g₀_in, g₀_ne⟩ := h,
  obtain ⟨g₁, g₁_in, g₁_pos⟩ : ∃ g₁ : ℤ, g₁ ∈ H ∧ 0 < g₁,
  { cases lt_or_gt_of_ne g₀_ne with Hg₀ Hg₀,
    { exact ⟨-g₀, H.neg_mem g₀_in, neg_pos.mpr Hg₀⟩ },
    { exact ⟨g₀, g₀_in, Hg₀⟩ } },
  obtain ⟨a, ha, ha'⟩ := int.exists_least_of_bdd ⟨(0 : ℤ), h_bdd⟩ ⟨g₁, g₁_in, g₁_pos⟩,
  exact ⟨a, add_subgroup.cyclic_of_min ⟨ha, ha'⟩⟩,
end
