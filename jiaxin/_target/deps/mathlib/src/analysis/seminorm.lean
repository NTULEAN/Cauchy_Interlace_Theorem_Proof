/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
import analysis.convex.function
import analysis.convex.star
import analysis.normed_space.ordered
import analysis.normed_space.pointwise
import data.real.pointwise
import topology.algebra.filter_basis
import topology.algebra.uniform_filter_basis
import data.real.sqrt

/-!
# Seminorms and Local Convexity

This file defines absorbent sets, balanced sets, seminorms and the Minkowski functional.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

A seminorm is a function to the reals which is positive-semidefinite, absolutely homogeneous, and
subadditive. They are closely related to convex sets and a topological vector space is locally
convex if and only if its topology is induced by a family of seminorms.

The Minkowski functional of a set `s` is the function which associates each point to how much you
need to scale `s` for `x` to be inside it. When `s` is symmetric, convex and absorbent, its gauge is
a seminorm. Reciprocally, any seminorm arises as the gauge of some set, namely its unit ball. This
induces the equivalence of seminorms and locally convex topological vector spaces.

## Main declarations

For a vector space over a normed field:
* `absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.
* `seminorm`: A function to the reals that is positive-semidefinite, absolutely homogeneous, and
  subadditive.
* `norm_seminorm 𝕜 E`: The norm on `E` as a seminorm.
* `gauge`: Aka Minkowksi functional. `gauge s x` is the least (actually, an infimum) `r` such
  that `x ∈ r • s`.
* `gauge_seminorm`: The Minkowski functional as a seminorm, when `s` is symmetric, convex and
  absorbent.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

Prove the properties of balanced and absorbent sets of a real vector space.

## Tags

absorbent, balanced, seminorm, Minkowski functional, gauge, locally convex, LCTVS
-/

/-!
### Set Properties

Absorbent and balanced sets in a vector space over a normed field.
-/

open normed_field set
open_locale pointwise topological_space nnreal big_operators

variables {R 𝕜 𝕝 E F G ι ι' : Type*}

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section has_scalar
variables (𝕜) [has_scalar 𝕜 E]

/-- A set `A` absorbs another set `B` if `B` is contained in all scalings of
`A` by elements of sufficiently large norms. -/
def absorbs (A B : set E) := ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := ∀ x, ∃ r, 0 < r ∧ ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm less than or equal to one. -/
def balanced (A : set E) := ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variables {𝕜} {A B : set E}

lemma balanced_univ : balanced 𝕜 (univ : set E) := λ a ha, subset_univ _

lemma balanced.union (hA : balanced 𝕜 A) (hB : balanced 𝕜 B) : balanced 𝕜 (A ∪ B) :=
begin
  intros a ha t ht,
  rw [smul_set_union] at ht,
  exact ht.imp (λ x, hA _ ha x) (λ x, hB _ ha x),
end

end has_scalar

section add_comm_group
variables [add_comm_group E] [module 𝕜 E] {s t u v A B : set E}

lemma balanced.inter (hA : balanced 𝕜 A) (hB : balanced 𝕜 B) : balanced 𝕜 (A ∩ B) :=
begin
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩,
  exact ⟨hA _ ha ⟨_, hx₁, rfl⟩, hB _ ha ⟨_, hx₂, rfl⟩⟩,
end

lemma balanced.add (hA₁ : balanced 𝕜 A) (hA₂ : balanced 𝕜 B) : balanced 𝕜 (A + B) :=
begin
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩,
  rw smul_add,
  exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩,
end

lemma absorbs.mono (hs : absorbs 𝕜 s u) (hst : s ⊆ t) (hvu : v ⊆ u) : absorbs 𝕜 t v :=
let ⟨r, hr, h⟩ := hs in ⟨r, hr, λ a ha, hvu.trans $ (h _ ha).trans $ smul_set_mono hst⟩

lemma absorbs.mono_left (hs : absorbs 𝕜 s u) (h : s ⊆ t) : absorbs 𝕜 t u := hs.mono h subset.rfl
lemma absorbs.mono_right (hs : absorbs 𝕜 s u) (h : v ⊆ u) : absorbs 𝕜 s v := hs.mono subset.rfl h

lemma absorbs.union (hu : absorbs 𝕜 s u) (hv : absorbs 𝕜 s v) : absorbs 𝕜 s (u ∪ v) :=
begin
  obtain ⟨a, ha, hu⟩ := hu,
  obtain ⟨b, hb, hv⟩ := hv,
  exact ⟨max a b, lt_max_of_lt_left ha,
    λ c hc, union_subset (hu _ $ le_of_max_le_left hc) (hv _ $ le_of_max_le_right hc)⟩,
end

@[simp] lemma absorbs_union : absorbs 𝕜 s (u ∪ v) ↔ absorbs 𝕜 s u ∧ absorbs 𝕜 s v :=
⟨λ h, ⟨h.mono_right $ subset_union_left _ _, h.mono_right $ subset_union_right _ _⟩,
  λ h, h.1.union h.2⟩

lemma absorbent.subset (hA : absorbent 𝕜 A) (hAB : A ⊆ B) : absorbent 𝕜 B :=
begin
  rintro x,
  obtain ⟨r, hr, hx⟩ := hA x,
  exact ⟨r, hr, λ a ha, set.smul_set_mono hAB $ hx a ha⟩,
end

lemma absorbent_iff_forall_absorbs_singleton : absorbent 𝕜 A ↔ ∀ x, absorbs 𝕜 A {x} :=
by simp_rw [absorbs, absorbent, singleton_subset_iff]

lemma absorbent.absorbs (hs : absorbent 𝕜 s) {x : E} : absorbs 𝕜 s {x} :=
absorbent_iff_forall_absorbs_singleton.1 hs _

lemma absorbent_iff_nonneg_lt : absorbent 𝕜 A ↔ ∀ x, ∃ r, 0 ≤ r ∧ ∀ a : 𝕜, r < ∥a∥ → x ∈ a • A :=
begin
  split,
  { rintro hA x,
    obtain ⟨r, hr, hx⟩ := hA x,
    exact ⟨r, hr.le, λ a ha, hx a ha.le⟩ },
  { rintro hA x,
    obtain ⟨r, hr, hx⟩ := hA x,
    exact ⟨r + 1, add_pos_of_nonneg_of_pos hr zero_lt_one,
      λ a ha, hx a ((lt_add_of_pos_right r zero_lt_one).trans_le ha)⟩ }
end

end add_comm_group
end semi_normed_ring

section normed_comm_ring
variables [normed_comm_ring 𝕜] [add_comm_monoid E] [module 𝕜 E] {A B : set E} (a : 𝕜)

lemma balanced.smul (hA : balanced 𝕜 A) : balanced 𝕜 (a • A) :=
begin
  rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
  exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩,
end

end normed_comm_ring

section normed_field
variables [normed_field 𝕜] [normed_ring 𝕝] [normed_space 𝕜 𝕝] [add_comm_group E] [module 𝕜 E]
  [smul_with_zero 𝕝 E] [is_scalar_tower 𝕜 𝕝 E] {s t u v A B : set E} {a b : 𝕜}

/-- Scalar multiplication (by possibly different types) of a balanced set is monotone. -/
lemma balanced.smul_mono (hs : balanced 𝕝 s) {a : 𝕝} {b : 𝕜} (h : ∥a∥ ≤ ∥b∥) : a • s ⊆ b • s :=
begin
  obtain rfl | hb := eq_or_ne b 0,
  { rw norm_zero at h,
    rw norm_eq_zero.1 (h.antisymm $ norm_nonneg _),
    obtain rfl | h := s.eq_empty_or_nonempty,
    { simp_rw [smul_set_empty] },
    { simp_rw [zero_smul_set h] } },
  rintro _ ⟨x, hx, rfl⟩,
  refine ⟨b⁻¹ • a • x, _, smul_inv_smul₀ hb _⟩,
  rw ←smul_assoc,
  refine hs _ _ (smul_mem_smul_set hx),
  rw [norm_smul, norm_inv, ←div_eq_inv_mul],
  exact div_le_one_of_le h (norm_nonneg _),
end

/-- A balanced set absorbs itself. -/
lemma balanced.absorbs_self (hA : balanced 𝕜 A) : absorbs 𝕜 A A :=
begin
  use [1, zero_lt_one],
  intros a ha x hx,
  rw mem_smul_set_iff_inv_smul_mem₀,
  { apply hA a⁻¹,
    { rw norm_inv, exact inv_le_one ha },
    { rw mem_smul_set, use [x, hx] }},
  { rw ←norm_pos_iff, calc 0 < 1 : zero_lt_one ... ≤ ∥a∥ : ha, }
end

lemma balanced.subset_smul (hA : balanced 𝕜 A) (ha : 1 ≤ ∥a∥) : A ⊆ a • A :=
begin
  refine (subset_set_smul_iff₀ _).2 (hA (a⁻¹) _),
  { rintro rfl,
    rw norm_zero at ha,
    exact zero_lt_one.not_le ha },
  { rw norm_inv,
    exact inv_le_one ha }
end

lemma balanced.smul_eq (hA : balanced 𝕜 A) (ha : ∥a∥ = 1) : a • A = A :=
(hA _ ha.le).antisymm $ hA.subset_smul ha.ge

lemma absorbs.inter (hs : absorbs 𝕜 s u) (ht : absorbs 𝕜 t u) : absorbs 𝕜 (s ∩ t) u :=
begin
  obtain ⟨a, ha, hs⟩ := hs,
  obtain ⟨b, hb, ht⟩ := ht,
  have h : 0 < max a b := lt_max_of_lt_left ha,
  refine ⟨max a b, lt_max_of_lt_left ha, λ c hc, _⟩,
  rw smul_set_inter₀ (norm_pos_iff.1 $ h.trans_le hc),
  exact subset_inter (hs _ $ le_of_max_le_left hc) (ht _ $ le_of_max_le_right hc),
end

@[simp] lemma absorbs_inter : absorbs 𝕜 (s ∩ t) u ↔ absorbs 𝕜 s u ∧ absorbs 𝕜 t u :=
⟨λ h, ⟨h.mono_left $ inter_subset_left _ _, h.mono_left $ inter_subset_right _ _⟩,
  λ h, h.1.inter h.2⟩

lemma absorbent_univ : absorbent 𝕜 (univ : set E) :=
begin
  refine λ x, ⟨1, zero_lt_one, λ a ha, _⟩,
  rw smul_set_univ₀ (norm_pos_iff.1 $ zero_lt_one.trans_le ha),
  exact trivial,
end

/-! #### Topological vector space -/

variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : absorbent 𝕜 A :=
begin
  intro x,
  rcases mem_nhds_iff.mp hA with ⟨w, hw₁, hw₂, hw₃⟩,
  have hc : continuous (λ t : 𝕜, t • x), from continuous_id.smul continuous_const,
  rcases metric.is_open_iff.mp (hw₂.preimage hc) 0 (by rwa [mem_preimage, zero_smul])
    with ⟨r, hr₁, hr₂⟩,
  have hr₃, from inv_pos.mpr (half_pos hr₁),
  use [(r/2)⁻¹, hr₃],
  intros a ha₁,
  have ha₂ : 0 < ∥a∥ := hr₃.trans_le ha₁,
  rw [mem_smul_set_iff_inv_smul_mem₀ (norm_pos_iff.mp ha₂)],
  refine hw₁ (hr₂ _),
  rw [metric.mem_ball, dist_zero_right, norm_inv],
  calc ∥a∥⁻¹ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).mp ha₁
  ...       < r : half_lt_self hr₁,
end

/-- The union of `{0}` with the interior of a balanced set is balanced. -/
lemma balanced_zero_union_interior (hA : balanced 𝕜 A) : balanced 𝕜 ((0 : set E) ∪ interior A) :=
begin
  intros a ha, by_cases a = 0,
  { rw [h, zero_smul_set],
    exacts [subset_union_left _ _, ⟨0, or.inl rfl⟩] },
  { rw [←image_smul, image_union],
    apply union_subset_union,
    { rw [image_zero, smul_zero],
      refl },
    { calc a • interior A ⊆ interior (a • A) : (is_open_map_smul₀ h).image_interior_subset A
                      ... ⊆ interior A       : interior_mono (hA _ ha) } }
end

/-- The interior of a balanced set is balanced if it contains the origin. -/
lemma balanced.interior (hA : balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
  balanced 𝕜 (interior A) :=
begin
  rw ←singleton_subset_iff at h,
  rw [←union_eq_self_of_subset_left h],
  exact balanced_zero_union_interior hA,
end

/-- The closure of a balanced set is balanced. -/
lemma balanced.closure (hA : balanced 𝕜 A) : balanced 𝕜 (closure A) :=
assume a ha,
calc _ ⊆ closure (a • A) : image_closure_subset_closure_image (continuous_id.const_smul _)
...    ⊆ _ : closure_mono (hA _ ha)

end normed_field

section nondiscrete_normed_field
variables [nondiscrete_normed_field 𝕜] [add_comm_group E] [module 𝕜 E] {s : set E}

lemma absorbs_zero_iff : absorbs 𝕜 s 0 ↔ (0 : E) ∈ s :=
begin
  refine ⟨_, λ h, ⟨1, zero_lt_one, λ a _, zero_subset.2 $ zero_mem_smul_set h⟩⟩,
  rintro ⟨r, hr, h⟩,
  obtain ⟨a, ha⟩ := normed_space.exists_lt_norm 𝕜 𝕜 r,
  have := h _ ha.le,
  rwa [zero_subset, zero_mem_smul_set_iff] at this,
  exact norm_ne_zero_iff.1 (hr.trans ha).ne',
end

lemma absorbent.zero_mem (hs : absorbent 𝕜 s) : (0 : E) ∈ s :=
absorbs_zero_iff.1 $ absorbent_iff_forall_absorbs_singleton.1 hs _

end nondiscrete_normed_field

/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*) [semi_normed_ring 𝕜] [add_monoid E] [has_scalar 𝕜 E] :=
(to_fun    : E → ℝ)
(smul'     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

namespace seminorm

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_monoid
variables [add_monoid E]

section has_scalar
variables [has_scalar 𝕜 E]

instance fun_like : fun_like (seminorm 𝕜 E) E (λ _, ℝ) :=
{ coe := seminorm.to_fun, coe_injective' := λ f g h, by cases f; cases g; congr' }

/-- Helper instance for when there's too many metavariables to apply `to_fun.to_coe_fn`. -/
instance : has_coe_to_fun (seminorm 𝕜 E) (λ _, E → ℝ) := ⟨λ p, p.to_fun⟩

@[ext] lemma ext {p q : seminorm 𝕜 E} (h : ∀ x, (p : E → ℝ) x = q x) : p = q := fun_like.ext p q h

instance : has_zero (seminorm 𝕜 E) :=
⟨{ to_fun    := 0,
  smul'     := λ _ _, (mul_zero _).symm,
  triangle' := λ _ _, eq.ge (zero_add _) }⟩

@[simp] lemma coe_zero : ⇑(0 : seminorm 𝕜 E) = 0 := rfl

@[simp] lemma zero_apply (x : E) : (0 : seminorm 𝕜 E) x = 0 := rfl

instance : inhabited (seminorm 𝕜 E) := ⟨0⟩

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected lemma smul : p (c • x) = ∥c∥ * p x := p.smul' _ _
protected lemma triangle : p (x + y) ≤ p x + p y := p.triangle' _ _

/-- Any action on `ℝ` which factors through `ℝ≥0` applies to a seminorm. -/
instance [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  has_scalar R (seminorm 𝕜 E) :=
{ smul := λ r p,
  { to_fun := λ x, r • p x,
    smul' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      rw [p.smul, mul_left_comm],
    end,
    triangle' := λ _ _, begin
      simp only [←smul_one_smul ℝ≥0 r (_ : ℝ), nnreal.smul_def, smul_eq_mul],
      exact (mul_le_mul_of_nonneg_left (p.triangle _ _) (nnreal.coe_nonneg _)).trans_eq
        (mul_add _ _ _),
    end } }

lemma coe_smul [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p : seminorm 𝕜 E) : ⇑(r • p) = r • p := rfl

@[simp] lemma smul_apply [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]
  (r : R) (p : seminorm 𝕜 E) (x : E) : (r • p) x = r • p x := rfl

instance : has_add (seminorm 𝕜 E) :=
{ add := λ p q,
  { to_fun := λ x, p x + q x,
    smul' := λ a x, by rw [p.smul, q.smul, mul_add],
    triangle' := λ _ _, has_le.le.trans_eq (add_le_add (p.triangle _ _) (q.triangle _ _))
      (add_add_add_comm _ _ _ _) } }

lemma coe_add (p q : seminorm 𝕜 E) : ⇑(p + q) = p + q := rfl

@[simp] lemma add_apply (p q : seminorm 𝕜 E) (x : E) : (p + q) x = p x + q x := rfl

instance : add_monoid (seminorm 𝕜 E) :=
fun_like.coe_injective.add_monoid_smul _ rfl coe_add (λ p n, coe_smul n p)

instance : ordered_cancel_add_comm_monoid (seminorm 𝕜 E) :=
{ nsmul := (•),  -- to avoid introducing a diamond
  ..seminorm.add_monoid,
  ..(fun_like.coe_injective.ordered_cancel_add_comm_monoid _ rfl coe_add
      : ordered_cancel_add_comm_monoid (seminorm 𝕜 E)) }

instance [monoid R] [mul_action R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  mul_action R (seminorm 𝕜 E) :=
fun_like.coe_injective.mul_action _ coe_smul

variables (𝕜 E)

/-- `coe_fn` as an `add_monoid_hom`. Helper definition for showing that `seminorm 𝕜 E` is
a module. -/
@[simps]
def coe_fn_add_monoid_hom : add_monoid_hom (seminorm 𝕜 E) (E → ℝ) := ⟨coe_fn, coe_zero, coe_add⟩

lemma coe_fn_add_monoid_hom_injective : function.injective (coe_fn_add_monoid_hom 𝕜 E) :=
show @function.injective (seminorm 𝕜 E) (E → ℝ) coe_fn, from fun_like.coe_injective

variables {𝕜 E}

instance [monoid R] [distrib_mul_action R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  distrib_mul_action R (seminorm 𝕜 E) :=
(coe_fn_add_monoid_hom_injective 𝕜 E).distrib_mul_action _ coe_smul

instance [semiring R] [module R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ] :
  module R (seminorm 𝕜 E) :=
(coe_fn_add_monoid_hom_injective 𝕜 E).module R _ coe_smul

-- TODO: define `has_Sup` too, from the skeleton at
-- https://github.com/leanprover-community/mathlib/pull/11329#issuecomment-1008915345
noncomputable instance : has_sup (seminorm 𝕜 E) :=
{ sup := λ p q,
  { to_fun := p ⊔ q,
    triangle' := λ x y, sup_le
      ((p.triangle x y).trans $ add_le_add le_sup_left le_sup_left)
      ((q.triangle x y).trans $ add_le_add le_sup_right le_sup_right),
    smul' := λ x v, (congr_arg2 max (p.smul x v) (q.smul x v)).trans $
      (mul_max_of_nonneg _ _ $ norm_nonneg x).symm } }

@[simp] lemma coe_sup (p q : seminorm 𝕜 E) : ⇑(p ⊔ q) = p ⊔ q := rfl

instance : partial_order (seminorm 𝕜 E) :=
  partial_order.lift _ fun_like.coe_injective

lemma le_def (p q : seminorm 𝕜 E) : p ≤ q ↔ (p : E → ℝ) ≤ q := iff.rfl
lemma lt_def (p q : seminorm 𝕜 E) : p < q ↔ (p : E → ℝ) < q := iff.rfl

noncomputable instance : semilattice_sup (seminorm 𝕜 E) :=
function.injective.semilattice_sup _ fun_like.coe_injective coe_sup

end has_scalar

section smul_with_zero
variables [smul_with_zero 𝕜 E] (p : seminorm 𝕜 E)

@[simp]
protected lemma zero : p 0 = 0 :=
calc p 0 = p ((0 : 𝕜) • 0) : by rw zero_smul
...      = 0 : by rw [p.smul, norm_zero, zero_mul]

end smul_with_zero
end add_monoid

section module
variables [add_comm_group E] [add_comm_group F] [add_comm_group G]
variables [module 𝕜 E] [module 𝕜 F] [module 𝕜 G]
variables [has_scalar R ℝ] [has_scalar R ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ]

/-- Composition of a seminorm with a linear map is a seminorm. -/
def comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : seminorm 𝕜 E :=
{ to_fun := λ x, p(f x),
  smul' := λ _ _, (congr_arg p (f.map_smul _ _)).trans (p.smul _ _),
  triangle' := λ _ _, eq.trans_le (congr_arg p (f.map_add _ _)) (p.triangle _ _) }

lemma coe_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : ⇑(p.comp f) = p ∘ f := rfl

@[simp] lemma comp_apply (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) : (p.comp f) x = p (f x) := rfl

@[simp] lemma comp_id (p : seminorm 𝕜 E) : p.comp linear_map.id = p :=
ext $ λ _, rfl

@[simp] lemma comp_zero (p : seminorm 𝕜 F) : p.comp (0 : E →ₗ[𝕜] F) = 0 :=
ext $ λ _, seminorm.zero _

@[simp] lemma zero_comp (f : E →ₗ[𝕜] F) : (0 : seminorm 𝕜 F).comp f = 0 :=
ext $ λ _, rfl

lemma comp_comp (p : seminorm 𝕜 G) (g : F →ₗ[𝕜] G) (f : E →ₗ[𝕜] F) :
  p.comp (g.comp f) = (p.comp g).comp f :=
ext $ λ _, rfl

lemma add_comp (p q : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : (p + q).comp f = p.comp f + q.comp f :=
ext $ λ _, rfl

lemma comp_triangle (p : seminorm 𝕜 F) (f g : E →ₗ[𝕜] F) : p.comp (f + g) ≤ p.comp f + p.comp g :=
λ _, p.triangle _ _

lemma smul_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : R) : (c • p).comp f = c • (p.comp f) :=
ext $ λ _, rfl

lemma comp_mono {p : seminorm 𝕜 F} {q : seminorm 𝕜 F} (f : E →ₗ[𝕜] F) (hp : p ≤ q) :
  p.comp f ≤ q.comp f := λ _, hp _

/-- The composition as an `add_monoid_hom`. -/
@[simps] def pullback (f : E →ₗ[𝕜] F) : add_monoid_hom (seminorm 𝕜 F) (seminorm 𝕜 E) :=
⟨λ p, p.comp f, zero_comp f, λ p q, add_comp p q f⟩

section norm_one_class
variables [norm_one_class 𝕜] (p : seminorm 𝕜 E) (x y : E) (r : ℝ)

@[simp]
protected lemma neg : p (-x) = p x :=
calc p (-x) = p ((-1 : 𝕜) • x) : by rw neg_one_smul
...         = p x : by rw [p.smul, norm_neg, norm_one, one_mul]

protected lemma sub_le : p (x - y) ≤ p x + p y :=
calc
  p (x - y)
      = p (x + -y) : by rw sub_eq_add_neg
  ... ≤ p x + p (-y) : p.triangle x (-y)
  ... = p x + p y : by rw p.neg

lemma nonneg : 0 ≤ p x :=
have h: 0 ≤ 2 * p x, from
calc 0 = p (x + (- x)) : by rw [add_neg_self, p.zero]
...    ≤ p x + p (-x)  : p.triangle _ _
...    = 2 * p x : by rw [p.neg, two_mul],
nonneg_of_mul_nonneg_left h zero_lt_two

lemma sub_rev : p (x - y) = p (y - x) := by rw [←neg_sub, p.neg]

instance : order_bot (seminorm 𝕜 E) := ⟨0, nonneg⟩

@[simp] lemma coe_bot : ⇑(⊥ : seminorm 𝕜 E) = 0 := rfl

lemma bot_eq_zero : (⊥ : seminorm 𝕜 E) = 0 := rfl

lemma smul_le_smul {p q : seminorm 𝕜 E} {a b : ℝ≥0} (hpq : p ≤ q) (hab : a ≤ b) :
  a • p ≤ b • q :=
begin
  simp_rw [le_def, pi.le_def, coe_smul],
  intros x,
  simp_rw [pi.smul_apply, nnreal.smul_def, smul_eq_mul],
  exact mul_le_mul hab (hpq x) (nonneg p x) (nnreal.coe_nonneg b),
end

lemma finset_sup_apply (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) :
  s.sup p x = ↑(s.sup (λ i, ⟨p i x, nonneg (p i) x⟩) : ℝ≥0) :=
begin
  induction s using finset.cons_induction_on with a s ha ih,
  { rw [finset.sup_empty, finset.sup_empty, coe_bot, _root_.bot_eq_zero, pi.zero_apply,
        nonneg.coe_zero] },
  { rw [finset.sup_cons, finset.sup_cons, coe_sup, sup_eq_max, pi.sup_apply, sup_eq_max,
        nnreal.coe_max, subtype.coe_mk, ih] }
end

lemma finset_sup_le_sum (p : ι → seminorm 𝕜 E) (s : finset ι) : s.sup p ≤ ∑ i in s, p i :=
begin
  classical,
  refine finset.sup_le_iff.mpr _,
  intros i hi,
  rw [finset.sum_eq_sum_diff_singleton_add hi, le_add_iff_nonneg_left],
  exact bot_le,
end

end norm_one_class
end module
end semi_normed_ring

section semi_normed_comm_ring
variables [semi_normed_comm_ring 𝕜] [add_comm_group E] [add_comm_group F] [module 𝕜 E] [module 𝕜 F]

lemma comp_smul (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) :
  p.comp (c • f) = ∥c∥₊ • p.comp f :=
ext $ λ _, by rw [comp_apply, smul_apply, linear_map.smul_apply, p.smul, nnreal.smul_def,
  coe_nnnorm, smul_eq_mul, comp_apply]

lemma comp_smul_apply (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (c : 𝕜) (x : E) :
  p.comp (c • f) x = ∥c∥ * p (f x) := p.smul _ _

end semi_normed_comm_ring

/-! ### Seminorm ball -/

section semi_normed_ring
variables [semi_normed_ring 𝕜]

section add_comm_group
variables [add_comm_group E]

section has_scalar
variables [has_scalar 𝕜 E] (p : seminorm 𝕜 E)

/-- The ball of radius `r` at `x` with respect to seminorm `p` is the set of elements `y` with
`p (y - x) < `r`. -/
def ball (x : E) (r : ℝ) := { y : E | p (y - x) < r }

variables {x y : E} {r : ℝ}

@[simp] lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r := iff.rfl

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r := by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } := set.ext $ λ x, p.mem_ball_zero

@[simp] lemma ball_zero' (x : E) (hr : 0 < r) : ball (0 : seminorm 𝕜 E) x r = set.univ :=
begin
  rw [set.eq_univ_iff_forall, ball],
  simp [hr],
end

lemma ball_smul (p : seminorm 𝕜 E) {c : nnreal} (hc : 0 < c) (r : ℝ) (x : E) :
  (c • p).ball x r = p.ball x (r / c) :=
by { ext, rw [mem_ball, mem_ball, smul_apply, nnreal.smul_def, smul_eq_mul, mul_comm,
  lt_div_iff (nnreal.coe_pos.mpr hc)] }

lemma ball_sup (p : seminorm 𝕜 E) (q : seminorm 𝕜 E) (e : E) (r : ℝ) :
  ball (p ⊔ q) e r = ball p e r ∩ ball q e r :=
by simp_rw [ball, ←set.set_of_and, coe_sup, pi.sup_apply, sup_lt_iff]

lemma ball_finset_sup' (p : ι → seminorm 𝕜 E) (s : finset ι) (H : s.nonempty) (e : E) (r : ℝ) :
  ball (s.sup' H p) e r = s.inf' H (λ i, ball (p i) e r) :=
begin
  induction H using finset.nonempty.cons_induction with a a s ha hs ih,
  { classical, simp },
  { rw [finset.sup'_cons hs, finset.inf'_cons hs, ball_sup, inf_eq_inter, ih] },
end

lemma ball_mono {p : seminorm 𝕜 E} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) : p.ball x r₁ ⊆ p.ball x r₂ :=
λ _ (hx : _ < _), hx.trans_le h

lemma ball_antitone {p q : seminorm 𝕜 E} (h : q ≤ p) : p.ball x r ⊆ q.ball x r :=
λ _, (h _).trans_lt

lemma ball_add_ball_subset (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) (x₁ x₂ : E):
  p.ball (x₁ : E) r₁ + p.ball (x₂ : E) r₂ ⊆ p.ball (x₁ + x₂) (r₁ + r₂) :=
begin
  rintros x ⟨y₁, y₂, hy₁, hy₂, rfl⟩,
  rw [mem_ball, add_sub_comm],
  exact (p.triangle _ _).trans_lt (add_lt_add hy₁ hy₂),
end

end has_scalar

section module

variables [module 𝕜 E]
variables [add_comm_group F] [module 𝕜 F]

lemma ball_comp (p : seminorm 𝕜 F) (f : E →ₗ[𝕜] F) (x : E) (r : ℝ) :
  (p.comp f).ball x r = f ⁻¹' (p.ball (f x) r) :=
begin
  ext,
  simp_rw [ball, mem_preimage, comp_apply, set.mem_set_of_eq, map_sub],
end

section norm_one_class
variables [norm_one_class 𝕜] (p : seminorm 𝕜 E)

@[simp] lemma ball_bot {r : ℝ} (x : E) (hr : 0 < r) : ball (⊥ : seminorm 𝕜 E) x r = set.univ :=
ball_zero' x hr

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero (r : ℝ) : balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, p.smul],
  calc _ ≤ p y : mul_le_of_le_one_left (p.nonneg _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

lemma ball_finset_sup_eq_Inter (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ} (hr : 0 < r) :
  ball (s.sup p) x r = ⋂ (i ∈ s), ball (p i) x r :=
begin
  lift r to nnreal using hr.le,
  simp_rw [ball, Inter_set_of, finset_sup_apply, nnreal.coe_lt_coe,
    finset.sup_lt_iff (show ⊥ < r, from hr), ←nnreal.coe_lt_coe, subtype.coe_mk],
end

lemma ball_finset_sup (p : ι → seminorm 𝕜 E) (s : finset ι) (x : E) {r : ℝ}
  (hr : 0 < r) : ball (s.sup p) x r = s.inf (λ i, ball (p i) x r) :=
begin
  rw finset.inf_eq_infi,
  exact ball_finset_sup_eq_Inter _ _ _ hr,
end

lemma ball_smul_ball (p : seminorm 𝕜 E) (r₁ r₂ : ℝ) :
  metric.ball (0 : 𝕜) r₁ • p.ball 0 r₂ ⊆ p.ball 0 (r₁ * r₂) :=
begin
  rw set.subset_def,
  intros x hx,
  rw set.mem_smul at hx,
  rcases hx with ⟨a, y, ha, hy, hx⟩,
  rw [←hx, mem_ball_zero, seminorm.smul],
  exact mul_lt_mul'' (mem_ball_zero_iff.mp ha) (p.mem_ball_zero.mp hy) (norm_nonneg a) (p.nonneg y),
end

end norm_one_class
end module
end add_comm_group
end semi_normed_ring

section normed_field
variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] (p : seminorm 𝕜 E) {A B : set E}
  {a : 𝕜} {r : ℝ} {x : E}

/-- Seminorm-balls at the origin are absorbent. -/
protected lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (ball p (0 : E) r) :=
begin
  rw absorbent_iff_nonneg_lt,
  rintro x,
  have hxr : 0 ≤ p x/r := div_nonneg (p.nonneg _) hr.le,
  refine ⟨p x/r, hxr, λ a ha, _⟩,
  have ha₀ : 0 < ∥a∥ := hxr.trans_lt ha,
  refine ⟨a⁻¹ • x, _, smul_inv_smul₀ (norm_pos_iff.1 ha₀) x⟩,
  rwa [mem_ball_zero, p.smul, norm_inv, inv_mul_lt_iff ha₀, ←div_lt_iff hr],
end

/-- Seminorm-balls containing the origin are absorbent. -/
protected lemma absorbent_ball (hpr : p x < r) : absorbent 𝕜 (ball p x r) :=
begin
  refine (p.absorbent_ball_zero $ sub_pos.2 hpr).subset (λ y hy, _),
  rw p.mem_ball_zero at hy,
  exact p.mem_ball.2 ((p.sub_le _ _).trans_lt $ add_lt_of_lt_sub_right hy),
end

lemma symmetric_ball_zero (r : ℝ) (hx : x ∈ ball p 0 r) : -x ∈ ball p 0 r :=
balanced_ball_zero p r (-1) (by rw [norm_neg, norm_one]) ⟨x, hx, by rw [neg_smul, one_smul]⟩

@[simp]
lemma neg_ball (p : seminorm 𝕜 E) (r : ℝ) (x : E) :
  -ball p x r = ball p (-x) r :=
by { ext, rw [mem_neg, mem_ball, mem_ball, ←neg_add', sub_neg_eq_add, p.neg], }

@[simp]
lemma smul_ball_preimage (p : seminorm 𝕜 E) (y : E) (r : ℝ) (a : 𝕜) (ha : a ≠ 0) :
  ((•) a) ⁻¹' p.ball y r = p.ball (a⁻¹ • y) (r / ∥a∥) :=
set.ext $ λ _, by rw [mem_preimage, mem_ball, mem_ball,
  lt_div_iff (norm_pos_iff.mpr ha), mul_comm, ←p.smul, smul_sub, smul_inv_smul₀ ha]

end normed_field

section normed_linear_ordered_field
variables [normed_linear_ordered_field 𝕜] [add_comm_group E] [normed_space ℝ 𝕜] [module 𝕜 E]

section has_scalar
variables [has_scalar ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E)

/-- A seminorm is convex. Also see `convex_on_norm`. -/
protected lemma convex_on : convex_on ℝ univ p :=
begin
  refine ⟨convex_univ, λ x y _ _ a b ha hb hab, _⟩,
  calc p (a • x + b • y) ≤ p (a • x) + p (b • y) : p.triangle _ _
    ... = ∥a • (1 : 𝕜)∥ * p x + ∥b • (1 : 𝕜)∥ * p y
        : by rw [←p.smul, ←p.smul, smul_one_smul, smul_one_smul]
    ... = a * p x + b * p y
        : by rw [norm_smul, norm_smul, norm_one, mul_one, mul_one, real.norm_of_nonneg ha,
            real.norm_of_nonneg hb],
end

end has_scalar

section module
variables [module ℝ E] [is_scalar_tower ℝ 𝕜 E] (p : seminorm 𝕜 E) (x : E) (r : ℝ)

/-- Seminorm-balls are convex. -/
lemma convex_ball : convex ℝ (ball p x r) :=
begin
  convert (p.convex_on.translate_left (-x)).convex_lt r,
  ext y,
  rw [preimage_univ, sep_univ, p.mem_ball, sub_eq_add_neg],
  refl,
end

end module
end normed_linear_ordered_field

-- TODO: convexity and absorbent/balanced sets in vector spaces over ℝ

end seminorm

/-! ### The norm as a seminorm -/

section norm_seminorm
variables (𝕜 E) [normed_field 𝕜] [semi_normed_group E] [normed_space 𝕜 E] {r : ℝ}

/-- The norm of a seminormed group as a seminorm. -/
def norm_seminorm : seminorm 𝕜 E := ⟨norm, norm_smul, norm_add_le⟩

@[simp] lemma coe_norm_seminorm : ⇑(norm_seminorm 𝕜 E) = norm := rfl

@[simp] lemma ball_norm_seminorm : (norm_seminorm 𝕜 E).ball = metric.ball :=
by { ext x r y, simp only [seminorm.mem_ball, metric.mem_ball, coe_norm_seminorm, dist_eq_norm] }

variables {𝕜 E} {x : E}

/-- Balls at the origin are absorbent. -/
lemma absorbent_ball_zero (hr : 0 < r) : absorbent 𝕜 (metric.ball (0 : E) r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).absorbent_ball_zero hr }

/-- Balls containing the origin are absorbent. -/
lemma absorbent_ball (hx : ∥x∥ < r) : absorbent 𝕜 (metric.ball x r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).absorbent_ball hx }

/-- Balls at the origin are balanced. -/
lemma balanced_ball_zero [norm_one_class 𝕜] : balanced 𝕜 (metric.ball (0 : E) r) :=
by { rw ←ball_norm_seminorm 𝕜, exact (norm_seminorm _ _).balanced_ball_zero r }

end norm_seminorm

/-! ### Minkowksi functional -/

section gauge
noncomputable theory

section add_comm_group
variables [add_comm_group E] [module ℝ E]

/--The Minkowski functional. Given a set `s` in a real vector space, `gauge s` is the functional
which sends `x : E` to the smallest `r : ℝ` such that `x` is in `s` scaled by `r`. -/
def gauge (s : set E) (x : E) : ℝ := Inf {r : ℝ | 0 < r ∧ x ∈ r • s}

variables {s t : set E} {a : ℝ} {x : E}

lemma gauge_def : gauge s x = Inf {r ∈ set.Ioi 0 | x ∈ r • s} := rfl

/-- An alternative definition of the gauge using scalar multiplication on the element rather than on
the set. -/
lemma gauge_def' : gauge s x = Inf {r ∈ set.Ioi 0 | r⁻¹ • x ∈ s} :=
begin
  unfold gauge,
  congr' 1,
  ext r,
  exact and_congr_right (λ hr, mem_smul_set_iff_inv_smul_mem₀ hr.ne' _ _),
end

private lemma gauge_set_bdd_below : bdd_below {r : ℝ | 0 < r ∧ x ∈ r • s} := ⟨0, λ r hr, hr.1.le⟩

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
lemma absorbent.gauge_set_nonempty (absorbs : absorbent ℝ s) :
  {r : ℝ | 0 < r ∧ x ∈ r • s}.nonempty :=
let ⟨r, hr₁, hr₂⟩ := absorbs x in ⟨r, hr₁, hr₂ r (real.norm_of_nonneg hr₁.le).ge⟩

lemma gauge_mono (hs : absorbent ℝ s) (h : s ⊆ t) : gauge t ≤ gauge s :=
λ x, cInf_le_cInf gauge_set_bdd_below hs.gauge_set_nonempty $ λ r hr, ⟨hr.1, smul_set_mono h hr.2⟩

lemma exists_lt_of_gauge_lt (absorbs : absorbent ℝ s) (h : gauge s x < a) :
  ∃ b, 0 < b ∧ b < a ∧ x ∈ b • s :=
begin
  obtain ⟨b, ⟨hb, hx⟩, hba⟩ := exists_lt_of_cInf_lt absorbs.gauge_set_nonempty h,
  exact ⟨b, hb, hba, hx⟩,
end

/-- The gauge evaluated at `0` is always zero (mathematically this requires `0` to be in the set `s`
but, the real infimum of the empty set in Lean being defined as `0`, it holds unconditionally). -/
@[simp] lemma gauge_zero : gauge s 0 = 0 :=
begin
  rw gauge_def',
  by_cases (0 : E) ∈ s,
  { simp only [smul_zero, sep_true, h, cInf_Ioi] },
  { simp only [smul_zero, sep_false, h, real.Inf_empty] }
end

@[simp] lemma gauge_zero' : gauge (0 : set E) = 0 :=
begin
  ext,
  rw gauge_def',
  obtain rfl | hx := eq_or_ne x 0,
  { simp only [cInf_Ioi, mem_zero, pi.zero_apply, eq_self_iff_true, sep_true, smul_zero] },
  { simp only [mem_zero, pi.zero_apply, inv_eq_zero, smul_eq_zero],
    convert real.Inf_empty,
    exact eq_empty_iff_forall_not_mem.2 (λ r hr, hr.2.elim (ne_of_gt hr.1) hx) }
end

@[simp] lemma gauge_empty : gauge (∅ : set E) = 0 :=
by { ext, simp only [gauge_def', real.Inf_empty, mem_empty_eq, pi.zero_apply, sep_false] }

lemma gauge_of_subset_zero (h : s ⊆ 0) : gauge s = 0 :=
by { obtain rfl | rfl := subset_singleton_iff_eq.1 h, exacts [gauge_empty, gauge_zero'] }

/-- The gauge is always nonnegative. -/
lemma gauge_nonneg (x : E) : 0 ≤ gauge s x := real.Inf_nonneg _ $ λ x hx, hx.1.le

lemma gauge_neg (symmetric : ∀ x ∈ s, -x ∈ s) (x : E) : gauge s (-x) = gauge s x :=
begin
  have : ∀ x, -x ∈ s ↔ x ∈ s := λ x, ⟨λ h, by simpa using symmetric _ h, symmetric x⟩,
  rw [gauge_def', gauge_def'],
  simp_rw [smul_neg, this],
end

lemma gauge_le_of_mem (ha : 0 ≤ a) (hx : x ∈ a • s) : gauge s x ≤ a :=
begin
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [mem_singleton_iff.1 (zero_smul_subset _ hx), gauge_zero] },
  { exact cInf_le gauge_set_bdd_below ⟨ha', hx⟩ }
end

lemma gauge_le_eq (hs₁ : convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : absorbent ℝ s) (ha : 0 ≤ a) :
  {x | gauge s x ≤ a} = ⋂ (r : ℝ) (H : a < r), r • s :=
begin
  ext,
  simp_rw [set.mem_Inter, set.mem_set_of_eq],
  split,
  { intros h r hr,
    have hr' := ha.trans_lt hr,
    rw mem_smul_set_iff_inv_smul_mem₀ hr'.ne',
    obtain ⟨δ, δ_pos, hδr, hδ⟩ := exists_lt_of_gauge_lt hs₂ (h.trans_lt hr),
    suffices : (r⁻¹ * δ) • δ⁻¹ • x ∈ s,
    { rwa [smul_smul, mul_inv_cancel_right₀ δ_pos.ne'] at this },
    rw mem_smul_set_iff_inv_smul_mem₀ δ_pos.ne' at hδ,
    refine hs₁.smul_mem_of_zero_mem hs₀ hδ
      ⟨mul_nonneg (inv_nonneg.2 hr'.le) δ_pos.le, _⟩,
    rw [inv_mul_le_iff hr', mul_one],
    exact hδr.le },
  { refine λ h, le_of_forall_pos_lt_add (λ ε hε, _),
    have hε' := (lt_add_iff_pos_right a).2 (half_pos hε),
    exact (gauge_le_of_mem (ha.trans hε'.le) $ h _ hε').trans_lt
      (add_lt_add_left (half_lt_self hε) _) }
end

lemma gauge_lt_eq' (absorbs : absorbent ℝ s) (a : ℝ) :
  {x | gauge s x < a} = ⋃ (r : ℝ) (H : 0 < r) (H : r < a), r • s :=
begin
  ext,
  simp_rw [mem_set_of_eq, mem_Union, exists_prop],
  exact ⟨exists_lt_of_gauge_lt absorbs,
    λ ⟨r, hr₀, hr₁, hx⟩, (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩,
end

lemma gauge_lt_eq (absorbs : absorbent ℝ s) (a : ℝ) :
  {x | gauge s x < a} = ⋃ (r ∈ set.Ioo 0 (a : ℝ)), r • s :=
begin
  ext,
  simp_rw [mem_set_of_eq, mem_Union, exists_prop, mem_Ioo, and_assoc],
  exact ⟨exists_lt_of_gauge_lt absorbs,
    λ ⟨r, hr₀, hr₁, hx⟩, (gauge_le_of_mem hr₀.le hx).trans_lt hr₁⟩,
end

lemma gauge_lt_one_subset_self (hs : convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : absorbent ℝ s) :
  {x | gauge s x < 1} ⊆ s :=
begin
  rw gauge_lt_eq absorbs,
  apply set.Union₂_subset,
  rintro r hr _ ⟨y, hy, rfl⟩,
  exact hs.smul_mem_of_zero_mem h₀ hy (Ioo_subset_Icc_self hr),
end

lemma gauge_le_one_of_mem {x : E} (hx : x ∈ s) : gauge s x ≤ 1 :=
gauge_le_of_mem zero_le_one $ by rwa one_smul

lemma self_subset_gauge_le_one : s ⊆ {x | gauge s x ≤ 1} := λ x, gauge_le_one_of_mem

lemma convex.gauge_le (hs : convex ℝ s) (h₀ : (0 : E) ∈ s) (absorbs : absorbent ℝ s) (a : ℝ) :
  convex ℝ {x | gauge s x ≤ a} :=
begin
  by_cases ha : 0 ≤ a,
  { rw gauge_le_eq hs h₀ absorbs ha,
    exact convex_Inter (λ i, convex_Inter (λ hi, hs.smul _)) },
  { convert convex_empty,
    exact eq_empty_iff_forall_not_mem.2 (λ x hx, ha $ (gauge_nonneg _).trans hx) }
end

lemma balanced.star_convex (hs : balanced ℝ s) : star_convex ℝ 0 s :=
star_convex_zero_iff.2 $ λ x hx a ha₀ ha₁,
  hs _ (by rwa real.norm_of_nonneg ha₀) (smul_mem_smul_set hx)

lemma le_gauge_of_not_mem (hs₀ : star_convex ℝ 0 s) (hs₂ : absorbs ℝ s {x}) (hx : x ∉ a • s) :
  a ≤ gauge s x :=
begin
  rw star_convex_zero_iff at hs₀,
  obtain ⟨r, hr, h⟩ := hs₂,
  refine le_cInf ⟨r, hr, singleton_subset_iff.1 $ h _ (real.norm_of_nonneg hr.le).ge⟩ _,
  rintro b ⟨hb, x, hx', rfl⟩,
  refine not_lt.1 (λ hba, hx _),
  have ha := hb.trans hba,
  refine ⟨(a⁻¹ * b) • x, hs₀ hx' (mul_nonneg (inv_nonneg.2 ha.le) hb.le) _, _⟩,
  { rw ←div_eq_inv_mul,
    exact div_le_one_of_le hba.le ha.le },
  { rw [←mul_smul, mul_inv_cancel_left₀ ha.ne'] }
end

lemma one_le_gauge_of_not_mem (hs₁ : star_convex ℝ 0 s) (hs₂ : absorbs ℝ s {x}) (hx : x ∉ s) :
  1 ≤ gauge s x :=
le_gauge_of_not_mem hs₁ hs₂ $ by rwa one_smul

section linear_ordered_field
variables {α : Type*} [linear_ordered_field α] [mul_action_with_zero α ℝ] [ordered_smul α ℝ]

lemma gauge_smul_of_nonneg [mul_action_with_zero α E] [is_scalar_tower α ℝ (set E)] {s : set E}
  {r : α} (hr : 0 ≤ r) (x : E) :
  gauge s (r • x) = r • gauge s x :=
begin
  obtain rfl | hr' := hr.eq_or_lt,
  { rw [zero_smul, gauge_zero, zero_smul] },
  rw [gauge_def', gauge_def', ←real.Inf_smul_of_nonneg hr],
  congr' 1,
  ext β,
  simp_rw [set.mem_smul_set, set.mem_sep_eq],
  split,
  { rintro ⟨hβ, hx⟩,
    simp_rw [mem_Ioi] at ⊢ hβ,
    have := smul_pos (inv_pos.2 hr') hβ,
    refine ⟨r⁻¹ • β, ⟨this, _⟩, smul_inv_smul₀ hr'.ne' _⟩,
    rw ←mem_smul_set_iff_inv_smul_mem₀ at ⊢ hx,
    rwa [smul_assoc, mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr'.ne'), inv_inv₀],
    { exact this.ne' },
    { exact hβ.ne' } },
  { rintro ⟨β, ⟨hβ, hx⟩, rfl⟩,
    rw mem_Ioi at ⊢ hβ,
    have := smul_pos hr' hβ,
    refine ⟨this, _⟩,
    rw ←mem_smul_set_iff_inv_smul_mem₀ at ⊢ hx,
    rw smul_assoc,
    exact smul_mem_smul_set hx,
    { exact this.ne' },
    { exact hβ.ne'} }
end

/-- In textbooks, this is the homogeneity of the Minkowksi functional. -/
lemma gauge_smul [module α E] [is_scalar_tower α ℝ (set E)] {s : set E}
  (symmetric : ∀ x ∈ s, -x ∈ s) (r : α) (x : E) :
  gauge s (r • x) = abs r • gauge s x :=
begin
  rw ←gauge_smul_of_nonneg (abs_nonneg r),
  obtain h | h := abs_choice r,
  { rw h },
  { rw [h, neg_smul, gauge_neg symmetric] },
  { apply_instance }
end

lemma gauge_smul_left_of_nonneg [mul_action_with_zero α E] [smul_comm_class α ℝ ℝ]
  [is_scalar_tower α ℝ ℝ] [is_scalar_tower α ℝ E] {s : set E} {a : α} (ha : 0 ≤ a) :
  gauge (a • s) = a⁻¹ • gauge s :=
begin
  obtain rfl | ha' := ha.eq_or_lt,
  { rw [inv_zero, zero_smul, gauge_of_subset_zero (zero_smul_subset _)] },
  ext,
  rw [gauge_def', pi.smul_apply, gauge_def', ←real.Inf_smul_of_nonneg (inv_nonneg.2 ha)],
  congr' 1,
  ext r,
  simp_rw [set.mem_smul_set, set.mem_sep_eq],
  split,
  { rintro ⟨hr, y, hy, h⟩,
    simp_rw [mem_Ioi] at ⊢ hr,
    refine ⟨a • r, ⟨smul_pos ha' hr, _⟩, inv_smul_smul₀ ha'.ne' _⟩,
    rwa [smul_inv₀, smul_assoc, ←h, inv_smul_smul₀ ha'.ne'] },
  { rintro ⟨r, ⟨hr, hx⟩, rfl⟩,
    rw mem_Ioi at ⊢ hr,
    have := smul_pos ha' hr,
    refine ⟨smul_pos (inv_pos.2 ha') hr, r⁻¹ • x, hx, _⟩,
    rw [smul_inv₀, smul_assoc, inv_inv₀] }
end

lemma gauge_smul_left [module α E] [smul_comm_class α ℝ ℝ] [is_scalar_tower α ℝ ℝ]
  [is_scalar_tower α ℝ E] {s : set E} (symmetric : ∀ x ∈ s, -x ∈ s) (a : α) :
  gauge (a • s) = |a|⁻¹ • gauge s :=
begin
  rw ←gauge_smul_left_of_nonneg (abs_nonneg a),
  obtain h | h := abs_choice a,
  { rw h },
  { rw [h, set.neg_smul_set, ←set.smul_set_neg],
    congr,
    ext y,
    refine ⟨symmetric _, λ hy, _⟩,
    rw ←neg_neg y,
    exact symmetric _ hy },
  { apply_instance }
end

end linear_ordered_field

section topological_space
variables [topological_space E] [has_continuous_smul ℝ E]

lemma interior_subset_gauge_lt_one (s : set E) : interior s ⊆ {x | gauge s x < 1} :=
begin
  intros x hx,
  let f : ℝ → E := λ t, t • x,
  have hf : continuous f,
  { continuity },
  let s' := f ⁻¹' (interior s),
  have hs' : is_open s' := hf.is_open_preimage _ is_open_interior,
  have one_mem : (1 : ℝ) ∈ s',
  { simpa only [s', f, set.mem_preimage, one_smul] },
  obtain ⟨ε, hε₀, hε⟩ := (metric.nhds_basis_closed_ball.1 _).1
    (is_open_iff_mem_nhds.1 hs' 1 one_mem),
  rw real.closed_ball_eq_Icc at hε,
  have hε₁ : 0 < 1 + ε := hε₀.trans (lt_one_add ε),
  have : (1 + ε)⁻¹ < 1,
  { rw inv_lt_one_iff,
    right,
    linarith },
  refine (gauge_le_of_mem (inv_nonneg.2 hε₁.le) _).trans_lt this,
  rw mem_inv_smul_set_iff₀ hε₁.ne',
  exact interior_subset
    (hε ⟨(sub_le_self _ hε₀.le).trans ((le_add_iff_nonneg_right _).2 hε₀.le), le_rfl⟩),
end

lemma gauge_lt_one_eq_self_of_open (hs₁ : convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : is_open s) :
  {x | gauge s x < 1} = s :=
begin
  apply (gauge_lt_one_subset_self hs₁ ‹_› $ absorbent_nhds_zero $ hs₂.mem_nhds hs₀).antisymm,
  convert interior_subset_gauge_lt_one s,
  exact hs₂.interior_eq.symm,
end

lemma gauge_lt_one_of_mem_of_open (hs₁ : convex ℝ s) (hs₀ : (0 : E) ∈ s) (hs₂ : is_open s)
  {x : E} (hx : x ∈ s) :
  gauge s x < 1 :=
by rwa ←gauge_lt_one_eq_self_of_open hs₁ hs₀ hs₂ at hx

lemma gauge_lt_of_mem_smul (x : E) (ε : ℝ) (hε : 0 < ε) (hs₀ : (0 : E) ∈ s)
  (hs₁ : convex ℝ s) (hs₂ : is_open s) (hx : x ∈ ε • s) :
  gauge s x < ε :=
begin
  have : ε⁻¹ • x ∈ s,
  { rwa ←mem_smul_set_iff_inv_smul_mem₀ hε.ne' },
  have h_gauge_lt := gauge_lt_one_of_mem_of_open hs₁ hs₀ hs₂ this,
  rwa [gauge_smul_of_nonneg (inv_nonneg.2 hε.le), smul_eq_mul, inv_mul_lt_iff hε, mul_one]
    at h_gauge_lt,
  apply_instance
end

end topological_space

lemma gauge_add_le (hs : convex ℝ s) (absorbs : absorbent ℝ s) (x y : E) :
  gauge s (x + y) ≤ gauge s x + gauge s y :=
begin
  refine le_of_forall_pos_lt_add (λ ε hε, _),
  obtain ⟨a, ha, ha', hx⟩ := exists_lt_of_gauge_lt absorbs
    (lt_add_of_pos_right (gauge s x) (half_pos hε)),
  obtain ⟨b, hb, hb', hy⟩ := exists_lt_of_gauge_lt absorbs
    (lt_add_of_pos_right (gauge s y) (half_pos hε)),
  rw mem_smul_set_iff_inv_smul_mem₀ ha.ne' at hx,
  rw mem_smul_set_iff_inv_smul_mem₀ hb.ne' at hy,
  suffices : gauge s (x + y) ≤ a + b,
  { linarith },
  have hab : 0 < a + b := add_pos ha hb,
  apply gauge_le_of_mem hab.le,
  have := convex_iff_div.1 hs hx hy ha.le hb.le hab,
  rwa [smul_smul, smul_smul, mul_comm_div', mul_comm_div', ←mul_div_assoc, ←mul_div_assoc,
    mul_inv_cancel ha.ne', mul_inv_cancel hb.ne', ←smul_add, one_div,
    ←mem_smul_set_iff_inv_smul_mem₀ hab.ne'] at this,
end

/-- `gauge s` as a seminorm when `s` is symmetric, convex and absorbent. -/
@[simps] def gauge_seminorm (hs₀ : ∀ x ∈ s, -x ∈ s) (hs₁ : convex ℝ s) (hs₂ : absorbent ℝ s) :
  seminorm ℝ E :=
{ to_fun := gauge s,
  smul' := λ r x, by rw [gauge_smul hs₀, real.norm_eq_abs, smul_eq_mul]; apply_instance,
  triangle' := gauge_add_le hs₁ hs₂ }

section gauge_seminorm
variables {hs₀ : ∀ x ∈ s, -x ∈ s} {hs₁ : convex ℝ s} {hs₂ : absorbent ℝ s}

section topological_space
variables [topological_space E] [has_continuous_smul ℝ E]

lemma gauge_seminorm_lt_one_of_open (hs : is_open s) {x : E} (hx : x ∈ s) :
  gauge_seminorm hs₀ hs₁ hs₂ x < 1 :=
gauge_lt_one_of_mem_of_open hs₁ hs₂.zero_mem hs hx

end topological_space
end gauge_seminorm

/-- Any seminorm arises as the gauge of its unit ball. -/
@[simp] protected lemma seminorm.gauge_ball (p : seminorm ℝ E) : gauge (p.ball 0 1) = p :=
begin
  ext,
  obtain hp | hp := {r : ℝ | 0 < r ∧ x ∈ r • p.ball 0 1}.eq_empty_or_nonempty,
  { rw [gauge, hp, real.Inf_empty],
    by_contra,
    have hpx : 0 < p x := (p.nonneg x).lt_of_ne h,
    have hpx₂ : 0 < 2 * p x := mul_pos zero_lt_two hpx,
    refine hp.subset ⟨hpx₂, (2 * p x)⁻¹ • x, _, smul_inv_smul₀ hpx₂.ne' _⟩,
    rw [p.mem_ball_zero, p.smul, real.norm_eq_abs, abs_of_pos (inv_pos.2 hpx₂), inv_mul_lt_iff hpx₂,
      mul_one],
    exact lt_mul_of_one_lt_left hpx one_lt_two },
  refine is_glb.cInf_eq ⟨λ r, _, λ r hr, le_of_forall_pos_le_add $ λ ε hε, _⟩ hp,
  { rintro ⟨hr, y, hy, rfl⟩,
    rw p.mem_ball_zero at hy,
    rw [p.smul, real.norm_eq_abs, abs_of_pos hr],
    exact mul_le_of_le_one_right hr.le hy.le },
  { have hpε : 0 < p x + ε := add_pos_of_nonneg_of_pos (p.nonneg _) hε,
    refine hr ⟨hpε, (p x + ε)⁻¹ • x, _, smul_inv_smul₀ hpε.ne' _⟩,
    rw [p.mem_ball_zero, p.smul, real.norm_eq_abs, abs_of_pos (inv_pos.2 hpε), inv_mul_lt_iff hpε,
      mul_one],
    exact lt_add_of_pos_right _ hε }
end

lemma seminorm.gauge_seminorm_ball (p : seminorm ℝ E) :
  gauge_seminorm (λ x, p.symmetric_ball_zero 1) (p.convex_ball 0 1)
    (p.absorbent_ball_zero zero_lt_one) = p := fun_like.coe_injective p.gauge_ball

end add_comm_group

section norm
variables [semi_normed_group E] [normed_space ℝ E] {s : set E} {r : ℝ} {x : E}

lemma gauge_unit_ball (x : E) : gauge (metric.ball (0 : E) 1) x = ∥x∥ :=
begin
  obtain rfl | hx := eq_or_ne x 0,
  { rw [norm_zero, gauge_zero] },
  refine (le_of_forall_pos_le_add $ λ ε hε, _).antisymm _,
  { have := add_pos_of_nonneg_of_pos (norm_nonneg x) hε,
    refine gauge_le_of_mem this.le _,
    rw [smul_ball this.ne', smul_zero, real.norm_of_nonneg this.le, mul_one, mem_ball_zero_iff],
    exact lt_add_of_pos_right _ hε },
  refine le_gauge_of_not_mem balanced_ball_zero.star_convex
    (absorbent_ball_zero zero_lt_one).absorbs (λ h, _),
  obtain hx' | hx' := eq_or_ne (∥x∥) 0,
  { rw hx' at h,
    exact hx (zero_smul_subset _ h) },
  { rw [mem_smul_set_iff_inv_smul_mem₀ hx', mem_ball_zero_iff, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel hx'] at h,
    exact lt_irrefl _ h }
end

lemma smul_unit_ball {r : ℝ} (hr : 0 < r) : r • metric.ball (0 : E) 1 = metric.ball (0 : E) r :=
by rw [smul_ball hr.ne', smul_zero, mul_one, real.norm_of_nonneg hr.le]

lemma gauge_ball (hr : 0 < r) (x : E) : gauge (metric.ball (0 : E) r) x = ∥x∥ / r :=
begin
  rw [←smul_unit_ball hr, gauge_smul_left, pi.smul_apply, gauge_unit_ball, smul_eq_mul,
    abs_of_nonneg hr.le, div_eq_inv_mul],
  simp_rw [mem_ball_zero_iff, norm_neg],
  exact λ _, id,
end

lemma mul_gauge_le_norm (hs : metric.ball (0 : E) r ⊆ s) : r * gauge s x ≤ ∥x∥ :=
begin
  obtain hr | hr := le_or_lt r 0,
  { exact (mul_nonpos_of_nonpos_of_nonneg hr $ gauge_nonneg _).trans (norm_nonneg _) },
  rw [mul_comm, ←le_div_iff hr, ←gauge_ball hr],
  exact gauge_mono (absorbent_ball_zero hr) hs x,
end

end norm
end gauge

/-! ### Topology induced by a family of seminorms -/

namespace seminorm

section filter_basis

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E]

/-- A filter basis for the neighborhood filter of 0. -/
def seminorm_basis_zero (p : ι → seminorm 𝕜 E) : set (set E) :=
⋃ (s : finset ι) r (hr : 0 < r), singleton $ ball (s.sup p) (0 : E) r

lemma seminorm_basis_zero_iff (p : ι → seminorm 𝕜 E) (U : set E) :
  U ∈ seminorm_basis_zero p ↔ ∃ (i : finset ι) r (hr : 0 < r), U = ball (i.sup p) 0 r :=
by simp only [seminorm_basis_zero, mem_Union, mem_singleton_iff]

lemma seminorm_basis_zero_mem (p : ι → seminorm 𝕜 E) (i : finset ι) {r : ℝ} (hr : 0 < r) :
  (i.sup p).ball 0 r ∈ seminorm_basis_zero p :=
(seminorm_basis_zero_iff _ _).mpr ⟨i,_,hr,rfl⟩

lemma seminorm_basis_zero_singleton_mem (p : ι → seminorm 𝕜 E) (i : ι) {r : ℝ} (hr : 0 < r) :
  (p i).ball 0 r ∈ seminorm_basis_zero p :=
(seminorm_basis_zero_iff _ _).mpr ⟨{i},_,hr, by rw finset.sup_singleton⟩

lemma seminorm_basis_zero_nonempty (p : ι → seminorm 𝕜 E) [nonempty ι] :
  (seminorm_basis_zero p).nonempty :=
begin
  let i := classical.arbitrary ι,
  refine set.nonempty_def.mpr ⟨ball (p i) 0 1, _⟩,
  exact seminorm_basis_zero_singleton_mem _ i zero_lt_one,
end

lemma seminorm_basis_zero_intersect (p : ι → seminorm 𝕜 E)
  (U V : set E) (hU : U ∈ seminorm_basis_zero p) (hV : V ∈ seminorm_basis_zero p) :
  ∃ (z : set E) (H : z ∈ (seminorm_basis_zero p)), z ⊆ U ∩ V :=
begin
  classical,
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨s, r₁, hr₁, hU⟩,
  rcases (seminorm_basis_zero_iff p V).mp hV with ⟨t, r₂, hr₂, hV⟩,
  use ((s ∪ t).sup p).ball 0 (min r₁ r₂),
  refine ⟨seminorm_basis_zero_mem p (s ∪ t) (lt_min_iff.mpr ⟨hr₁, hr₂⟩), _⟩,
  rw [hU, hV, ball_finset_sup_eq_Inter _ _ _ (lt_min_iff.mpr ⟨hr₁, hr₂⟩),
    ball_finset_sup_eq_Inter _ _ _ hr₁, ball_finset_sup_eq_Inter _ _ _ hr₂],
  exact set.subset_inter
    (set.Inter₂_mono' $ λ i hi, ⟨i, finset.subset_union_left _ _ hi, ball_mono $ min_le_left _ _⟩)
    (set.Inter₂_mono' $ λ i hi, ⟨i, finset.subset_union_right _ _ hi, ball_mono $
    min_le_right _ _⟩),
end

lemma seminorm_basis_zero_zero (p : ι → seminorm 𝕜 E) (U) (hU : U ∈ seminorm_basis_zero p) :
  (0 : E) ∈ U :=
begin
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨ι', r, hr, hU⟩,
  rw [hU, mem_ball_zero, (ι'.sup p).zero],
  exact hr,
end

lemma seminorm_basis_zero_add (p : ι → seminorm 𝕜 E) (U) (hU : U ∈ seminorm_basis_zero p) :
  ∃ (V : set E) (H : V ∈ (seminorm_basis_zero p)), V + V ⊆ U :=
begin
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩,
  use (s.sup p).ball 0 (r/2),
  refine ⟨seminorm_basis_zero_mem p s (div_pos hr zero_lt_two), _⟩,
  refine set.subset.trans (ball_add_ball_subset (s.sup p) (r/2) (r/2) 0 0) _,
  rw [hU, add_zero, add_halves'],
end

lemma seminorm_basis_zero_neg (p : ι → seminorm 𝕜 E) (U) (hU' : U ∈ seminorm_basis_zero p) :
  ∃ (V : set E) (H : V ∈ (seminorm_basis_zero p)), V ⊆ (λ (x : E), -x) ⁻¹' U :=
begin
  rcases (seminorm_basis_zero_iff p U).mp hU' with ⟨s, r, hr, hU⟩,
  rw [hU, neg_preimage, neg_ball (s.sup p), neg_zero],
  exact ⟨U, hU', eq.subset hU⟩,
end

/-- The `add_group_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
def seminorm_add_group_filter_basis [nonempty ι]
  (p : ι → seminorm 𝕜 E) : add_group_filter_basis E :=
add_group_filter_basis_of_comm (seminorm_basis_zero p)
  (seminorm_basis_zero_nonempty p)
  (seminorm_basis_zero_intersect p)
  (seminorm_basis_zero_zero p)
  (seminorm_basis_zero_add p)
  (seminorm_basis_zero_neg p)

lemma seminorm_basis_zero_smul_right (p : ι → seminorm 𝕜 E) (v : E) (U : set E)
  (hU : U ∈ seminorm_basis_zero p) : ∀ᶠ (x : 𝕜) in 𝓝 0, x • v ∈ U :=
begin
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩,
  rw [hU, filter.eventually_iff],
  simp_rw [(s.sup p).mem_ball_zero, (s.sup p).smul],
  by_cases h : 0 < (s.sup p) v,
  { simp_rw (lt_div_iff h).symm,
    rw ←_root_.ball_zero_eq,
    exact metric.ball_mem_nhds 0 (div_pos hr h) },
  simp_rw [le_antisymm (not_lt.mp h) ((s.sup p).nonneg v), mul_zero, hr],
  exact is_open.mem_nhds is_open_univ (mem_univ 0),
end

variables [nonempty ι]

lemma seminorm_basis_zero_smul (p : ι → seminorm 𝕜 E) (U) (hU : U ∈ seminorm_basis_zero p) :
  ∃ (V : set 𝕜) (H : V ∈ 𝓝 (0 : 𝕜)) (W : set E)
  (H : W ∈ (seminorm_add_group_filter_basis p).sets), V • W ⊆ U :=
begin
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩,
  refine ⟨metric.ball 0 r.sqrt, metric.ball_mem_nhds 0 (real.sqrt_pos.mpr hr), _⟩,
  refine ⟨(s.sup p).ball 0 r.sqrt, seminorm_basis_zero_mem p s (real.sqrt_pos.mpr hr), _⟩,
  refine set.subset.trans (ball_smul_ball (s.sup p) r.sqrt r.sqrt) _,
  rw [hU, real.mul_self_sqrt (le_of_lt hr)],
end

lemma seminorm_basis_zero_smul_left (p : ι → seminorm 𝕜 E) (x : 𝕜) (U : set E)
  (hU : U ∈ seminorm_basis_zero p) : ∃ (V : set E)
  (H : V ∈ (seminorm_add_group_filter_basis p).sets), V ⊆ (λ (y : E), x • y) ⁻¹' U :=
begin
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩,
  rw hU,
  by_cases h : x ≠ 0,
  { rw [(s.sup p).smul_ball_preimage 0 r x h, smul_zero],
    use (s.sup p).ball 0 (r / ∥x∥),
    exact ⟨seminorm_basis_zero_mem p s (div_pos hr (norm_pos_iff.mpr h)), subset.rfl⟩ },
  refine ⟨(s.sup p).ball 0 r, seminorm_basis_zero_mem p s hr, _⟩,
  simp only [not_ne_iff.mp h, subset_def, mem_ball_zero, hr, mem_univ, seminorm.zero,
    implies_true_iff, preimage_const_of_mem, zero_smul],
end

/-- The `module_filter_basis` induced by the filter basis `seminorm_basis_zero`. -/
def seminorm_module_filter_basis (p : ι → seminorm 𝕜 E) : module_filter_basis 𝕜 E :=
{ to_add_group_filter_basis := seminorm_add_group_filter_basis p,
  smul' := seminorm_basis_zero_smul p,
  smul_left' := seminorm_basis_zero_smul_left p,
  smul_right' := seminorm_basis_zero_smul_right p }

end filter_basis

section bounded

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]

/-- The proposition that a linear map is bounded between spaces with families of seminorms. -/
def is_bounded (p : ι → seminorm 𝕜 E) (q : ι' → seminorm 𝕜 F) (f : E →ₗ[𝕜] F) : Prop :=
  ∀ i, ∃ s : finset ι, ∃ C : ℝ≥0, C ≠ 0 ∧ (q i).comp f ≤ C • s.sup p

lemma is_bounded_const (ι' : Type*) [nonempty ι']
  {p : ι → seminorm 𝕜 E} {q : seminorm 𝕜 F} (f : E →ₗ[𝕜] F) :
  is_bounded p (λ _ : ι', q) f ↔ ∃ (s : finset ι) C : ℝ≥0, C ≠ 0 ∧ q.comp f ≤ C • s.sup p :=
by simp only [is_bounded, forall_const]

lemma const_is_bounded (ι : Type*) [nonempty ι]
  {p : seminorm 𝕜 E} {q : ι' → seminorm 𝕜 F} (f : E →ₗ[𝕜] F) :
  is_bounded (λ _ : ι, p) q f ↔ ∀ i, ∃ C : ℝ≥0, C ≠ 0 ∧ (q i).comp f ≤ C • p :=
begin
  dunfold is_bounded,
  split,
  { intros h i,
    rcases h i with ⟨s, C, hC, h⟩,
    exact ⟨C, hC, le_trans h (smul_le_smul (finset.sup_le (λ _ _, le_rfl)) le_rfl)⟩ },
  intros h i,
  use [{classical.arbitrary ι}],
  simp only [h, finset.sup_singleton],
end

lemma is_bounded_sup {p : ι → seminorm 𝕜 E} {q : ι' → seminorm 𝕜 F}
  {f : E →ₗ[𝕜] F} (hf : is_bounded p q f) (s' : finset ι') :
  ∃ (C : ℝ≥0) (s : finset ι), 0 < C ∧ (s'.sup q).comp f ≤ C • (s.sup p) :=
begin
  classical,
  by_cases hs' : ¬s'.nonempty,
  { refine ⟨1, ∅, zero_lt_one, _⟩,
    rw [finset.not_nonempty_iff_eq_empty.mp hs', finset.sup_empty, bot_eq_zero, zero_comp],
    exact seminorm.nonneg _ },
  rw not_not at hs',
  choose fₛ fC hf using hf,
  use [s'.card • s'.sup fC, finset.bUnion s' fₛ],
  split,
  { refine nsmul_pos _ (ne_of_gt (finset.nonempty.card_pos hs')),
    cases finset.nonempty.bex hs' with j hj,
    exact lt_of_lt_of_le (zero_lt_iff.mpr (and.elim_left (hf j))) (finset.le_sup hj) },
  have hs : ∀ i : ι', i ∈ s' → (q i).comp f ≤ s'.sup fC • ((finset.bUnion s' fₛ).sup p) :=
  begin
    intros i hi,
    refine le_trans (and.elim_right (hf i)) (smul_le_smul _ (finset.le_sup hi)),
    exact finset.sup_mono (finset.subset_bUnion_of_mem fₛ hi),
  end,
  refine le_trans (comp_mono f (finset_sup_le_sum q s')) _,
  simp_rw [←pullback_apply, add_monoid_hom.map_sum, pullback_apply], --improve this
  refine le_trans (finset.sum_le_sum hs) _,
  rw [finset.sum_const, smul_assoc],
  exact le_rfl,
end

end bounded

section topology

variables [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] [add_comm_group F] [module 𝕜 F]
variables [nonempty ι] [nonempty ι']

/-- The proposition that the topology of `E` is induced by a family of seminorms `p`. -/
class with_seminorms (p : ι → seminorm 𝕜 E) [t : topological_space E] : Prop :=
(topology_eq_with_seminorms : t = (seminorm_module_filter_basis p).topology)

lemma with_seminorms_eq (p : ι → seminorm 𝕜 E) [t : topological_space E] [with_seminorms p] :
  t = ((seminorm_module_filter_basis p).topology) := with_seminorms.topology_eq_with_seminorms

/-- The topology of a `normed_space 𝕜 E` is induced by the seminorm `norm_seminorm 𝕜 E`. -/
instance norm_with_seminorms (𝕜 E) [normed_field 𝕜] [semi_normed_group E] [normed_space 𝕜 E] :
  with_seminorms (λ (_ : fin 1), norm_seminorm 𝕜 E) :=
begin
  let p := λ _ : fin 1, norm_seminorm 𝕜 E,
  refine ⟨topological_add_group.ext normed_top_group
    ((seminorm_add_group_filter_basis _).is_topological_add_group) _⟩,
  refine filter.has_basis.eq_of_same_basis metric.nhds_basis_ball _,
  rw ←ball_norm_seminorm 𝕜 E,
  refine filter.has_basis.to_has_basis (seminorm_add_group_filter_basis p).nhds_zero_has_basis _
    (λ r hr, ⟨(norm_seminorm 𝕜 E).ball 0 r, seminorm_basis_zero_singleton_mem p 0 hr, rfl.subset⟩),
  rintros U (hU : U ∈ seminorm_basis_zero p),
  rcases (seminorm_basis_zero_iff p U).mp hU with ⟨s, r, hr, hU⟩,
  use [r, hr],
  rw [hU, id.def],
  by_cases h : s.nonempty,
  { rw finset.sup_const h },
  rw [finset.not_nonempty_iff_eq_empty.mp h, finset.sup_empty, ball_bot _ hr],
  exact set.subset_univ _,
end

lemma continuous_from_bounded (p : ι → seminorm 𝕜 E) (q : ι' → seminorm 𝕜 F)
  [uniform_space E] [uniform_add_group E] [with_seminorms p]
  [uniform_space F] [uniform_add_group F] [with_seminorms q]
  (f : E →ₗ[𝕜] F) (hf : is_bounded p q f) : continuous f :=
begin
  refine uniform_continuous.continuous _,
  refine add_monoid_hom.uniform_continuous_of_continuous_at_zero f.to_add_monoid_hom _,
  rw [f.to_add_monoid_hom_coe, continuous_at_def, f.map_zero, with_seminorms_eq p],
  intros U hU,
  rw [with_seminorms_eq q, add_group_filter_basis.nhds_zero_eq, filter_basis.mem_filter_iff] at hU,
  rcases hU with ⟨V, hV : V ∈ seminorm_basis_zero q, hU⟩,
  rcases (seminorm_basis_zero_iff q V).mp hV with ⟨s₂, r, hr, hV⟩,
  rw hV at hU,
  rw [(seminorm_add_group_filter_basis p).nhds_zero_eq, filter_basis.mem_filter_iff],
  rcases (is_bounded_sup hf s₂) with ⟨C, s₁, hC, hf⟩,
  refine ⟨(s₁.sup p).ball 0 (r/C),
    seminorm_basis_zero_mem p _ (div_pos hr (nnreal.coe_pos.mpr hC)), _⟩,
  refine subset.trans _ (preimage_mono hU),
  simp_rw [←linear_map.map_zero f, ←ball_comp],
  refine subset.trans _ (ball_antitone hf),
  rw ball_smul (s₁.sup p) hC,
end

lemma cont_with_seminorms_normed_space (F) [semi_normed_group F] [normed_space 𝕜 F]
  [uniform_space E] [uniform_add_group E]
  (p : ι → seminorm 𝕜 E) [with_seminorms p] (f : E →ₗ[𝕜] F)
  (hf : ∃ (s : finset ι) C : ℝ≥0, C ≠ 0 ∧ (norm_seminorm 𝕜 F).comp f ≤ C • s.sup p) :
  continuous f :=
begin
  rw ←is_bounded_const (fin 1) at hf,
  exact continuous_from_bounded p (λ _ : fin 1, norm_seminorm 𝕜 F) f hf,
end

lemma cont_normed_space_to_with_seminorms (E) [semi_normed_group E] [normed_space 𝕜 E]
  [uniform_space F] [uniform_add_group F]
  (q : ι → seminorm 𝕜 F) [with_seminorms q] (f : E →ₗ[𝕜] F)
  (hf : ∀ i : ι, ∃ C : ℝ≥0, C ≠ 0 ∧ (q i).comp f ≤ C • (norm_seminorm 𝕜 E)) : continuous f :=
begin
  rw ←const_is_bounded (fin 1) at hf,
  exact continuous_from_bounded (λ _ : fin 1, norm_seminorm 𝕜 E) q f hf,
end

end topology

end seminorm



-- TODO: local convexity.
