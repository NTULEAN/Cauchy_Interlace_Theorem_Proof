/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.finsupp.basic

/-!
# The pointwise product on `finsupp`.

For the convolution product on `finsupp` when the domain has a binary operation,
see the type synonyms `add_monoid_algebra`
(which is in turn used to define `polynomial` and `mv_polynomial`)
and `monoid_algebra`.
-/

noncomputable theory

open finset

universes u₁ u₂ u₃ u₄ u₅
variables {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {ι : Type u₅}

namespace finsupp

/-! ### Declarations about the pointwise product on `finsupp`s -/

section
variables [mul_zero_class β]

/-- The product of `f g : α →₀ β` is the finitely supported function
  whose value at `a` is `f a * g a`. -/
instance : has_mul (α →₀ β) := ⟨zip_with (*) (mul_zero 0)⟩

@[simp] lemma mul_apply {g₁ g₂ : α →₀ β} {a : α} : (g₁ * g₂) a = g₁ a * g₂ a :=
rfl

lemma support_mul [decidable_eq α] {g₁ g₂ : α →₀ β} : (g₁ * g₂).support ⊆ g₁.support ∩ g₂.support :=
begin
  intros a h,
  simp only [mul_apply, mem_support_iff] at h,
  simp only [mem_support_iff, mem_inter, ne.def],
  rw ←not_or_distrib,
  intro w,
  apply h,
  cases w; { rw w, simp },
end

instance : mul_zero_class (α →₀ β) :=
{ zero      := 0,
  mul       := (*),
  mul_zero  := λ f, by { ext, simp only [mul_apply, zero_apply, mul_zero], },
  zero_mul  := λ f, by { ext, simp only [mul_apply, zero_apply, zero_mul], }, }

end

instance [semigroup_with_zero β] : semigroup_with_zero (α →₀ β) :=
{ mul       := (*),
  mul_assoc := λ f g h, by { ext, simp only [mul_apply, mul_assoc], },
  ..(infer_instance : mul_zero_class (α →₀ β)) }

instance [non_unital_non_assoc_semiring β] : non_unital_non_assoc_semiring (α →₀ β) :=
{ left_distrib := λ f g h, by { ext, simp only [mul_apply, add_apply, left_distrib] {proj := ff} },
  right_distrib := λ f g h,
    by { ext, simp only [mul_apply, add_apply, right_distrib] {proj := ff} },
  ..(infer_instance : mul_zero_class (α →₀ β)),
  ..(infer_instance : add_comm_monoid (α →₀ β)) }

instance [non_unital_semiring β] : non_unital_semiring (α →₀ β) :=
{ ..(infer_instance : semigroup (α →₀ β)),
  ..(infer_instance : non_unital_non_assoc_semiring (α →₀ β)) }

instance [non_unital_non_assoc_ring β] : non_unital_non_assoc_ring (α →₀ β) :=
{ left_distrib := λ f g h, by { ext, simp only [mul_apply, add_apply, left_distrib] {proj := ff} },
  right_distrib := λ f g h,
    by { ext, simp only [mul_apply, add_apply, right_distrib] {proj := ff} },
  ..(infer_instance : mul_zero_class (α →₀ β)),
  ..(infer_instance : add_comm_group (α →₀ β)) }

-- TODO can this be generalized in the direction of `pi.has_scalar'`
-- (i.e. dependent functions and finsupps)
-- TODO in theory this could be generalised, we only really need `smul_zero` for the definition
/-- The pointwise multiplicative action of functions on finitely supported functions -/
instance pointwise_module [semiring β] : module (α → β) (α →₀ β) :=
{ smul := λ f g, finsupp.of_support_finite (λ a, f a • g a) begin
    apply set.finite.subset g.finite_support,
    simp only [function.support_subset_iff, finsupp.mem_support_iff, ne.def,
      finsupp.fun_support_eq, finset.mem_coe],
    intros x hx h,
    apply hx,
    rw [h, smul_zero],
  end,
  one_smul := λ b,
    by { ext a, simp only [one_smul, pi.one_apply, finsupp.of_support_finite_coe], },
  mul_smul := λ x y b, by simp [finsupp.of_support_finite_coe, mul_smul],
  smul_add := λ r x y, finsupp.ext (λ a, by simpa only [smul_add, pi.add_apply, coe_add]),
  smul_zero := λ b, finsupp.ext (by simp [finsupp.of_support_finite_coe, smul_zero]),
  zero_smul := λ a, finsupp.ext (λ b, by simp [finsupp.of_support_finite_coe]),
  add_smul := λ r s x, finsupp.ext (λ b, by simp [finsupp.of_support_finite_coe, add_smul]) }

@[simp]
lemma coe_pointwise_module [semiring β] (f : α → β) (g : α →₀ β) :
  ⇑(f • g) = f • g := rfl

end finsupp
