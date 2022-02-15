/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import algebra.group.prod
import group_theory.group_action.defs

/-!
# Prod instances for additive and multiplicative actions

This file defines instances for binary product of additive and multiplicative actions and provides
scalar multiplication as a homomorphism from `α × β` to `β`.

## Main declarations

* `smul_mul_hom`/`smul_monoid_hom`: Scalar multiplication bundled as a multiplicative/monoid
  homomorphism.
-/

variables {M N P α β : Type*}

namespace prod

section

variables [has_scalar M α] [has_scalar M β] [has_scalar N α] [has_scalar N β] (a : M) (x : α × β)

@[to_additive prod.has_vadd] instance : has_scalar M (α × β) := ⟨λa p, (a • p.1, a • p.2)⟩

@[simp, to_additive] theorem smul_fst : (a • x).1 = a • x.1 := rfl
@[simp, to_additive] theorem smul_snd : (a • x).2 = a • x.2 := rfl
@[simp, to_additive] theorem smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) := rfl
@[to_additive] theorem smul_def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) := rfl

instance [has_scalar M N] [is_scalar_tower M N α] [is_scalar_tower M N β] :
  is_scalar_tower M N (α × β) :=
⟨λ x y z, mk.inj_iff.mpr ⟨smul_assoc _ _ _, smul_assoc _ _ _⟩⟩

@[to_additive] instance [smul_comm_class M N α] [smul_comm_class M N β] :
  smul_comm_class M N (α × β) :=
{ smul_comm := λ r s x, mk.inj_iff.mpr ⟨smul_comm _ _ _, smul_comm _ _ _⟩ }

instance [has_scalar Mᵐᵒᵖ α] [has_scalar Mᵐᵒᵖ β] [is_central_scalar M α] [is_central_scalar M β] :
  is_central_scalar M (α × β) :=
⟨λ r m, prod.ext (op_smul_eq_smul _ _) (op_smul_eq_smul _ _)⟩

@[to_additive has_faithful_vadd_left]
instance has_faithful_scalar_left [has_faithful_scalar M α] [nonempty β] :
  has_faithful_scalar M (α × β) :=
⟨λ x y h, let ⟨b⟩ := ‹nonempty β› in eq_of_smul_eq_smul $ λ a : α, by injection h (a, b)⟩

@[to_additive has_faithful_vadd_right]
instance has_faithful_scalar_right [nonempty α] [has_faithful_scalar M β] :
  has_faithful_scalar M (α × β) :=
⟨λ x y h, let ⟨a⟩ := ‹nonempty α› in eq_of_smul_eq_smul $ λ b : β, by injection h (a, b)⟩

end

@[to_additive]
instance smul_comm_class_both [monoid N] [monoid P] [has_scalar M N] [has_scalar M P]
  [smul_comm_class M N N] [smul_comm_class M P P] :
  smul_comm_class M (N × P) (N × P) :=
⟨λ c x y, by simp [smul_def, mul_def, mul_smul_comm]⟩

instance is_scalar_tower_both [monoid N] [monoid P] [has_scalar M N] [has_scalar M P]
  [is_scalar_tower M N N] [is_scalar_tower M P P] :
  is_scalar_tower M (N × P) (N × P) :=
⟨λ c x y, by simp [smul_def, mul_def, smul_mul_assoc]⟩

@[to_additive] instance {m : monoid M} [mul_action M α] [mul_action M β] : mul_action M (α × β) :=
{ mul_smul  := λ a₁ a₂ p, mk.inj_iff.mpr ⟨mul_smul _ _ _, mul_smul _ _ _⟩,
  one_smul  := λ ⟨b, c⟩, mk.inj_iff.mpr ⟨one_smul _ _, one_smul _ _⟩ }

instance {R M N : Type*} {r : monoid R} [add_monoid M] [add_monoid N]
  [distrib_mul_action R M] [distrib_mul_action R N] : distrib_mul_action R (M × N) :=
{ smul_add  := λ a p₁ p₂, mk.inj_iff.mpr ⟨smul_add _ _ _, smul_add _ _ _⟩,
  smul_zero := λ a, mk.inj_iff.mpr ⟨smul_zero _, smul_zero _⟩ }

instance {R M N : Type*} {r : monoid R} [monoid M] [monoid N]
  [mul_distrib_mul_action R M] [mul_distrib_mul_action R N] : mul_distrib_mul_action R (M × N) :=
{ smul_mul  := λ a p₁ p₂, mk.inj_iff.mpr ⟨smul_mul' _ _ _, smul_mul' _ _ _⟩,
  smul_one := λ a, mk.inj_iff.mpr ⟨smul_one _, smul_one _⟩ }

end prod

/-! ### Scalar multiplication as a homomorphism -/

section bundled_smul

/-- Scalar multiplication as a multiplicative homomorphism. -/
@[simps]
def smul_mul_hom [monoid α] [has_mul β] [mul_action α β] [is_scalar_tower α β β]
  [smul_comm_class α β β] :
  mul_hom (α × β) β :=
{ to_fun := λ a, a.1 • a.2,
  map_mul' := λ a b, (smul_mul_smul _ _ _ _).symm }

/-- Scalar multiplication as a monoid homomorphism. -/
@[simps]
def smul_monoid_hom [monoid α] [mul_one_class β] [mul_action α β] [is_scalar_tower α β β]
  [smul_comm_class α β β] :
  α × β →* β :=
{ map_one' := one_smul _ _,
  .. smul_mul_hom }

end bundled_smul
