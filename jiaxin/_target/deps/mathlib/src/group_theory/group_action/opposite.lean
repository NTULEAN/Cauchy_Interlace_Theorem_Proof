/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.group.opposite
import group_theory.group_action.defs

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

This file defines the actions on the opposite type `has_scalar R Mᵐᵒᵖ`, and actions by the opposite
type, `has_scalar Rᵐᵒᵖ M`.

Note that `mul_opposite.has_scalar` is provided in an earlier file as it is needed to provide the
`add_monoid.nsmul` and `add_comm_group.gsmul` fields.
-/

variables (α : Type*)

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/

namespace mul_opposite

@[to_additive] instance (R : Type*) [monoid R] [mul_action R α] : mul_action R αᵐᵒᵖ :=
{ one_smul := λ x, unop_injective $ one_smul R (unop x),
  mul_smul := λ r₁ r₂ x, unop_injective $ mul_smul r₁ r₂ (unop x),
  .. mul_opposite.has_scalar α R }

instance (R : Type*) [monoid R] [add_monoid α] [distrib_mul_action R α] :
  distrib_mul_action R αᵐᵒᵖ :=
{ smul_add := λ r x₁ x₂, unop_injective $ smul_add r (unop x₁) (unop x₂),
  smul_zero := λ r, unop_injective $ smul_zero r,
  .. mul_opposite.mul_action α R }

instance (R : Type*) [monoid R] [monoid α] [mul_distrib_mul_action R α] :
  mul_distrib_mul_action R αᵐᵒᵖ :=
{ smul_mul := λ r x₁ x₂, unop_injective $ smul_mul' r (unop x₂) (unop x₁),
  smul_one := λ r, unop_injective $ smul_one r,
  .. mul_opposite.mul_action α R }

instance {M N} [has_scalar M N] [has_scalar M α] [has_scalar N α] [is_scalar_tower M N α] :
  is_scalar_tower M N αᵐᵒᵖ :=
⟨λ x y z, unop_injective $ smul_assoc _ _ _⟩

@[to_additive] instance {M N} [has_scalar M α] [has_scalar N α] [smul_comm_class M N α] :
  smul_comm_class M N αᵐᵒᵖ :=
⟨λ x y z, unop_injective $ smul_comm _ _ _⟩

instance (R : Type*) [has_scalar R α] [has_scalar Rᵐᵒᵖ α] [is_central_scalar R α] :
  is_central_scalar R αᵐᵒᵖ :=
⟨λ r m, unop_injective $ op_smul_eq_smul _ _⟩

lemma op_smul_eq_op_smul_op {R : Type*} [has_scalar R α] [has_scalar Rᵐᵒᵖ α] [is_central_scalar R α]
  (r : R) (a : α) : op (r • a) = op r • op a :=
(op_smul_eq_smul r (op a)).symm

lemma unop_smul_eq_unop_smul_unop {R : Type*} [has_scalar R α] [has_scalar Rᵐᵒᵖ α]
  [is_central_scalar R α] (r : Rᵐᵒᵖ) (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a :=
(unop_smul_eq_smul r (unop a)).symm

end mul_opposite

/-! ### Actions _by_ the opposite type (right actions)

In `has_mul.to_has_scalar` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `mul_opposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/

open mul_opposite

/-- Like `has_mul.to_has_scalar`, but multiplies on the right.

See also `monoid.to_opposite_mul_action` and `monoid_with_zero.to_opposite_mul_action_with_zero`. -/
@[to_additive] instance has_mul.to_has_opposite_scalar [has_mul α] : has_scalar αᵐᵒᵖ α :=
{ smul := λ c x, x * c.unop }

@[simp, to_additive] lemma op_smul_eq_mul [has_mul α] {a a' : α} : op a • a' = a' * a := rfl

/-- The right regular action of a group on itself is transitive. -/
@[to_additive] instance mul_action.opposite_regular.is_pretransitive {G : Type*} [group G] :
  mul_action.is_pretransitive Gᵐᵒᵖ G :=
⟨λ x y, ⟨op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩

@[to_additive] instance semigroup.opposite_smul_comm_class [semigroup α] :
  smul_comm_class αᵐᵒᵖ α α :=
{ smul_comm := λ x y z, (mul_assoc _ _ _) }

@[to_additive] instance semigroup.opposite_smul_comm_class' [semigroup α] :
  smul_comm_class α αᵐᵒᵖ α :=
smul_comm_class.symm _ _ _

instance comm_semigroup.is_central_scalar [comm_semigroup α] : is_central_scalar α α :=
⟨λ r m, mul_comm _ _⟩

/-- Like `monoid.to_mul_action`, but multiplies on the right. -/
@[to_additive] instance monoid.to_opposite_mul_action [monoid α] : mul_action αᵐᵒᵖ α :=
{ smul := (•),
  one_smul := mul_one,
  mul_smul := λ x y r, (mul_assoc _ _ _).symm }

instance is_scalar_tower.opposite_mid {M N} [monoid N] [has_scalar M N]
  [smul_comm_class M N N] :
  is_scalar_tower M Nᵐᵒᵖ N :=
⟨λ x y z, mul_smul_comm _ _ _⟩

instance smul_comm_class.opposite_mid {M N} [monoid N] [has_scalar M N]
  [is_scalar_tower M N N] :
  smul_comm_class M Nᵐᵒᵖ N :=
⟨λ x y z, by { induction y using mul_opposite.rec, simp [smul_mul_assoc] }⟩

-- The above instance does not create an unwanted diamond, the two paths to
-- `mul_action αᵐᵒᵖ αᵐᵒᵖ` are defeq.
example [monoid α] : monoid.to_mul_action αᵐᵒᵖ = mul_opposite.mul_action α αᵐᵒᵖ := rfl

/-- `monoid.to_opposite_mul_action` is faithful on cancellative monoids. -/
@[to_additive] instance left_cancel_monoid.to_has_faithful_opposite_scalar [left_cancel_monoid α] :
  has_faithful_scalar αᵐᵒᵖ α :=
⟨λ x y h, unop_injective $ mul_left_cancel (h 1)⟩

/-- `monoid.to_opposite_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance cancel_monoid_with_zero.to_has_faithful_opposite_scalar
  [cancel_monoid_with_zero α] [nontrivial α] : has_faithful_scalar αᵐᵒᵖ α :=
⟨λ x y h, unop_injective $ mul_left_cancel₀ one_ne_zero (h 1)⟩
