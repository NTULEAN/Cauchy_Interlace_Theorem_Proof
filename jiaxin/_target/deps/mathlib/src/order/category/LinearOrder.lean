/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import order.category.PartialOrder

/-!
# Category of linear orders

This defines `LinearOrder`, the category of linear orders with monotone maps.
-/

open category_theory

universe u

/-- The category of linear orders. -/
def LinearOrder := bundled linear_order

namespace LinearOrder

instance : bundled_hom.parent_projection @linear_order.to_partial_order := ⟨⟩

attribute [derive [large_category, concrete_category]] LinearOrder

instance : has_coe_to_sort LinearOrder Type* := bundled.has_coe_to_sort

/-- Construct a bundled `LinearOrder` from the underlying type and typeclass. -/
def of (α : Type*) [linear_order α] : LinearOrder := bundled.of α

instance : inhabited LinearOrder := ⟨of punit⟩

instance (α : LinearOrder) : linear_order α := α.str

instance has_forget_to_PartialOrder : has_forget₂ LinearOrder PartialOrder :=
bundled_hom.forget₂ _ _

/-- Constructs an equivalence between linear orders from an order isomorphism between them. -/
@[simps] def iso.mk {α β : LinearOrder.{u}} (e : α ≃o β) : α ≅ β :=
{ hom := e,
  inv := e.symm,
  hom_inv_id' := by { ext, exact e.symm_apply_apply x },
  inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

/-- `order_dual` as a functor. -/
@[simps] def to_dual : LinearOrder ⥤ LinearOrder :=
{ obj := λ X, of (order_dual X), map := λ X Y, order_hom.dual }

/-- The equivalence between `PartialOrder` and itself induced by `order_dual` both ways. -/
@[simps functor inverse] def dual_equiv : LinearOrder ≌ LinearOrder :=
equivalence.mk to_dual to_dual
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, iso.mk $ order_iso.dual_dual X) $ λ X Y f, rfl)

end LinearOrder

lemma LinearOrder_dual_equiv_comp_forget_to_PartialOrder :
  LinearOrder.dual_equiv.functor ⋙ forget₂ LinearOrder PartialOrder
  = forget₂ LinearOrder PartialOrder ⋙ PartialOrder.dual_equiv.functor := rfl
