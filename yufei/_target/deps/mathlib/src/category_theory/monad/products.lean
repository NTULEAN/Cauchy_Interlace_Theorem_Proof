/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.over
import category_theory.monad.algebra
import category_theory.limits.shapes.binary_products

/-!
# Algebras for the coproduct monad

The functor `Y ↦ X ⨿ Y` forms a monad, whose category of monads is equivalent to the under category
of `X`. Similarly, `Y ↦ X ⨯ Y` forms a comonad, whose category of comonads is equivalent to the
over category of `X`.

## TODO

Show that `over.forget X : over X ⥤ C` is a comonadic left adjoint and `under.forget : under X ⥤ C`
is a monadic right adjoint.
-/

noncomputable theory

universes v u -- morphism levels before object levels. See note [category_theory universes].

namespace category_theory
open category limits

variables {C : Type u} [category.{v} C] (X : C)

section

open comonad
variable [has_binary_products C]

/-- `X ⨯ -` has a comonad structure. This is sometimes called the writer comonad. -/
@[simps]
def prod_comonad : comonad C :=
{ to_functor := prod.functor.obj X,
  ε' := { app := λ Y, limits.prod.snd },
  δ' := { app := λ Y, prod.lift limits.prod.fst (𝟙 _) } }

/--
The forward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def coalgebra_to_over :
  coalgebra (prod_comonad X) ⥤ over X :=
{ obj := λ A, over.mk (A.a ≫ limits.prod.fst),
  map := λ A₁ A₂ f, over.hom_mk f.f (by { rw [over.mk_hom, ← f.h_assoc], dsimp, simp }) }

/--
The backward direction of the equivalence from coalgebras for the product comonad to the over
category.
-/
@[simps]
def over_to_coalgebra :
  over X ⥤ coalgebra (prod_comonad X) :=
{ obj := λ f, { A := f.left, a := prod.lift f.hom (𝟙 _) },
  map := λ f₁ f₂ g, { f := g.left } }

/-- The equivalence from coalgebras for the product comonad to the over category. -/
@[simps]
def coalgebra_equiv_over :
  coalgebra (prod_comonad X) ≌ over X :=
{ functor := coalgebra_to_over X,
  inverse := over_to_coalgebra X,
  unit_iso := nat_iso.of_components
                (λ A, coalgebra.iso_mk (iso.refl _)
                        (prod.hom_ext (by { dsimp, simp }) (by { dsimp, simpa using A.counit })))
              (λ A₁ A₂ f, by { ext, simp }),
  counit_iso := nat_iso.of_components (λ f, over.iso_mk (iso.refl _)) (λ f g k, by tidy) }.

end

section

open _root_.monad
variable [has_binary_coproducts C]

/-- `X ⨿ -` has a monad structure. This is sometimes called the either monad. -/
@[simps]
def coprod_monad : monad C :=
{ to_functor := coprod.functor.obj X,
  η' := { app := λ Y, coprod.inr },
  μ' := { app := λ Y, coprod.desc coprod.inl (𝟙 _) } }

/--
The forward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def algebra_to_under :
  monad.algebra (coprod_monad X) ⥤ under X :=
{ obj := λ A, under.mk (coprod.inl ≫ A.a),
  map := λ A₁ A₂ f, under.hom_mk f.f (by { rw [under.mk_hom, assoc, ←f.h], dsimp, simp }) }

/--
The backward direction of the equivalence from algebras for the coproduct monad to the under
category.
-/
@[simps]
def under_to_algebra :
  under X ⥤ monad.algebra (coprod_monad X) :=
{ obj := λ f, { A := f.right, a := coprod.desc f.hom (𝟙 _) },
  map := λ f₁ f₂ g, { f := g.right } }

/--
The equivalence from algebras for the coproduct monad to the under category.
-/
@[simps]
def algebra_equiv_under :
  monad.algebra (coprod_monad X) ≌ under X :=
{ functor := algebra_to_under X,
  inverse := under_to_algebra X,
  unit_iso := nat_iso.of_components
                 (λ A, monad.algebra.iso_mk (iso.refl _)
                         (coprod.hom_ext (by tidy) (by { dsimp, simpa using A.unit.symm })))
                 (λ A₁ A₂ f, by { ext, simp }),
  counit_iso :=
    nat_iso.of_components (λ f, under.iso_mk (iso.refl _) (by tidy)) (λ f g k, by tidy) }.

end

end category_theory
