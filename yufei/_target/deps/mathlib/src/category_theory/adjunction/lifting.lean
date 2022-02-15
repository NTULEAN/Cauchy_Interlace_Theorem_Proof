/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.equalizers
import category_theory.limits.shapes.reflexive
import category_theory.monad.adjunction
import category_theory.monad.coequalizer

/-!
# Adjoint lifting

This file gives two constructions for building left adjoints: the adjoint triangle theorem and the
adjoint lifting theorem.
The adjoint triangle theorem says that given a functor `U : B ⥤ C` with a left adjoint `F` such
that `ε_X : FUX ⟶ X` is a regular epi. Then for any category `A` with coequalizers of reflexive
pairs, a functor `R : A ⥤ B` has a left adjoint if (and only if) the composite `R ⋙ U` does.
Note that the condition on `U` regarding `ε_X` is automatically satisfied in the case when `U` is
a monadic functor, giving the corollary: `monadic_adjoint_triangle_lift`, i.e. if `U` is monadic,
`A` has reflexive coequalizers then `R : A ⥤ B` has a left adjoint provided `R ⋙ U` does.

The adjoint lifting theorem says that given a commutative square of functors (up to isomorphism):

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` and `V` are monadic and `A` has reflexive coequalizers, then if `R` has a left adjoint
then `Q` has a left adjoint.

## Implementation

It is more convenient to prove this theorem by assuming we are given the explicit adjunction rather
than just a functor known to be a right adjoint. In docstrings, we write `(η, ε)` for the unit
and counit of the adjunction `adj₁ : F ⊣ U` and `(ι, δ)` for the unit and counit of the adjunction
`adj₂ : F' ⊣ R ⋙ U`.

## TODO

Dualise to lift right adjoints through comonads (by reversing 1-cells) and dualise to lift right
adjoints through monads (by reversing 2-cells), and the combination.

## References
* https://ncatlab.org/nlab/show/adjoint+triangle+theorem
* https://ncatlab.org/nlab/show/adjoint+lifting+theorem
* Adjoint Lifting Theorems for Categories of Algebras (PT Johnstone, 1975)
* A unified approach to the lifting of adjoints (AJ Power, 1988)
-/

namespace category_theory

open category limits

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {A : Type u₁} {B : Type u₂} {C : Type u₃}
variables [category.{v₁} A] [category.{v₂} B] [category.{v₃} C]

-- Hide implementation details in this namespace
namespace lift_adjoint

variables {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A)
variables (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)

/--
To show that `ε_X` is a coequalizer for `(FUε_X, ε_FUX)`, it suffices to assume it's always a
coequalizer of something (i.e. a regular epi).
-/
def counit_coequalises [∀ (X : B), regular_epi (adj₁.counit.app X)] (X : B) :
  is_colimit (cofork.of_π (adj₁.counit.app X) (adj₁.counit_naturality _)) :=
cofork.is_colimit.mk' _ $ λ s,
begin
  refine ⟨(regular_epi.desc' (adj₁.counit.app X) s.π _).1, _, _⟩,
  { rw ← cancel_epi (adj₁.counit.app (regular_epi.W (adj₁.counit.app X))),
    rw ← adj₁.counit_naturality_assoc,
    dsimp only [functor.comp_obj],
    rw [← s.condition, ← F.map_comp_assoc, ← U.map_comp, regular_epi.w, U.map_comp,
        F.map_comp_assoc, s.condition, ← adj₁.counit_naturality_assoc] },
  { apply (regular_epi.desc' (adj₁.counit.app X) s.π _).2 },
  { intros m hm,
    rw ← cancel_epi (adj₁.counit.app X),
    apply hm.trans (regular_epi.desc' (adj₁.counit.app X) s.π _).2.symm }
end

include adj₁ adj₂

/--
(Implementation)
To construct the left adjoint, we use the coequalizer of `F' U ε_Y` with the composite

`F' U F U X ⟶ F' U F U R F U' X ⟶ F' U R F' U X ⟶ F' U X`

where the first morphism is `F' U F ι_UX`, the second is `F' U ε_RF'UX`, and the third is `δ_F'UX`.
We will show that this coequalizer exists and that it forms the object map for a left adjoint to
`R`.
-/
def other_map (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

/--
`(F'Uε_X, other_map X)` is a reflexive pair: in particular if `A` has reflexive coequalizers then
it has a coequalizer.
-/
instance (X : B) :
  is_reflexive_pair (F'.map (U.map (adj₁.counit.app X))) (other_map _ _ adj₁ adj₂ X) :=
is_reflexive_pair.mk'
  (F'.map (adj₁.unit.app (U.obj X)))
  (by {rw [← F'.map_comp, adj₁.right_triangle_components], apply F'.map_id })
  begin
    dsimp [other_map],
    rw [← F'.map_comp_assoc, U.map_comp, adj₁.unit_naturality_assoc, adj₁.right_triangle_components,
        comp_id, adj₂.left_triangle_components]
  end

variables [has_reflexive_coequalizers A]

/--
Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`other_map`.
-/
noncomputable def construct_left_adjoint_obj (Y : B) : A :=
coequalizer (F'.map (U.map (adj₁.counit.app Y))) (other_map _ _ adj₁ adj₂ Y)

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
@[simps {rhs_md := semireducible}]
noncomputable
def construct_left_adjoint_equiv [∀ (X : B), regular_epi (adj₁.counit.app X)] (Y : A) (X : B) :
  (construct_left_adjoint_obj _ _ adj₁ adj₂ X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
calc (construct_left_adjoint_obj _ _ adj₁ adj₂ X ⟶ Y)
        ≃ {f : F'.obj (U.obj X) ⟶ Y //
              F'.map (U.map (adj₁.counit.app X)) ≫ f = other_map _ _ adj₁ adj₂ _ ≫ f} :
                cofork.is_colimit.hom_iso (colimit.is_colimit _) _
  ... ≃ {g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g} :
            begin
              apply (adj₂.hom_equiv _ _).subtype_equiv _,
              intro f,
              rw [← (adj₂.hom_equiv _ _).injective.eq_iff, eq_comm, adj₂.hom_equiv_naturality_left,
                  other_map, assoc, adj₂.hom_equiv_naturality_left, ← adj₂.counit_naturality,
                  adj₂.hom_equiv_naturality_left, adj₂.hom_equiv_unit,
                  adj₂.right_triangle_components, comp_id, functor.comp_map, ← U.map_comp, assoc,
                  ← adj₁.counit_naturality, adj₂.hom_equiv_unit, adj₂.hom_equiv_unit, F.map_comp,
                  assoc],
              refl,
            end
  ... ≃ {z : F.obj (U.obj X) ⟶ R.obj Y // _} :
            begin
              apply (adj₁.hom_equiv _ _).symm.subtype_equiv,
              intro g,
              rw [← (adj₁.hom_equiv _ _).symm.injective.eq_iff, adj₁.hom_equiv_counit,
                  adj₁.hom_equiv_counit, adj₁.hom_equiv_counit, F.map_comp, assoc, U.map_comp,
                  F.map_comp, assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc],
              apply eq_comm,
            end
  ... ≃ (X ⟶ R.obj Y) : (cofork.is_colimit.hom_iso (counit_coequalises adj₁ X) _).symm

/-- Construct the left adjoint to `R`, with object map `construct_left_adjoint_obj`. -/
noncomputable def construct_left_adjoint [∀ (X : B), regular_epi (adj₁.counit.app X)] : B ⥤ A :=
begin
  refine adjunction.left_adjoint_of_equiv (λ X Y, construct_left_adjoint_equiv R _ adj₁ adj₂ Y X) _,
  intros X Y Y' g h,
  rw [construct_left_adjoint_equiv_apply, construct_left_adjoint_equiv_apply, function.comp_app,
      function.comp_app, equiv.trans_apply, equiv.trans_apply, equiv.trans_apply, equiv.trans_apply,
      equiv.symm_apply_eq, subtype.ext_iff, cofork.is_colimit.hom_iso_natural,
      equiv.apply_symm_apply, equiv.subtype_equiv_apply, equiv.subtype_equiv_apply,
      equiv.subtype_equiv_apply, equiv.subtype_equiv_apply, subtype.coe_mk, subtype.coe_mk,
      subtype.coe_mk, subtype.coe_mk, ← adj₁.hom_equiv_naturality_right_symm,
      cofork.is_colimit.hom_iso_natural, adj₂.hom_equiv_naturality_right, functor.comp_map],
end

end lift_adjoint

/--
The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that each counit
`ε_X : FUX ⟶ X` is a regular epimorphism. Then if a category `A` has coequalizers of reflexive
pairs, then a functor `R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
noncomputable def adjoint_triangle_lift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
  [Π (X : B), regular_epi (adj₁.counit.app X)]
  [has_reflexive_coequalizers A]
  [is_right_adjoint (R ⋙ U)] : is_right_adjoint R :=
{ left := lift_adjoint.construct_left_adjoint R _ adj₁ (adjunction.of_right_adjoint _),
  adj := adjunction.adjunction_of_equiv_left _ _ }

/--
If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjoint_triangle_lift` which is often more useful in practice.
-/
noncomputable def monadic_adjoint_triangle_lift (U : B ⥤ C) [monadic_right_adjoint U] {R : A ⥤ B}
  [has_reflexive_coequalizers A]
  [is_right_adjoint (R ⋙ U)] :
  is_right_adjoint R :=
begin
  let R' : A ⥤ _ := R ⋙ monad.comparison (adjunction.of_right_adjoint U),
  suffices : is_right_adjoint R',
  { let : is_right_adjoint (R' ⋙ (monad.comparison (adjunction.of_right_adjoint U)).inv),
    { resetI,
      apply_instance },
    { let : R' ⋙ (monad.comparison (adjunction.of_right_adjoint U)).inv ≅ R :=
        (iso_whisker_left R (monad.comparison _).as_equivalence.unit_iso.symm : _) ≪≫
          R.right_unitor,
      exactI adjunction.right_adjoint_of_nat_iso this } },
  let : is_right_adjoint (R' ⋙ monad.forget (adjunction.of_right_adjoint U).to_monad) :=
    adjunction.right_adjoint_of_nat_iso
      (iso_whisker_left R (monad.comparison_forget (adjunction.of_right_adjoint U)).symm : _),
  letI : Π X, regular_epi ((monad.adj (adjunction.of_right_adjoint U).to_monad).counit.app X),
  { intro X,
    simp only [monad.adj_counit],
    exact ⟨_, _, _, _, monad.beck_algebra_coequalizer X⟩ },
  exact adjoint_triangle_lift R' (monad.adj _),
end

variables {D : Type u₄}
variables [category.{v₄} D]

/--
Suppose we have a commutative square of functors

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` has a left adjoint such that
each component of the counit is a regular epi.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
noncomputable def adjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  (comm : U ⋙ R ≅ Q ⋙ V)
  [is_right_adjoint U] [is_right_adjoint V] [is_right_adjoint R]
  [∀ X, regular_epi ((adjunction.of_right_adjoint V).counit.app X)]
  [has_reflexive_coequalizers A] :
  is_right_adjoint Q :=
begin
  let := adjunction.right_adjoint_of_nat_iso comm,
  exactI adjoint_triangle_lift Q (adjunction.of_right_adjoint V),
end

/--
Suppose we have a commutative square of functors

      Q
    A → B
  U ↓   ↓ V
    C → D
      R

where `U` has a left adjoint, `A` has reflexive coequalizers and `V` is monadic.
Then `Q` has a left adjoint if `R` has a left adjoint.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
noncomputable def monadic_adjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  (comm : U ⋙ R ≅ Q ⋙ V)
  [is_right_adjoint U] [monadic_right_adjoint V] [is_right_adjoint R]
  [has_reflexive_coequalizers A] :
  is_right_adjoint Q :=
begin
  let := adjunction.right_adjoint_of_nat_iso comm,
  exactI monadic_adjoint_triangle_lift V,
end

end category_theory
