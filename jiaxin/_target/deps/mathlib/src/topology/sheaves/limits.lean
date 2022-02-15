/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import topology.sheaves.sheaf_condition.sites
import category_theory.sites.limits
import category_theory.adjunction
import category_theory.limits.functor_category

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits

variables {C : Type u} [category.{v} C] {J : Type v} [small_category J]

namespace Top

instance [has_limits C] (X : Top) : has_limits (presheaf C X) :=
by { dsimp [presheaf], apply_instance, }

instance [has_colimits C] (X : Top) : has_colimits (presheaf C X) :=
by { dsimp [presheaf], apply_instance, }

instance [has_limits C] (X : Top) : creates_limits (sheaf.forget C X) :=
(@@creates_limits_of_nat_iso _ _
  (presheaf.Sheaf_spaces_equiv_sheaf_sites_inverse_forget C X))
  (@@category_theory.comp_creates_limits _ _ _ _ _ _
    Sheaf.category_theory.Sheaf_to_presheaf.category_theory.creates_limits.{u v v})

instance [has_limits C] (X : Top) : has_limits (sheaf C X) :=
has_limits_of_has_limits_creates_limits (sheaf.forget C X)

lemma is_sheaf_of_is_limit [has_limits C] {X : Top} (F : J ⥤ presheaf C X)
  (H : ∀ j, (F.obj j).is_sheaf) {c : cone F} (hc : is_limit c) : c.X.is_sheaf :=
begin
  let F' : J ⥤ sheaf C X := { obj := λ j, ⟨F.obj j, H j⟩, map := F.map },
  let e : F' ⋙ sheaf.forget C X ≅ F := nat_iso.of_components (λ _, iso.refl _) (by tidy),
  exact presheaf.is_sheaf_of_iso ((is_limit_of_preserves (sheaf.forget C X)
      (limit.is_limit F')).cone_points_iso_of_nat_iso hc e) (limit F').2
end

lemma limit_is_sheaf [has_limits C] {X : Top} (F : J ⥤ presheaf C X)
  (H : ∀ j, (F.obj j).is_sheaf) : (limit F).is_sheaf :=
is_sheaf_of_is_limit F H (limit.is_limit F)

end Top
