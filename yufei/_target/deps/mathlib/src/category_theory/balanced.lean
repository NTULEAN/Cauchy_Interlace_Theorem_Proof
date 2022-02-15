/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.isomorphism

/-!
# Balanced categories

A category is called balanced if any morphism that is both monic and epic is an isomorphism.

Balanced categories arise frequently. For example, categories in which every monomorphism
(or epimorphism) is strong are balanced. Examples of this are abelian categories and toposes, such
as the category of types.

## TODO

The opposite of a balanced category is again balanced.

-/

universes v u

namespace category_theory
variables {C : Type u} [category.{v} C]

section
variables (C)

/-- A category is called balanced if any morphism that is both monic and epic is an isomorphism. -/
class balanced : Prop :=
(is_iso_of_mono_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [mono f] [epi f], is_iso f)

end

lemma is_iso_of_mono_of_epi [balanced C] {X Y : C} (f : X ⟶ Y) [mono f] [epi f] : is_iso f :=
balanced.is_iso_of_mono_of_epi _

lemma is_iso_iff_mono_and_epi [balanced C] {X Y : C} (f : X ⟶ Y) : is_iso f ↔ mono f ∧ epi f :=
⟨λ _, by exactI ⟨infer_instance, infer_instance⟩, λ ⟨_, _⟩, by exactI is_iso_of_mono_of_epi _⟩

end category_theory
