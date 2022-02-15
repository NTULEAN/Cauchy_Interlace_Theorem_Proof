/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/

import topology.category.CompHaus
import topology.connected
import topology.subset_properties
import topology.locally_constant.basic
import category_theory.adjunction.reflective
import category_theory.monad.limits
import category_theory.limits.constructions.epi_mono
import category_theory.Fintype

/-!
# The category of Profinite Types

We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. finite coproducts
2. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/

universe u

open category_theory

/-- The type of profinite topological spaces. -/
structure Profinite :=
(to_CompHaus : CompHaus)
[is_totally_disconnected : totally_disconnected_space to_CompHaus]

namespace Profinite

/--
Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type*) [topological_space X] [compact_space X] [t2_space X]
  [totally_disconnected_space X] : Profinite := ⟨⟨⟨X⟩⟩⟩

instance : inhabited Profinite := ⟨Profinite.of pempty⟩

instance category : category Profinite := induced_category.category to_CompHaus
instance concrete_category : concrete_category Profinite := induced_category.concrete_category _
instance has_forget₂ : has_forget₂ Profinite Top := induced_category.has_forget₂ _

instance : has_coe_to_sort Profinite Type* := ⟨λ X, X.to_CompHaus⟩
instance {X : Profinite} : totally_disconnected_space X := X.is_totally_disconnected

-- We check that we automatically infer that Profinite sets are compact and Hausdorff.
example {X : Profinite} : compact_space X := infer_instance
example {X : Profinite} : t2_space X := infer_instance

@[simp]
lemma coe_to_CompHaus {X : Profinite} : (X.to_CompHaus : Type*) = X :=
rfl

@[simp] lemma coe_id (X : Profinite) : (𝟙 X : X → X) = id := rfl

@[simp] lemma coe_comp {X Y Z : Profinite} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f := rfl

end Profinite

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps, derive [full, faithful]]
def Profinite_to_CompHaus : Profinite ⥤ CompHaus := induced_functor _

/-- The fully faithful embedding of `Profinite` in `Top`. This is definitionally the same as the
obvious composite. -/
@[simps, derive [full, faithful]]
def Profinite.to_Top : Profinite ⥤ Top := forget₂ _ _

@[simp] lemma Profinite.to_CompHaus_to_Top :
  Profinite_to_CompHaus ⋙ CompHaus_to_Top = Profinite.to_Top :=
rfl

section Profinite

/--
(Implementation) The object part of the connected_components functor from compact Hausdorff spaces
to Profinite spaces, given by quotienting a space by its connected components.
See: https://stacks.math.columbia.edu/tag/0900
-/
-- Without explicit universe annotations here, Lean introduces two universe variables and
-- unhelpfully defines a function `CompHaus.{max u₁ u₂} → Profinite.{max u₁ u₂}`.
def CompHaus.to_Profinite_obj (X : CompHaus.{u}) : Profinite.{u} :=
{ to_CompHaus :=
  { to_Top := Top.of (connected_components X),
    is_compact := quotient.compact_space,
    is_hausdorff := connected_components.t2 },
  is_totally_disconnected := connected_components.totally_disconnected_space }

/--
(Implementation) The bijection of homsets to establish the reflective adjunction of Profinite
spaces in compact Hausdorff spaces.
-/
def Profinite.to_CompHaus_equivalence (X : CompHaus.{u}) (Y : Profinite.{u}) :
  (CompHaus.to_Profinite_obj X ⟶ Y) ≃ (X ⟶ Profinite_to_CompHaus.obj Y) :=
{ to_fun := λ f, f.comp ⟨quotient.mk', continuous_quotient_mk⟩,
  inv_fun := λ g,
    { to_fun := continuous.connected_components_lift g.2,
      continuous_to_fun := continuous.connected_components_lift_continuous g.2},
  left_inv := λ f, continuous_map.ext $ connected_components.surjective_coe.forall.2 $ λ a, rfl,
  right_inv := λ f, continuous_map.ext $ λ x, rfl }

/--
The connected_components functor from compact Hausdorff spaces to profinite spaces,
left adjoint to the inclusion functor.
-/
def CompHaus.to_Profinite : CompHaus ⥤ Profinite :=
adjunction.left_adjoint_of_equiv Profinite.to_CompHaus_equivalence (λ _ _ _ _ _, rfl)

lemma CompHaus.to_Profinite_obj' (X : CompHaus) :
  ↥(CompHaus.to_Profinite.obj X) = connected_components X := rfl

/-- Finite types are given the discrete topology. -/
def Fintype.discrete_topology (A : Fintype) : topological_space A := ⊥

section discrete_topology

local attribute [instance] Fintype.discrete_topology

/-- The natural functor from `Fintype` to `Profinite`, endowing a finite type with the
discrete topology. -/
@[simps] def Fintype.to_Profinite : Fintype ⥤ Profinite :=
{ obj := λ A, Profinite.of A,
  map := λ _ _ f, ⟨f⟩ }

end discrete_topology

end Profinite

namespace Profinite

/-- An explicit limit cone for a functor `F : J ⥤ Profinite`, defined in terms of
`Top.limit_cone`. -/
def limit_cone {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.cone F :=
{ X :=
  { to_CompHaus := (CompHaus.limit_cone (F ⋙ Profinite_to_CompHaus)).X,
    is_totally_disconnected :=
    begin
      change totally_disconnected_space ↥{u : Π (j : J), (F.obj j) | _},
      exact subtype.totally_disconnected_space,
    end },
  π := { app := (CompHaus.limit_cone (F ⋙ Profinite_to_CompHaus)).π.app } }

/-- The limit cone `Profinite.limit_cone F` is indeed a limit cone. -/
def limit_cone_is_limit {J : Type u} [small_category J] (F : J ⥤ Profinite.{u}) :
  limits.is_limit (limit_cone F) :=
{ lift := λ S, (CompHaus.limit_cone_is_limit (F ⋙ Profinite_to_CompHaus)).lift
    (Profinite_to_CompHaus.map_cone S),
  uniq' := λ S m h,
    (CompHaus.limit_cone_is_limit _).uniq (Profinite_to_CompHaus.map_cone S) _ h }

/-- The adjunction between CompHaus.to_Profinite and Profinite.to_CompHaus -/
def to_Profinite_adj_to_CompHaus : CompHaus.to_Profinite ⊣ Profinite_to_CompHaus :=
adjunction.adjunction_of_equiv_left _ _

/-- The category of profinite sets is reflective in the category of compact hausdroff spaces -/
instance to_CompHaus.reflective : reflective Profinite_to_CompHaus :=
{ to_is_right_adjoint := ⟨CompHaus.to_Profinite, Profinite.to_Profinite_adj_to_CompHaus⟩ }

noncomputable
instance to_CompHaus.creates_limits : creates_limits Profinite_to_CompHaus :=
monadic_creates_limits _

noncomputable
instance to_Top.reflective : reflective Profinite.to_Top :=
reflective.comp Profinite_to_CompHaus CompHaus_to_Top

noncomputable
instance to_Top.creates_limits : creates_limits Profinite.to_Top :=
monadic_creates_limits _

instance has_limits : limits.has_limits Profinite :=
has_limits_of_has_limits_creates_limits Profinite.to_Top

instance has_colimits : limits.has_colimits Profinite :=
has_colimits_of_reflective Profinite_to_CompHaus

noncomputable
instance forget_preserves_limits : limits.preserves_limits (forget Profinite) :=
by apply limits.comp_preserves_limits Profinite.to_Top (forget Top)

variables {X Y : Profinite.{u}} (f : X ⟶ Y)

/-- Any morphism of profinite spaces is a closed map. -/
lemma is_closed_map : is_closed_map f :=
CompHaus.is_closed_map _

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
lemma is_iso_of_bijective (bij : function.bijective f) : is_iso f :=
begin
  haveI := CompHaus.is_iso_of_bijective (Profinite_to_CompHaus.map f) bij,
  exact is_iso_of_fully_faithful Profinite_to_CompHaus _
end

/-- Any continuous bijection of profinite spaces induces an isomorphism. -/
noncomputable def iso_of_bijective (bij : function.bijective f) : X ≅ Y :=
by letI := Profinite.is_iso_of_bijective f bij; exact as_iso f

instance forget_reflects_isomorphisms : reflects_isomorphisms (forget Profinite) :=
⟨by introsI A B f hf; exact Profinite.is_iso_of_bijective _ ((is_iso_iff_bijective f).mp hf)⟩

/-- Construct an isomorphism from a homeomorphism. -/
@[simps hom inv] def iso_of_homeo (f : X ≃ₜ Y) : X ≅ Y :=
{ hom := ⟨f, f.continuous⟩,
  inv := ⟨f.symm, f.symm.continuous⟩,
  hom_inv_id' := by { ext x, exact f.symm_apply_apply x },
  inv_hom_id' := by { ext x, exact f.apply_symm_apply x } }

/-- Construct a homeomorphism from an isomorphism. -/
@[simps] def homeo_of_iso (f : X ≅ Y) : X ≃ₜ Y :=
{ to_fun := f.hom,
  inv_fun := f.inv,
  left_inv := λ x, by { change (f.hom ≫ f.inv) x = x, rw [iso.hom_inv_id, coe_id, id.def] },
  right_inv := λ x, by { change (f.inv ≫ f.hom) x = x, rw [iso.inv_hom_id, coe_id, id.def] },
  continuous_to_fun := f.hom.continuous,
  continuous_inv_fun := f.inv.continuous }

/-- The equivalence between isomorphisms in `Profinite` and homeomorphisms
of topological spaces. -/
@[simps] def iso_equiv_homeo : (X ≅ Y) ≃ (X ≃ₜ Y) :=
{ to_fun := homeo_of_iso,
  inv_fun := iso_of_homeo,
  left_inv := λ f, by { ext, refl },
  right_inv := λ f, by { ext, refl } }

lemma epi_iff_surjective {X Y : Profinite.{u}} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  split,
  { contrapose!,
    rintros ⟨y, hy⟩ hf,
    let C := set.range f,
    have hC : is_closed C := (is_compact_range f.continuous).is_closed,
    let U := Cᶜ,
    have hU : is_open U := is_open_compl_iff.mpr hC,
    have hyU : y ∈ U,
    { refine set.mem_compl _, rintro ⟨y', hy'⟩, exact hy y' hy' },
    have hUy : U ∈ nhds y := hU.mem_nhds hyU,
    obtain ⟨V, hV, hyV, hVU⟩ := is_topological_basis_clopen.mem_nhds_iff.mp hUy,
    classical,
    letI : topological_space (ulift.{u} $ fin 2) := ⊥,
    let Z := of (ulift.{u} $ fin 2),
    let g : Y ⟶ Z := ⟨(locally_constant.of_clopen hV).map ulift.up, locally_constant.continuous _⟩,
    let h : Y ⟶ Z := ⟨λ _, ⟨1⟩, continuous_const⟩,
    have H : h = g,
    { rw ← cancel_epi f,
      ext x, dsimp [locally_constant.of_clopen],
      rw if_neg, { refl },
      refine mt (λ α, hVU α) _,
      simp only [set.mem_range_self, not_true, not_false_iff, set.mem_compl_eq], },
    apply_fun (λ e, (e y).down) at H,
    dsimp [locally_constant.of_clopen] at H,
    rw if_pos hyV at H,
    exact top_ne_bot H },
  { rw ← category_theory.epi_iff_surjective,
    apply faithful_reflects_epi (forget Profinite) },
end

lemma mono_iff_injective {X Y : Profinite.{u}} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  split,
  { intro h,
    haveI : limits.preserves_limits Profinite_to_CompHaus := infer_instance,
    haveI : mono (Profinite_to_CompHaus.map f) := infer_instance,
    rwa ← CompHaus.mono_iff_injective },
  { rw ← category_theory.mono_iff_injective,
    apply faithful_reflects_mono (forget Profinite) }
end

end Profinite
