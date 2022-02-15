/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Floris van Doorn
-/
import category_theory.limits.shapes.finite_products
import category_theory.discrete_category

/-!
# Limits in `C` give colimits in `Cᵒᵖ`.

We also give special cases for (co)products,
but not yet for pullbacks / pushouts or for (co)equalizers.

-/

universes v u

noncomputable theory

open category_theory
open category_theory.functor
open opposite

namespace category_theory.limits

variables {C : Type u} [category.{v} C]
variables {J : Type v} [small_category J]
variable (F : J ⥤ Cᵒᵖ)

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a colimit, we can construct a limit for `F : J ⥤ Cᵒᵖ`.
-/
lemma has_limit_of_has_colimit_left_op [has_colimit F.left_op] : has_limit F :=
has_limit.mk
{ cone := cone_of_cocone_left_op (colimit.cocone F.left_op),
  is_limit :=
  { lift := λ s, (colimit.desc F.left_op (cocone_left_op_of_cone s)).op,
    fac' := λ s j,
    begin
      rw [cone_of_cocone_left_op_π_app, colimit.cocone_ι, ←op_comp,
          colimit.ι_desc, cocone_left_op_of_cone_ι_app, quiver.hom.op_unop],
      refl, end,
    uniq' := λ s m w,
    begin
      -- It's a pity we can't do this automatically.
      -- Usually something like this would work by limit.hom_ext,
      -- but the opposites get in the way of this firing.
      have u := (colimit.is_colimit F.left_op).uniq (cocone_left_op_of_cone s) (m.unop),
      convert congr_arg (λ f : _ ⟶ _, f.op) (u _), clear u,
      intro j,
      rw [cocone_left_op_of_cone_ι_app, colimit.cocone_ι],
      convert congr_arg (λ f : _ ⟶ _, f.unop) (w (unop j)), clear w,
      rw [cone_of_cocone_left_op_π_app, colimit.cocone_ι, quiver.hom.unop_op],
      refl,
    end } }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
lemma has_limits_of_shape_op_of_has_colimits_of_shape [has_colimits_of_shape Jᵒᵖ C] :
  has_limits_of_shape J Cᵒᵖ :=
{ has_limit := λ F, has_limit_of_has_colimit_left_op F }

local attribute [instance] has_limits_of_shape_op_of_has_colimits_of_shape

/--
If `C` has colimits, we can construct limits for `Cᵒᵖ`.
-/
lemma has_limits_op_of_has_colimits [has_colimits C] : has_limits Cᵒᵖ := ⟨infer_instance⟩

/--
If `F.left_op : Jᵒᵖ ⥤ C` has a limit, we can construct a colimit for `F : J ⥤ Cᵒᵖ`.
-/
lemma has_colimit_of_has_limit_left_op [has_limit F.left_op] : has_colimit F :=
has_colimit.mk
{ cocone := cocone_of_cone_left_op (limit.cone F.left_op),
  is_colimit :=
  { desc := λ s, (limit.lift F.left_op (cone_left_op_of_cocone s)).op,
    fac' := λ s j,
    begin
      rw [cocone_of_cone_left_op_ι_app, limit.cone_π, ←op_comp,
          limit.lift_π, cone_left_op_of_cocone_π_app, quiver.hom.op_unop],
      refl, end,
    uniq' := λ s m w,
    begin
      have u := (limit.is_limit F.left_op).uniq (cone_left_op_of_cocone s) (m.unop),
      convert congr_arg (λ f : _ ⟶ _, f.op) (u _), clear u,
      intro j,
      rw [cone_left_op_of_cocone_π_app, limit.cone_π],
      convert congr_arg (λ f : _ ⟶ _, f.unop) (w (unop j)), clear w,
      rw [cocone_of_cone_left_op_ι_app, limit.cone_π, quiver.hom.unop_op],
      refl,
    end } }

/--
If `C` has colimits of shape `Jᵒᵖ`, we can construct limits in `Cᵒᵖ` of shape `J`.
-/
lemma has_colimits_of_shape_op_of_has_limits_of_shape [has_limits_of_shape Jᵒᵖ C] :
  has_colimits_of_shape J Cᵒᵖ :=
{ has_colimit := λ F, has_colimit_of_has_limit_left_op F }

local attribute [instance] has_colimits_of_shape_op_of_has_limits_of_shape

/--
If `C` has limits, we can construct colimits for `Cᵒᵖ`.
-/
lemma has_colimits_op_of_has_limits [has_limits C] : has_colimits Cᵒᵖ := ⟨infer_instance⟩

variables (X : Type v)
/--
If `C` has products indexed by `X`, then `Cᵒᵖ` has coproducts indexed by `X`.
-/
lemma has_coproducts_opposite [has_products_of_shape X C] :
  has_coproducts_of_shape X Cᵒᵖ :=
begin
  haveI : has_limits_of_shape (discrete X)ᵒᵖ C :=
    has_limits_of_shape_of_equivalence (discrete.opposite X).symm,
  apply_instance
end

/--
If `C` has coproducts indexed by `X`, then `Cᵒᵖ` has products indexed by `X`.
-/
lemma has_products_opposite [has_coproducts_of_shape X C] :
  has_products_of_shape X Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape (discrete X)ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence (discrete.opposite X).symm,
  apply_instance
end

lemma has_finite_coproducts_opposite [has_finite_products C] :
  has_finite_coproducts Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, begin
    resetI,
    haveI : has_limits_of_shape (discrete J)ᵒᵖ C :=
      has_limits_of_shape_of_equivalence (discrete.opposite J).symm,
    apply_instance,
  end }

lemma has_finite_products_opposite [has_finite_coproducts C] :
  has_finite_products Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, begin
    resetI,
    haveI : has_colimits_of_shape (discrete J)ᵒᵖ C :=
      has_colimits_of_shape_of_equivalence (discrete.opposite J).symm,
    apply_instance,
  end }

lemma has_equalizers_opposite [has_coequalizers C] : has_equalizers Cᵒᵖ :=
begin
  haveI : has_colimits_of_shape walking_parallel_pair.{v}ᵒᵖ C :=
    has_colimits_of_shape_of_equivalence walking_parallel_pair_op_equiv.{v},
  apply_instance
end

lemma has_coequalizers_opposite [has_equalizers C] : has_coequalizers Cᵒᵖ :=
begin
  haveI : has_limits_of_shape walking_parallel_pair.{v}ᵒᵖ C :=
    has_limits_of_shape_of_equivalence walking_parallel_pair_op_equiv.{v},
  apply_instance
end

local attribute [instance] fin_category_opposite

lemma has_finite_colimits_opposite [has_finite_limits C] :
  has_finite_colimits Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, by { resetI, apply_instance, }, }

lemma has_finite_limits_opposite [has_finite_colimits C] :
  has_finite_limits Cᵒᵖ :=
{ out := λ J 𝒟 𝒥, by { resetI, apply_instance, }, }

end category_theory.limits
