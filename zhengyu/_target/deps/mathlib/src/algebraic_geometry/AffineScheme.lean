/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.Gamma_Spec_adjunction
import algebraic_geometry.open_immersion
import category_theory.limits.opposites

/-!
# Affine schemes

We define the category of `AffineScheme`s as the essential image of `Spec`.
We also define predicates about affine schemes and affine open sets.

## Main definitions

* `algebraic_geometry.AffineScheme`: The category of affine schemes.
* `algebraic_geometry.is_affine`: A scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an
  isomorphism.
* `algebraic_geometry.Scheme.iso_Spec`: The canonical isomorphism `X ≅ Spec Γ(X)` for an affine
  scheme.
* `algebraic_geometry.AffineScheme.equiv_CommRing`: The equivalence of categories
  `AffineScheme ≌ CommRingᵒᵖ` given by `AffineScheme.Spec : CommRingᵒᵖ ⥤ AffineScheme` and
  `AffineScheme.Γ : AffineSchemeᵒᵖ ⥤ CommRing`.
* `algebraic_geometry.is_affine_open`: An open subset of a scheme is affine if the open subscheme is
  affine.
* `algebraic_geometry.is_affine_open.from_Spec`: The immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`.

-/

noncomputable theory

open category_theory category_theory.limits opposite topological_space

universe u

namespace algebraic_geometry

/-- The category of affine schemes -/
def AffineScheme := Scheme.Spec.ess_image

/-- A Scheme is affine if the canonical map `X ⟶ Spec Γ(X)` is an isomorphism. -/
class is_affine (X : Scheme) : Prop :=
(affine : is_iso (Γ_Spec.adjunction.unit.app X))

attribute [instance] is_affine.affine

/-- The canonical isomorphism `X ≅ Spec Γ(X)` for an affine scheme. -/
def Scheme.iso_Spec (X : Scheme) [is_affine X] :
  X ≅ Scheme.Spec.obj (op $ Scheme.Γ.obj $ op X) :=
as_iso (Γ_Spec.adjunction.unit.app X)

lemma mem_AffineScheme (X : Scheme) : X ∈ AffineScheme ↔ is_affine X :=
⟨λ h, ⟨functor.ess_image.unit_is_iso h⟩, λ h, @@mem_ess_image_of_unit_is_iso _ _ _ X h.1⟩

instance is_affine_AffineScheme (X : AffineScheme.{u}) : is_affine (X : Scheme.{u}) :=
(mem_AffineScheme _).mp X.prop

instance Spec_is_affine (R : CommRingᵒᵖ) : is_affine (Scheme.Spec.obj R) :=
(mem_AffineScheme _).mp (Scheme.Spec.obj_mem_ess_image R)

lemma is_affine_of_iso {X Y : Scheme} (f : X ⟶ Y) [is_iso f] [h : is_affine Y] :
  is_affine X :=
by { rw [← mem_AffineScheme] at h ⊢, exact functor.ess_image.of_iso (as_iso f).symm h }

namespace AffineScheme

/-- The `Spec` functor into the category of affine schemes. -/
@[derive [full, faithful, ess_surj], simps]
def Spec : CommRingᵒᵖ ⥤ AffineScheme := Scheme.Spec.to_ess_image

/-- The forgetful functor `AffineScheme ⥤ Scheme`. -/
@[derive [full, faithful], simps]
def forget_to_Scheme : AffineScheme ⥤ Scheme := Scheme.Spec.ess_image_inclusion

/-- The global section functor of an affine scheme. -/
def Γ : AffineSchemeᵒᵖ ⥤ CommRing := forget_to_Scheme.op ⋙ Scheme.Γ

/-- The category of affine schemes is equivalent to the category of commutative rings. -/
def equiv_CommRing : AffineScheme ≌ CommRingᵒᵖ :=
equiv_ess_image_of_reflective.symm

instance Γ_is_equiv : is_equivalence Γ.{u} :=
begin
  haveI : is_equivalence Γ.{u}.right_op.op := is_equivalence.of_equivalence equiv_CommRing.op,
  exact (functor.is_equivalence_trans Γ.{u}.right_op.op (op_op_equivalence _).functor : _),
end

instance : has_colimits AffineScheme.{u} :=
begin
  haveI := adjunction.has_limits_of_equivalence.{u} Γ.{u},
  haveI : has_colimits AffineScheme.{u} ᵒᵖᵒᵖ := has_colimits_op_of_has_limits,
  exactI adjunction.has_colimits_of_equivalence.{u} (op_op_equivalence AffineScheme.{u}).inverse
end

instance : has_limits AffineScheme.{u} :=
begin
  haveI := adjunction.has_colimits_of_equivalence Γ.{u},
  haveI : has_limits AffineScheme.{u} ᵒᵖᵒᵖ := limits.has_limits_op_of_has_colimits,
  exactI adjunction.has_limits_of_equivalence (op_op_equivalence AffineScheme.{u}).inverse
end

end AffineScheme

/-- An open subset of a scheme is affine if the open subscheme is affine. -/
def is_affine_open {X : Scheme} (U : opens X.carrier) : Prop :=
is_affine (X.restrict U.open_embedding)

lemma range_is_affine_open_of_open_immersion {X Y : Scheme} [is_affine X] (f : X ⟶ Y)
  [H : is_open_immersion f] : is_affine_open ⟨set.range f.1.base, H.base_open.open_range⟩ :=
begin
  refine is_affine_of_iso (is_open_immersion.iso_of_range_eq f (Y.of_restrict _) _).inv,
  exact subtype.range_coe.symm,
  apply_instance
end

lemma top_is_affine_open (X : Scheme) [is_affine X] : is_affine_open (⊤ : opens X.carrier) :=
begin
  convert range_is_affine_open_of_open_immersion (𝟙 X),
  ext1,
  exact set.range_id.symm
end

instance Scheme.affine_basis_cover_is_affine (X : Scheme) (i : X.affine_basis_cover.J) :
  is_affine (X.affine_basis_cover.obj i) :=
algebraic_geometry.Spec_is_affine _

lemma is_basis_affine_open (X : Scheme) :
  opens.is_basis { U : opens X.carrier | is_affine_open U } :=
begin
  rw opens.is_basis_iff_nbhd,
  rintros U x (hU : x ∈ (U : set X.carrier)),
  obtain ⟨S, hS, hxS, hSU⟩ := X.affine_basis_cover_is_basis.exists_subset_of_mem_open hU U.prop,
  refine ⟨⟨S, X.affine_basis_cover_is_basis.is_open hS⟩, _, hxS, hSU⟩,
  rcases hS with ⟨i, rfl⟩,
  exact range_is_affine_open_of_open_immersion _,
end

/-- The open immersion `Spec 𝒪ₓ(U) ⟶ X` for an affine `U`. -/
def is_affine_open.from_Spec {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  Scheme.Spec.obj (op $ X.presheaf.obj $ op U) ⟶ X :=
begin
  haveI : is_affine (X.restrict U.open_embedding) := hU,
  have : U.open_embedding.is_open_map.functor.obj ⊤ = U,
  { ext1, exact set.image_univ.trans subtype.range_coe },
  exact Scheme.Spec.map (X.presheaf.map (eq_to_hom this.symm).op).op ≫
    (X.restrict U.open_embedding).iso_Spec.inv ≫ X.of_restrict _
end

instance is_affine_open.is_open_immersion_from_Spec {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  is_open_immersion hU.from_Spec :=
by { delta is_affine_open.from_Spec, apply_instance }

lemma is_affine_open.from_Spec_range {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  set.range hU.from_Spec.1.base = (U : set X.carrier) :=
begin
  delta is_affine_open.from_Spec,
  erw [← category.assoc, Scheme.comp_val_base],
  rw [coe_comp, set.range_comp, set.range_iff_surjective.mpr, set.image_univ],
  exact subtype.range_coe,
  rw ← Top.epi_iff_surjective,
  apply_instance
end

lemma is_affine_open.from_Spec_image_top {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  hU.is_open_immersion_from_Spec.base_open.is_open_map.functor.obj ⊤ = U :=
by { ext1, exact set.image_univ.trans hU.from_Spec_range }

lemma is_affine_open.is_compact {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
  is_compact (U : set X.carrier) :=
begin
  convert @is_compact.image _ _ _ _ set.univ hU.from_Spec.1.base
    prime_spectrum.compact_space.1 (by continuity),
  convert hU.from_Spec_range.symm,
  exact set.image_univ
end

instance Scheme.quasi_compact_of_affine (X : Scheme) [is_affine X] : compact_space X.carrier :=
⟨(top_is_affine_open X).is_compact⟩

lemma is_affine_open.from_Spec_base_preimage
  {X : Scheme} {U : opens X.carrier} (hU : is_affine_open U) :
    (opens.map hU.from_Spec.val.base).obj U = ⊤ :=
begin
  ext1,
  change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
  rw [← hU.from_Spec_range, ← set.image_univ],
  exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj
end

lemma Scheme.Spec_map_presheaf_map_eq_to_hom {X : Scheme} {U V : opens X.carrier} (h : U = V) (W) :
  (Scheme.Spec.map (X.presheaf.map (eq_to_hom h).op).op).val.c.app W =
    eq_to_hom (by { cases h, dsimp, induction W using opposite.rec, congr, ext1, simpa }) :=
begin
  have : Scheme.Spec.map (X.presheaf.map (𝟙 (op U))).op = 𝟙 _,
  { rw [X.presheaf.map_id, op_id, Scheme.Spec.map_id]  },
  cases h,
  refine (Scheme.congr_app this _).trans _,
  erw category.id_comp,
  simpa
end

lemma is_affine_open.Spec_Γ_identity_hom_app_from_Spec {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  (Spec_Γ_identity.hom.app (X.presheaf.obj $ op U)) ≫ hU.from_Spec.1.c.app (op U) =
    (Scheme.Spec.obj _).presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
begin
  haveI : is_affine _ := hU,
  have e₁ :=
    Spec_Γ_identity.hom.naturality (X.presheaf.map (eq_to_hom U.open_embedding_obj_top).op),
  rw ← is_iso.comp_inv_eq at e₁,
  have e₂ := Γ_Spec.adjunction_unit_app_app_top (X.restrict U.open_embedding),
  erw ← e₂ at e₁,
  simp only [functor.id_map, quiver.hom.unop_op, functor.comp_map, ← functor.map_inv, ← op_inv,
    LocallyRingedSpace.Γ_map, category.assoc, functor.right_op_map, inv_eq_to_hom] at e₁,
  delta is_affine_open.from_Spec Scheme.iso_Spec,
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app, ← e₁],
  simp_rw category.assoc,
  erw ← X.presheaf.map_comp_assoc,
  rw ← op_comp,
  have e₃ : U.open_embedding.is_open_map.adjunction.counit.app U ≫
    eq_to_hom U.open_embedding_obj_top.symm =
    U.open_embedding.is_open_map.functor.map (eq_to_hom U.inclusion_map_eq_top) :=
    subsingleton.elim _ _,
  have e₄ : X.presheaf.map _ ≫ _ = _ :=
    (as_iso (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding)))
    .inv.1.c.naturality_assoc (eq_to_hom U.inclusion_map_eq_top).op _,
  erw [e₃, e₄, ← Scheme.comp_val_c_app_assoc, iso.inv_hom_id],
  simp only [eq_to_hom_map, eq_to_hom_op, Scheme.Spec_map_presheaf_map_eq_to_hom],
  erw [Scheme.Spec_map_presheaf_map_eq_to_hom, category.id_comp],
  simpa only [eq_to_hom_trans]
end

@[elementwise]
lemma is_affine_open.from_Spec_app_eq {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) :
  hU.from_Spec.1.c.app (op U) = Spec_Γ_identity.inv.app (X.presheaf.obj $ op U) ≫
    (Scheme.Spec.obj _).presheaf.map (eq_to_hom hU.from_Spec_base_preimage).op :=
by rw [← hU.Spec_Γ_identity_hom_app_from_Spec, iso.inv_hom_id_app_assoc]

lemma is_affine_open.basic_open_is_affine {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (f : X.presheaf.obj (op U)) : is_affine_open (X.basic_open f) :=
begin
  convert range_is_affine_open_of_open_immersion (Scheme.Spec.map (CommRing.of_hom
    (algebra_map (X.presheaf.obj (op U)) (localization.away f))).op ≫ hU.from_Spec),
  ext1,
  have : hU.from_Spec.val.base '' (hU.from_Spec.val.base ⁻¹' (X.basic_open f : set X.carrier)) =
    (X.basic_open f : set X.carrier),
  { rw [set.image_preimage_eq_inter_range, set.inter_eq_left_iff_subset, hU.from_Spec_range],
    exact Scheme.basic_open_subset _ _ },
  rw [subtype.coe_mk, Scheme.comp_val_base, ← this, coe_comp, set.range_comp],
  congr' 1,
  refine (congr_arg coe $ Scheme.preimage_basic_open hU.from_Spec f).trans _,
  refine eq.trans _ (prime_spectrum.localization_away_comap_range (localization.away f) f).symm,
  congr' 1,
  have : (opens.map hU.from_Spec.val.base).obj U = ⊤,
  { ext1,
    change hU.from_Spec.1.base ⁻¹' (U : set X.carrier) = set.univ,
    rw [← hU.from_Spec_range, ← set.image_univ],
    exact set.preimage_image_eq _ PresheafedSpace.is_open_immersion.base_open.inj },
  refine eq.trans _ (basic_open_eq_of_affine f),
  have lm : ∀ s, (opens.map hU.from_Spec.val.base).obj U ⊓ s = s := λ s, this.symm ▸ top_inf_eq,
  refine eq.trans _ (lm _),
  refine eq.trans _
    ((Scheme.Spec.obj $ op $ X.presheaf.obj $ op U).basic_open_res _ (eq_to_hom this).op),
  rw ← comp_apply,
  congr' 2,
  rw iso.eq_inv_comp,
  erw hU.Spec_Γ_identity_hom_app_from_Spec,
end

lemma Scheme.map_prime_spectrum_basic_open_of_affine (X : Scheme) [is_affine X]
  (f : Scheme.Γ.obj (op X)) :
  (opens.map X.iso_Spec.hom.1.base).obj (prime_spectrum.basic_open f) = X.basic_open f :=
begin
  rw ← basic_open_eq_of_affine,
  transitivity (opens.map X.iso_Spec.hom.1.base).obj ((Scheme.Spec.obj
    (op (Scheme.Γ.obj (op X)))).basic_open ((inv (X.iso_Spec.hom.1.c.app
      (op ((opens.map (inv X.iso_Spec.hom).val.base).obj ⊤)))) ((X.presheaf.map (eq_to_hom _)) f))),
  congr,
  { rw [← is_iso.inv_eq_inv, is_iso.inv_inv, is_iso.iso.inv_inv, nat_iso.app_hom],
    erw ← Γ_Spec.adjunction_unit_app_app_top,
    refl },
  { rw eq_to_hom_map, refl },
  { dsimp, congr },
  { refine (Scheme.preimage_basic_open _ _).trans _,
    rw [is_iso.inv_hom_id_apply, Scheme.basic_open_res_eq] }
end

lemma is_basis_basic_open (X : Scheme) [is_affine X] :
  opens.is_basis (set.range (X.basic_open : X.presheaf.obj (op ⊤) → opens X.carrier)) :=
begin
  delta opens.is_basis,
  convert prime_spectrum.is_basis_basic_opens.inducing
    (Top.homeo_of_iso (Scheme.forget_to_Top.map_iso X.iso_Spec)).inducing using 1,
  ext,
  simp only [set.mem_image, exists_exists_eq_and],
  split,
  { rintro ⟨_, ⟨x, rfl⟩, rfl⟩,
    refine ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, _⟩,
    exact congr_arg subtype.val (X.map_prime_spectrum_basic_open_of_affine x) },
  { rintro ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩,
    refine ⟨_, ⟨x, rfl⟩, _⟩,
    exact congr_arg subtype.val (X.map_prime_spectrum_basic_open_of_affine x).symm }
end

/-- The prime ideal of `𝒪ₓ(U)` corresponding to a point `x : U`. -/
noncomputable
def is_affine_open.prime_ideal_of {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (x : U) :
  prime_spectrum (X.presheaf.obj $ op U) :=
((Scheme.Spec.map (X.presheaf.map (eq_to_hom $
  show U.open_embedding.is_open_map.functor.obj ⊤ = U, from
    opens.ext (set.image_univ.trans subtype.range_coe)).op).op).1.base
  ((@@Scheme.iso_Spec (X.restrict U.open_embedding) hU).hom.1.base x))

lemma is_affine_open.from_Spec_prime_ideal_of {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (x : U) :
  hU.from_Spec.val.base (hU.prime_ideal_of x) = x.1 :=
begin
  dsimp only [is_affine_open.from_Spec, subtype.coe_mk],
  erw [← Scheme.comp_val_base_apply, ← Scheme.comp_val_base_apply],
  simpa only [← functor.map_comp_assoc, ← functor.map_comp, ← op_comp, eq_to_hom_trans, op_id,
    eq_to_hom_refl, category_theory.functor.map_id, category.id_comp, iso.hom_inv_id_assoc]
end

lemma is_affine_open.is_localization_stalk_aux {X : Scheme} (U : opens X.carrier)
  [is_affine (X.restrict U.open_embedding)] :
  (inv (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).1.c.app
    (op ((opens.map U.inclusion).obj U)) =
      X.presheaf.map (eq_to_hom $ by rw opens.inclusion_map_eq_top :
        U.open_embedding.is_open_map.functor.obj ⊤ ⟶
          (U.open_embedding.is_open_map.functor.obj ((opens.map U.inclusion).obj U))).op ≫
      to_Spec_Γ (X.presheaf.obj $ op (U.open_embedding.is_open_map.functor.obj ⊤)) ≫
      (Scheme.Spec.obj $ op $ X.presheaf.obj $ _).presheaf.map
        (eq_to_hom (by { rw [opens.inclusion_map_eq_top], refl }) : unop _ ⟶ ⊤).op :=
begin
  have e : (opens.map (inv (Γ_Spec.adjunction.unit.app (X.restrict U.open_embedding))).1.base).obj
    ((opens.map U.inclusion).obj U) = ⊤,
  by { rw [opens.inclusion_map_eq_top], refl },
  rw [Scheme.inv_val_c_app, is_iso.comp_inv_eq, Scheme.app_eq _ e,
    Γ_Spec.adjunction_unit_app_app_top],
  simp only [category.assoc, eq_to_hom_op],
  erw ← functor.map_comp_assoc,
  rw [eq_to_hom_trans, eq_to_hom_refl, category_theory.functor.map_id,
    category.id_comp],
  erw Spec_Γ_identity.inv_hom_id_app_assoc,
  simp only [eq_to_hom_map, eq_to_hom_trans],
end

lemma is_affine_open.is_localization_stalk {X : Scheme} {U : opens X.carrier}
  (hU : is_affine_open U) (x : U) :
  is_localization.at_prime (X.presheaf.stalk x) (hU.prime_ideal_of x).as_ideal :=
begin
  haveI : is_affine _ := hU,
  haveI : nonempty U := ⟨x⟩,
  rcases x with ⟨x, hx⟩,
  let y := hU.prime_ideal_of ⟨x, hx⟩,
  have : hU.from_Spec.val.base y = x := hU.from_Spec_prime_ideal_of ⟨x, hx⟩,
  change is_localization y.as_ideal.prime_compl _,
  clear_value y,
  subst this,
  apply (is_localization.is_localization_iff_of_ring_equiv _
    (as_iso $ PresheafedSpace.stalk_map hU.from_Spec.1 y).CommRing_iso_to_ring_equiv).mpr,
  convert structure_sheaf.is_localization.to_stalk _ _ using 1,
  delta structure_sheaf.stalk_algebra,
  congr' 1,
  rw ring_hom.algebra_map_to_algebra,
  refine (PresheafedSpace.stalk_map_germ hU.from_Spec.1 _ ⟨_, _⟩).trans _,
  delta is_affine_open.from_Spec Scheme.iso_Spec structure_sheaf.to_stalk,
  simp only [Scheme.comp_val_c_app, category.assoc],
  dsimp only [functor.op, as_iso_inv, unop_op],
  erw is_affine_open.is_localization_stalk_aux,
  simp only [category.assoc],
  conv_lhs { rw ← category.assoc },
  erw [← X.presheaf.map_comp, Spec_Γ_naturality_assoc],
  congr' 1,
  simp only [← category.assoc],
  transitivity _ ≫ (structure_sheaf (X.presheaf.obj $ op U)).1.germ ⟨_, _⟩,
  { refl },
  convert ((structure_sheaf (X.presheaf.obj $ op U)).1.germ_res (hom_of_le le_top) ⟨_, _⟩) using 2,
  rw category.assoc,
  erw nat_trans.naturality,
  rw [← LocallyRingedSpace.Γ_map_op, ← LocallyRingedSpace.Γ.map_comp_assoc, ← op_comp],
  erw ← Scheme.Spec.map_comp,
  rw [← op_comp, ← X.presheaf.map_comp],
  transitivity LocallyRingedSpace.Γ.map (quiver.hom.op $ Scheme.Spec.map
    (X.presheaf.map (𝟙 (op U))).op) ≫ _,
  { congr },
  simp only [category_theory.functor.map_id, op_id],
  erw category_theory.functor.map_id,
  rw category.id_comp,
  refl
end

end algebraic_geometry
