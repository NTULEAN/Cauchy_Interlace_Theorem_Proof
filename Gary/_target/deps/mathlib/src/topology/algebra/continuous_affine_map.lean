/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import linear_algebra.affine_space.affine_map
import topology.continuous_function.basic
import topology.algebra.module.basic

/-!
# Continuous affine maps.

This file defines a type of bundled continuous affine maps.

Note that the definition and basic properties established here require minimal assumptions, and do
not even assume compatibility between the topological and algebraic structures. Of course it is
necessary to assume some compatibility in order to obtain a useful theory. Such a theory is
developed elsewhere for affine spaces modelled on _normed_ vector spaces, but not yet for general
topological affine spaces (since we have not defined these yet).

## Main definitions:

 * `continuous_affine_map`

## Notation:

We introduce the notation `P →A[R] Q` for `continuous_affine_map R P Q`. Note that this is parallel
to the notation `E →L[R] F` for `continuous_linear_map R E F`.
-/

/-- A continuous map of affine spaces. -/
structure continuous_affine_map (R : Type*) {V W : Type*} (P Q : Type*) [ring R]
  [add_comm_group V] [module R V] [topological_space P] [add_torsor V P]
  [add_comm_group W] [module R W] [topological_space Q] [add_torsor W Q]
  extends P →ᵃ[R] Q :=
(cont : continuous to_fun)

notation P ` →A[`:25 R `] ` Q := continuous_affine_map R P Q

namespace continuous_affine_map

variables {R V W P Q : Type*} [ring R]
variables [add_comm_group V] [module R V] [topological_space P] [add_torsor V P]
variables [add_comm_group W] [module R W] [topological_space Q] [add_torsor W Q]

include V W

/-- see Note [function coercion] -/
instance : has_coe_to_fun (P →A[R] Q) (λ _, P → Q) := ⟨λ f, f.to_affine_map.to_fun⟩

lemma to_fun_eq_coe (f : P →A[R] Q) : f.to_fun = ⇑f := rfl

lemma coe_injective :
  @function.injective (P →A[R] Q) (P → Q) coe_fn :=
begin
  rintros ⟨⟨f, ⟨f', hf₁, hf₂⟩, hf₀⟩, hf₁⟩ ⟨⟨g, ⟨g', hg₁, hg₂⟩, hg₀⟩, hg₁⟩ h,
  have : f = g ∧ f' = g', { simpa only using affine_map.coe_fn_injective h, },
  congr,
  exacts [this.1, this.2],
end

@[ext] lemma ext {f g : P →A[R] Q} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : P →A[R] Q} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl, }, ext⟩

lemma congr_fun {f g : P →A[R] Q} (h : f = g) (x : P) : f x = g x := h ▸ rfl

instance : has_coe (P →A[R] Q) (P →ᵃ[R] Q) :=
⟨to_affine_map⟩

/-- Forgetting its algebraic properties, a continuous affine map is a continuous map. -/
def to_continuous_map (f : P →A[R] Q) : C(P, Q) :=
⟨f, f.cont⟩

instance : has_coe (P →A[R] Q) (C(P, Q)) :=
⟨to_continuous_map⟩

@[simp] lemma to_affine_map_eq_coe (f : P →A[R] Q) :
  f.to_affine_map = ↑f :=
rfl

@[simp] lemma to_continuous_map_coe (f : P →A[R] Q) : f.to_continuous_map = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_affine_map (f : P →A[R] Q) :
  ((f : P →ᵃ[R] Q) : P → Q) = f :=
rfl

@[simp, norm_cast] lemma coe_to_continuous_map (f : P →A[R] Q) :
  ((f : C(P, Q)) : P → Q) = f :=
rfl

lemma to_affine_map_injective {f g : P →A[R] Q}
  (h : (f : P →ᵃ[R] Q) = (g : P →ᵃ[R] Q)) : f = g :=
by { ext a, exact affine_map.congr_fun h a, }

lemma to_continuous_map_injective {f g : P →A[R] Q}
  (h : (f : C(P, Q)) = (g : C(P, Q))) : f = g :=
by { ext a, exact continuous_map.congr_fun h a, }

@[norm_cast] lemma coe_affine_map_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : P →ᵃ[R] Q) = f :=
rfl

@[norm_cast] lemma coe_continuous_map_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : C(P, Q)) = ⟨f, h⟩ :=
rfl

@[simp] lemma coe_mk (f : P →ᵃ[R] Q) (h) :
  ((⟨f, h⟩ : P →A[R] Q) : P → Q) = f :=
rfl

@[simp] lemma mk_coe (f : P →A[R] Q) (h) :
  (⟨(f : P →ᵃ[R] Q), h⟩ : P →A[R] Q) = f :=
by { ext, refl, }

@[continuity]
protected lemma continuous (f : P →A[R] Q) : continuous f := f.2

variables (R P)

/-- The constant map is a continuous affine map. -/
def const (q : Q) : P →A[R] Q :=
{ to_fun := affine_map.const R P q,
  cont   := continuous_const,
  .. affine_map.const R P q, }

@[simp] lemma coe_const (q : Q) : (const R P q : P → Q) = function.const P q := rfl

noncomputable instance : inhabited (P →A[R] Q) :=
⟨const R P $ nonempty.some (by apply_instance : nonempty Q)⟩

variables {R P} {W₂ Q₂ : Type*}
variables [add_comm_group W₂] [module R W₂] [topological_space Q₂] [add_torsor W₂ Q₂]

include W₂

/-- The composition of morphisms is a morphism. -/
def comp (f : Q →A[R] Q₂) (g : P →A[R] Q) : P →A[R] Q₂ :=
{ cont := f.cont.comp g.cont,
  .. (f : Q →ᵃ[R] Q₂).comp (g : P →ᵃ[R] Q), }

@[simp, norm_cast] lemma coe_comp (f : Q →A[R] Q₂) (g : P →A[R] Q) :
  (f.comp g : P → Q₂) = (f : Q → Q₂) ∘ (g : P → Q) :=
rfl

lemma comp_apply (f : Q →A[R] Q₂) (g : P →A[R] Q) (x : P) :
  f.comp g x = f (g x) :=
rfl

omit W₂

section module_valued_maps

variables {S : Type*} [comm_ring S] [module S V] [module S W]
variables [topological_space W] [topological_space S] [has_continuous_smul S W]

instance : has_zero (P →A[R] W) := ⟨continuous_affine_map.const R P 0⟩

@[norm_cast, simp] lemma coe_zero : ((0 : P →A[R] W) : P → W) = 0 := rfl

lemma zero_apply (x : P) : (0 : P →A[R] W) x = 0 := rfl

instance : has_scalar S (P →A[S] W) :=
{ smul := λ t f, { cont := f.continuous.const_smul t, .. (t • (f : P →ᵃ[S] W)) } }

@[norm_cast, simp] lemma coe_smul (t : S) (f : P →A[S] W) : ⇑(t • f) = t • f := rfl

lemma smul_apply (t : S) (f : P →A[S] W) (x : P) : (t • f) x = t • (f x) := rfl

variables [topological_add_group W]

instance : has_add (P →A[R] W) :=
{ add := λ f g, { cont := f.continuous.add g.continuous, .. ((f : P →ᵃ[R] W) + (g : P →ᵃ[R] W)) }, }

@[norm_cast, simp] lemma coe_add (f g : P →A[R] W) : ⇑(f + g) = f + g := rfl

lemma add_apply (f g : P →A[R] W) (x : P) : (f + g) x = f x + g x := rfl

instance : has_sub (P →A[R] W) :=
{ sub := λ f g, { cont := f.continuous.sub g.continuous, .. ((f : P →ᵃ[R] W) - (g : P →ᵃ[R] W)) }, }

@[norm_cast, simp] lemma coe_sub (f g : P →A[R] W) : ⇑(f - g) = f - g := rfl

lemma sub_apply (f g : P →A[R] W) (x : P) : (f - g) x = f x - g x := rfl

instance : has_neg (P →A[R] W) :=
{ neg := λ f, { cont := f.continuous.neg, .. (-(f : P →ᵃ[R] W)) }, }

@[norm_cast, simp] lemma coe_neg (f : P →A[R] W) : ⇑(-f) = -f := rfl

lemma neg_apply (f : P →A[R] W) (x : P) : (-f) x = -(f x) := rfl

instance : add_comm_group (P →A[R] W) :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  sub := has_sub.sub,
  .. (coe_injective.add_comm_group _ coe_zero coe_add coe_neg coe_sub :
    add_comm_group (P →A[R] W)) }

instance : module S (P →A[S] W) :=
function.injective.module S ⟨λ f, f.to_affine_map.to_fun, rfl, coe_add⟩ coe_injective coe_smul

end module_valued_maps

end continuous_affine_map

namespace continuous_linear_map

variables {R V W : Type*} [ring R]
variables [add_comm_group V] [module R V] [topological_space V]
variables [add_comm_group W] [module R W] [topological_space W]

/-- A continuous linear map can be regarded as a continuous affine map. -/
def to_continuous_affine_map (f : V →L[R] W) : V →A[R] W :=
{ to_fun    := f,
  linear    := f,
  map_vadd' := by simp,
  cont      := f.cont, }

@[simp] lemma coe_to_continuous_affine_map (f : V →L[R] W) :
  ⇑f.to_continuous_affine_map = f :=
rfl

@[simp] lemma to_continuous_affine_map_map_zero (f : V →L[R] W) :
  f.to_continuous_affine_map 0 = 0 :=
by simp

end continuous_linear_map
