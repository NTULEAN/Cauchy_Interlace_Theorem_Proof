/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Eric Wieser
-/

import group_theory.congruence
import linear_algebra.multilinear.tensor_product

/-!
# Tensor product of an indexed family of modules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of modules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `free_add_monoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `linear_algebra/tensor_product.lean`.

## Main definitions

* `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `lift_add_hom` constructs an `add_monoid_hom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : multilinear_map R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.
* `pi_tensor_product.reindex e` re-indexes the components of `⨂[R] i : ι, M` along `e : ι ≃ ι₂`.
* `pi_tensor_product.tmul_equiv` equivalence between a `tensor_product` of `pi_tensor_product`s and
  a single `pi_tensor_product`.

## Notations

* `⨂[R] i, s i` is defined as localized notation in locale `tensor_product`
* `⨂ₜ[R] i, f i` with `f : Π i, f i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `free_add_monoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `free_add_monoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

open function

section semiring

variables {ι ι₂ ι₃ : Type*} [decidable_eq ι] [decidable_eq ι₂] [decidable_eq ι₃]
variables {R : Type*} [comm_semiring R]
variables {R₁ R₂ : Type*}
variables {s : ι → Type*} [∀ i, add_comm_monoid (s i)] [∀ i, module R (s i)]
variables {M : Type*} [add_comm_monoid M] [module R M]
variables {E : Type*} [add_comm_monoid E] [module R E]
variables {F : Type*} [add_comm_monoid F]

namespace pi_tensor_product
include R
variables (R) (s)

/-- The relation on `free_add_monoid (R × Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (R × Π i, s i) → free_add_monoid (R × Π i, s i) → Prop
| of_zero : ∀ (r : R) (f : Π i, s i) (i : ι) (hf : f i = 0), eqv (free_add_monoid.of (r, f)) 0
| of_zero_scalar : ∀ (f : Π i, s i), eqv (free_add_monoid.of (0, f)) 0
| of_add : ∀ (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), eqv
    (free_add_monoid.of (r, update f i m₁) + free_add_monoid.of (r, update f i m₂))
    (free_add_monoid.of (r, update f i (m₁ + m₂)))
| of_add_scalar : ∀ (r r' : R) (f : Π i, s i), eqv
    (free_add_monoid.of (r, f) + free_add_monoid.of (r', f))
    (free_add_monoid.of (r + r', f))
| of_smul : ∀ (r : R) (f : Π i, s i) (i : ι) (r' : R), eqv
    (free_add_monoid.of (r, update f i (r' • (f i))))
    (free_add_monoid.of (r' * r, f))
| add_comm : ∀ x y, eqv (x + y) (y + x)

end pi_tensor_product

variables (R) (s)

/-- `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
def pi_tensor_product : Type* :=
(add_con_gen (pi_tensor_product.eqv R s)).quotient

variables {R}

/- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product, given `s : ι → Type*`. -/
localized "notation `⨂[`:100 R `] ` binders `, ` r:(scoped:67 f, pi_tensor_product R f) := r"
  in tensor_product

open_locale tensor_product

namespace pi_tensor_product

section module

instance : add_comm_monoid (⨂[R] i, s i) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (pi_tensor_product.eqv R s)).add_monoid }

instance : inhabited (⨂[R] i, s i) := ⟨0⟩

variables (R) {s}

/-- `tprod_coeff R r f` with `r : R` and `f : Π i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as an auxiliary
definition for this file alone, and that one should use `tprod` defined below for most purposes. -/
def tprod_coeff (r : R) (f : Π i, s i) : ⨂[R] i, s i := add_con.mk' _ $ free_add_monoid.of (r, f)

variables {R}

lemma zero_tprod_coeff (f : Π i, s i) : tprod_coeff R 0 f = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_scalar _

lemma zero_tprod_coeff' (z : R) (f : Π i, s i) (i : ι) (hf: f i = 0) : tprod_coeff R z f = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero _ _ i hf

lemma add_tprod_coeff (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
  tprod_coeff R z (update f i m₁) + tprod_coeff R z (update f i m₂) =
    tprod_coeff R z (update f i (m₁ + m₂)) :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add z f i m₁ m₂)

lemma add_tprod_coeff' (z₁ z₂ : R) (f : Π i, s i) :
  tprod_coeff R z₁ f + tprod_coeff R z₂ f = tprod_coeff R (z₁ + z₂) f :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add_scalar z₁ z₂ f)

lemma smul_tprod_coeff_aux (z : R) (f : Π i, s i) (i : ι) (r : R) :
  tprod_coeff R z (update f i (r • f i)) = tprod_coeff R (r * z) f :=
 quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _ _

lemma smul_tprod_coeff (z : R) (f : Π i, s i) (i : ι) (r : R₁)
  [has_scalar R₁ R] [is_scalar_tower R₁ R R] [has_scalar R₁ (s i)] [is_scalar_tower R₁ R (s i)] :
  tprod_coeff R z (update f i (r • f i)) = tprod_coeff R (r • z) f :=
begin
  have h₁ : r • z = (r • (1 : R)) * z := by rw [smul_mul_assoc, one_mul],
  have h₂ : r • (f i) = (r • (1 : R)) • f i := (smul_one_smul _ _ _).symm,
  rw [h₁, h₂],
  exact smul_tprod_coeff_aux z f i _,
end

/-- Construct an `add_monoid_hom` from `(⨂[R] i, s i)` to some space `F` from a function
`φ : (R × Π i, s i) → F` with the appropriate properties. -/
def lift_add_hom (φ : (R × Π i, s i) → F)
  (C0 : ∀ (r : R) (f : Π i, s i) (i : ι) (hf : f i = 0), φ (r, f) = 0)
  (C0' : ∀ (f : Π i, s i), φ (0, f) = 0)
  (C_add : ∀ (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
    φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
  (C_add_scalar : ∀ (r r' : R) (f : Π i, s i),
    φ (r , f) + φ (r', f) = φ (r + r', f))
  (C_smul : ∀ (r : R) (f : Π i, s i) (i : ι) (r' : R),
    φ (r, update f i (r' • (f i))) = φ (r' * r, f))
: (⨂[R] i, s i) →+ F :=
(add_con_gen (pi_tensor_product.eqv R s)).lift (free_add_monoid.lift φ) $ add_con.add_con_gen_le $
λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero r' f i hf)        := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C0 r' f i hf]
| _, _, (eqv.of_zero_scalar f)        := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C0']
| _, _, (eqv.of_add z f i m₁ m₂)      := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C_add]
| _, _, (eqv.of_add_scalar z₁ z₂ f)      := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C_add_scalar]
| _, _, (eqv.of_smul z f i r')     := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C_smul]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end

@[elab_as_eliminator]
protected theorem induction_on'
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C1 : ∀ {r : R} {f : Π i, s i}, C (tprod_coeff R r f))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
begin
  have C0 : C 0,
  { have h₁ := @C1 0 0,
    rwa [zero_tprod_coeff] at h₁ },
  refine add_con.induction_on z (λ x, free_add_monoid.rec_on x C0 _),
  simp_rw add_con.coe_add,
  refine λ f y ih, Cp _ ih,
  convert @C1 f.1 f.2,
  simp only [prod.mk.eta],
end

section distrib_mul_action
variables [monoid R₁] [distrib_mul_action R₁ R] [smul_comm_class R₁ R R]
variables [monoid R₂] [distrib_mul_action R₂ R] [smul_comm_class R₂ R R]

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance has_scalar' : has_scalar R₁ (⨂[R] i, s i) :=
⟨λ r, lift_add_hom (λ f : R × Π i, s i, tprod_coeff R (r • f.1) f.2)
  (λ r' f i hf, by simp_rw [zero_tprod_coeff' _ f i hf])
  (λ f, by simp [zero_tprod_coeff])
  (λ r' f i m₁ m₂, by simp [add_tprod_coeff])
  (λ r' r'' f, by simp [add_tprod_coeff', mul_add])
  (λ z f i r', by simp [smul_tprod_coeff, mul_smul_comm])⟩

instance : has_scalar R (⨂[R] i, s i) := pi_tensor_product.has_scalar'

lemma smul_tprod_coeff' (r : R₁) (z : R) (f : Π i, s i) :
  r • (tprod_coeff R z f) = tprod_coeff R (r • z) f := rfl

protected theorem smul_add (r : R₁) (x y : ⨂[R] i, s i) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

instance distrib_mul_action' : distrib_mul_action R₁ (⨂[R] i, s i) :=
{ smul := (•),
  smul_add := λ r x y, add_monoid_hom.map_add _ _ _,
  mul_smul := λ r r' x, pi_tensor_product.induction_on' x
    (λ r'' f, by simp [smul_tprod_coeff', smul_smul])
    (λ x y ihx ihy, by simp_rw [pi_tensor_product.smul_add, ihx, ihy]),
  one_smul := λ x, pi_tensor_product.induction_on' x
    (λ f, by simp [smul_tprod_coeff' _ _])
    (λ z y ihz ihy, by simp_rw [pi_tensor_product.smul_add, ihz, ihy]),
  smul_zero := λ r, add_monoid_hom.map_zero _ }

instance smul_comm_class' [smul_comm_class R₁ R₂ R] : smul_comm_class R₁ R₂ (⨂[R] i, s i) :=
⟨λ r' r'' x, pi_tensor_product.induction_on' x
  (λ xr xf, by simp only [smul_tprod_coeff', smul_comm])
  (λ z y ihz ihy, by simp_rw [pi_tensor_product.smul_add, ihz, ihy])⟩

instance is_scalar_tower' [has_scalar R₁ R₂] [is_scalar_tower R₁ R₂ R] :
  is_scalar_tower R₁ R₂ (⨂[R] i, s i) :=
⟨λ r' r'' x, pi_tensor_product.induction_on' x
  (λ xr xf, by simp only [smul_tprod_coeff', smul_assoc])
  (λ z y ihz ihy, by simp_rw [pi_tensor_product.smul_add, ihz, ihy])⟩

end distrib_mul_action

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance module' [semiring R₁] [module R₁ R] [smul_comm_class R₁ R R] : module R₁ (⨂[R] i, s i) :=
{ smul := (•),
  add_smul := λ r r' x, pi_tensor_product.induction_on' x
    (λ r f, by simp [smul_tprod_coeff' _ _, add_smul, add_tprod_coeff'])
    (λ x y ihx ihy, by simp [pi_tensor_product.smul_add, ihx, ihy, add_add_add_comm]),
  zero_smul := λ x, pi_tensor_product.induction_on' x
    (λ r f, by { simp_rw [smul_tprod_coeff' _ _, zero_smul], exact zero_tprod_coeff _ })
    (λ x y ihx ihy, by rw [pi_tensor_product.smul_add, ihx, ihy, add_zero]),
  ..pi_tensor_product.distrib_mul_action' }

-- shortcut instances
instance : module R (⨂[R] i, s i) := pi_tensor_product.module'
instance : smul_comm_class R R (⨂[R] i, s i) := pi_tensor_product.smul_comm_class'
instance : is_scalar_tower R R (⨂[R] i, s i) := pi_tensor_product.is_scalar_tower'

variables {R}

variables (R)
/-- The canonical `multilinear_map R s (⨂[R] i, s i)`. -/
def tprod : multilinear_map R s (⨂[R] i, s i) :=
{ to_fun := tprod_coeff R 1,
  map_add' := λ f i x y, (add_tprod_coeff (1 : R) f i x y).symm,
  map_smul' := λ f i r x,
    by simp_rw [smul_tprod_coeff', ←smul_tprod_coeff (1 : R) _ i, update_idem, update_same] }

variables {R}

notation `⨂ₜ[`:100 R`] ` binders `, ` r:(scoped:67 f, tprod R f) := r

@[simp]
lemma tprod_coeff_eq_smul_tprod (z : R) (f : Π i, s i) : tprod_coeff R z f = z • tprod R f :=
begin
  have : z = z • (1 : R) := by simp only [mul_one, algebra.id.smul_eq_mul],
  conv_lhs { rw this },
  rw ←smul_tprod_coeff',
  refl,
end

@[elab_as_eliminator]
protected theorem induction_on
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C1 : ∀ {r : R} {f : Π i, s i}, C (r • (tprod R f)))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
begin
  simp_rw ←tprod_coeff_eq_smul_tprod at C1,
  exact pi_tensor_product.induction_on' z @C1 @Cp,
end

@[ext]
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E}
  (H : φ₁.comp_multilinear_map (tprod R) = φ₂.comp_multilinear_map (tprod R)) : φ₁ = φ₂ :=
begin
  refine linear_map.ext _,
  refine λ z,
    (pi_tensor_product.induction_on' z _ (λ x y hx hy, by rw [φ₁.map_add, φ₂.map_add, hx, hy])),
  { intros r f,
    rw [tprod_coeff_eq_smul_tprod, φ₁.map_smul, φ₂.map_smul],
    apply _root_.congr_arg,
    exact multilinear_map.congr_fun H f }
end

end module

section multilinear
open multilinear_map
variables {s}

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`multilinear map R s E` with the property that its composition with the canonical
`multilinear_map R s (⨂[R] i, s i)` is the given multilinear map. -/
def lift_aux (φ : multilinear_map R s E) : (⨂[R] i, s i) →+ E :=
  lift_add_hom (λ (p : R × Π i, s i), p.1 • (φ p.2))
    (λ z f i hf, by rw [map_coord_zero φ i hf, smul_zero])
    (λ f, by rw [zero_smul])
    (λ z f i m₁ m₂, by rw [←smul_add, φ.map_add])
    (λ z₁ z₂ f, by rw [←add_smul])
    (λ z f i r, by simp [φ.map_smul, smul_smul, mul_comm])

lemma lift_aux_tprod (φ : multilinear_map R s E) (f : Π i, s i) : lift_aux φ (tprod R f) = φ f :=
by simp only [lift_aux, lift_add_hom, tprod, multilinear_map.coe_mk, tprod_coeff,
              free_add_monoid.lift_eval_of, one_smul, add_con.lift_mk']

lemma lift_aux_tprod_coeff (φ : multilinear_map R s E) (z : R) (f : Π i, s i) :
  lift_aux φ (tprod_coeff R z f) = z • φ f :=
by simp [lift_aux, lift_add_hom, tprod_coeff, free_add_monoid.lift_eval_of]

lemma lift_aux.smul {φ : multilinear_map R s E} (r : R) (x : ⨂[R] i, s i) :
  lift_aux φ (r • x) = r • lift_aux φ x :=
begin
  refine pi_tensor_product.induction_on' x _ _,
  { intros z f,
    rw [smul_tprod_coeff' r z f, lift_aux_tprod_coeff, lift_aux_tprod_coeff, smul_assoc] },
  { intros z y ihz ihy,
    rw [smul_add, (lift_aux φ).map_add, ihz, ihy, (lift_aux φ).map_add, smul_add] }
end

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `multilinear_map R s E` with the
property that its composition with the canonical `multilinear_map R s E` is
the given multilinear map `φ`. -/
def lift : (multilinear_map R s E) ≃ₗ[R] ((⨂[R] i, s i) →ₗ[R] E) :=
{ to_fun := λ φ, { map_smul' := lift_aux.smul, .. lift_aux φ },
  inv_fun := λ φ', φ'.comp_multilinear_map (tprod R),
  left_inv := λ φ, by { ext, simp [lift_aux_tprod, linear_map.comp_multilinear_map] },
  right_inv := λ φ, by { ext, simp [lift_aux_tprod] },
  map_add' := λ φ₁ φ₂, by { ext, simp [lift_aux_tprod] },
  map_smul' := λ r φ₂, by { ext, simp [lift_aux_tprod] } }

variables {φ : multilinear_map R s E}

@[simp] lemma lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f := lift_aux_tprod φ f
theorem lift.unique' {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : φ'.comp_multilinear_map (tprod R) = φ) :
  φ' = lift φ :=
ext $ H.symm ▸ (lift.symm_apply_apply φ).symm

theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (tprod R f) = φ f) :
  φ' = lift φ :=
lift.unique' (multilinear_map.ext H)

@[simp]
theorem lift_symm (φ' : (⨂[R] i, s i) →ₗ[R] E) : lift.symm φ' = φ'.comp_multilinear_map (tprod R) :=
rfl

@[simp]
theorem lift_tprod : lift (tprod R : multilinear_map R s _) = linear_map.id :=
eq.symm $ lift.unique' rfl

section

variables (R M)
/-- Re-index the components of the tensor power by `e`.

For simplicity, this is defined only for homogeneously- (rather than dependently-) typed components.
-/
def reindex (e : ι ≃ ι₂) : ⨂[R] i : ι, M ≃ₗ[R] ⨂[R] i : ι₂, M :=
linear_equiv.of_linear
  (lift (dom_dom_congr e.symm (tprod R : multilinear_map R _ (⨂[R] i : ι₂, M))))
  (lift (dom_dom_congr e (tprod R : multilinear_map R _ (⨂[R] i : ι, M))))
  (by { ext, simp only [linear_map.comp_apply, linear_map.id_apply, lift_tprod,
                        linear_map.comp_multilinear_map_apply, lift.tprod,
                        dom_dom_congr_apply, equiv.apply_symm_apply] })
  (by { ext, simp only [linear_map.comp_apply, linear_map.id_apply, lift_tprod,
                        linear_map.comp_multilinear_map_apply, lift.tprod,
                        dom_dom_congr_apply, equiv.symm_apply_apply] })

end

@[simp] lemma reindex_tprod (e : ι ≃ ι₂) (f : Π i, M) :
  reindex R M e (tprod R f) = tprod R (λ i, f (e.symm i)) :=
lift.tprod f

@[simp] lemma reindex_comp_tprod (e : ι ≃ ι₂) :
  (reindex R M e : ⨂[R] i : ι, M →ₗ[R] ⨂[R] i : ι₂, M).comp_multilinear_map (tprod R) =
    (tprod R : multilinear_map R (λ i, M) _).dom_dom_congr e.symm :=
multilinear_map.ext $ reindex_tprod e

@[simp] lemma lift_comp_reindex (e : ι ≃ ι₂) (φ : multilinear_map R (λ _ : ι₂, M) E) :
  (lift φ) ∘ₗ ↑(reindex R M e) = lift (φ.dom_dom_congr e.symm) :=
by { ext, simp, }

@[simp]
lemma lift_reindex (e : ι ≃ ι₂) (φ : multilinear_map R (λ _, M) E) (x : ⨂[R] i, M) :
  lift φ (reindex R M e x) = lift (φ.dom_dom_congr e.symm) x :=
linear_map.congr_fun (lift_comp_reindex e φ) x

@[simp] lemma reindex_trans (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) :
  (reindex R M e).trans (reindex R M e') = reindex R M (e.trans e') :=
begin
  apply linear_equiv.to_linear_map_injective,
  ext f,
  simp only [linear_equiv.trans_apply, linear_equiv.coe_coe, reindex_tprod,
    linear_map.coe_comp_multilinear_map, function.comp_app, multilinear_map.dom_dom_congr_apply,
    reindex_comp_tprod],
  congr,
end

@[simp] lemma reindex_reindex (e : ι ≃ ι₂) (e' : ι₂ ≃ ι₃) (x : ⨂[R] i, M) :
  reindex R M e' (reindex R M e x) = reindex R M (e.trans e') x :=
linear_equiv.congr_fun (reindex_trans e e' : _ = reindex R M (e.trans e')) x

@[simp] lemma reindex_symm (e : ι ≃ ι₂) :
  (reindex R M e).symm = reindex R M e.symm := rfl

@[simp] lemma reindex_refl : reindex R M (equiv.refl ι) = linear_equiv.refl R _ :=
begin
  apply linear_equiv.to_linear_map_injective,
  ext1,
  rw [reindex_comp_tprod, linear_equiv.refl_to_linear_map, equiv.refl_symm],
  refl,
end

variables (ι)

/-- The tensor product over an empty index type `ι` is isomorphic to the base ring. -/
@[simps symm_apply]
def is_empty_equiv [is_empty ι] : ⨂[R] i : ι, M ≃ₗ[R] R :=
{ to_fun := lift (const_of_is_empty R 1),
  inv_fun := λ r, r • tprod R (@is_empty_elim _ _ _),
  left_inv := λ x, by
  { apply x.induction_on,
    { intros r f,
      have := subsingleton.elim f is_empty_elim,
      simp [this], },
    { simp only,
      intros x y hx hy,
      simp [add_smul, hx, hy] }},
  right_inv := λ t, by simp only [mul_one, algebra.id.smul_eq_mul, const_of_is_empty_apply,
    linear_map.map_smul, pi_tensor_product.lift.tprod],
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _, }

@[simp]
lemma is_empty_equiv_apply_tprod [is_empty ι] (f : ι → M) : is_empty_equiv ι (tprod R f) = 1 :=
lift.tprod _

variables {ι}

/-- The tensor product over an single index is isomorphic to the module -/
@[simps symm_apply]
def subsingleton_equiv [subsingleton ι] (i₀ : ι) : ⨂[R] i : ι, M ≃ₗ[R] M :=
{ to_fun := lift (multilinear_map.of_subsingleton R M i₀),
  inv_fun := λ m, tprod R (λ v, m),
  left_inv := λ x, by
  { dsimp only,
    have : ∀ (f : ι → M) (z : M), (λ i : ι, z) = update f i₀ z,
    { intros f z,
      ext i,
      rw [subsingleton.elim i i₀, function.update_same] },
    apply x.induction_on,
    { intros r f,
      simp only [linear_map.map_smul, lift.tprod, of_subsingleton_apply, function.eval,
                 this f, map_smul, update_eq_self], },
    { intros x y hx hy,
      simp only [multilinear_map.map_add, this 0 (_ + _), linear_map.map_add, ←this 0 (lift _ _),
        hx, hy] } },
  right_inv := λ t, by simp only [of_subsingleton_apply, lift.tprod, function.eval_apply],
  map_add' := linear_map.map_add _,
  map_smul' := linear_map.map_smul _, }

@[simp]
lemma subsingleton_equiv_apply_tprod [subsingleton ι] (i : ι) (f : ι → M) :
  subsingleton_equiv i (tprod R f) = f i :=
lift.tprod _

section tmul

/-- Collapse a `tensor_product` of `pi_tensor_product`s. -/
private def tmul : (⨂[R] i : ι, M) ⊗[R] (⨂[R] i : ι₂, M) →ₗ[R] ⨂[R] i : ι ⊕ ι₂, M :=
tensor_product.lift
  { to_fun := λ a, pi_tensor_product.lift $ pi_tensor_product.lift
      (multilinear_map.curry_sum_equiv R _ _ M _ (tprod R)) a,
    map_add' := λ a b, by simp only [linear_equiv.map_add, linear_map.map_add],
    map_smul' := λ r a, by simp only [linear_equiv.map_smul, linear_map.map_smul,
                                      ring_hom.id_apply], }

private lemma tmul_apply (a : ι → M) (b : ι₂ → M) :
  tmul ((⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, sum.elim a b i :=
begin
  erw [tensor_product.lift.tmul, pi_tensor_product.lift.tprod, pi_tensor_product.lift.tprod],
  refl
end

/-- Expand `pi_tensor_product` into a `tensor_product` of two factors. -/
private def tmul_symm : ⨂[R] i : ι ⊕ ι₂, M →ₗ[R] (⨂[R] i : ι, M) ⊗[R] (⨂[R] i : ι₂, M) :=
-- by using tactic mode, we avoid the need for a lot of `@`s and `_`s
pi_tensor_product.lift $ by apply multilinear_map.dom_coprod; [exact tprod R, exact tprod R]

private lemma tmul_symm_apply (a : ι ⊕ ι₂ → M) :
  tmul_symm (⨂ₜ[R] i, a i) = (⨂ₜ[R] i, a (sum.inl i)) ⊗ₜ[R] (⨂ₜ[R] i, a (sum.inr i)) :=
pi_tensor_product.lift.tprod _

variables (R M)
local attribute [ext] tensor_product.ext

/-- Equivalence between a `tensor_product` of `pi_tensor_product`s and a single
`pi_tensor_product` indexed by a `sum` type.

For simplicity, this is defined only for homogeneously- (rather than dependently-) typed components.
-/
def tmul_equiv : (⨂[R] i : ι, M) ⊗[R] (⨂[R] i : ι₂, M) ≃ₗ[R] ⨂[R] i : ι ⊕ ι₂, M :=
linear_equiv.of_linear tmul tmul_symm
  (by { ext x,
        show tmul (tmul_symm (tprod R x)) = tprod R x, -- Speed up the call to `simp`.
        simp only [tmul_symm_apply, tmul_apply, sum.elim_comp_inl_inr], })
  (by { ext x y,
        show tmul_symm (tmul (tprod R x ⊗ₜ[R] tprod R y)) = tprod R x ⊗ₜ[R] tprod R y,
        simp only [tmul_apply, tmul_symm_apply, sum.elim_inl, sum.elim_inr], })

@[simp] lemma tmul_equiv_apply (a : ι → M) (b : ι₂ → M) :
  tmul_equiv R M ((⨂ₜ[R] i, a i) ⊗ₜ[R] (⨂ₜ[R] i, b i)) = ⨂ₜ[R] i, sum.elim a b i :=
tmul_apply a b

@[simp] lemma tmul_equiv_symm_apply (a : ι ⊕ ι₂ → M) :
  (tmul_equiv R M).symm (⨂ₜ[R] i, a i) = (⨂ₜ[R] i, a (sum.inl i)) ⊗ₜ[R] (⨂ₜ[R] i, a (sum.inr i)) :=
tmul_symm_apply a

end tmul

end multilinear

end pi_tensor_product

end semiring

section ring
namespace pi_tensor_product

open pi_tensor_product
open_locale tensor_product

variables {ι : Type*} [decidable_eq ι] {R : Type*} [comm_ring R]
variables {s : ι → Type*} [∀ i, add_comm_group (s i)] [∀ i, module R (s i)]

/- Unlike for the binary tensor product, we require `R` to be a `comm_ring` here, otherwise
this is false in the case where `ι` is empty. -/
instance : add_comm_group (⨂[R] i, s i) := module.add_comm_monoid_to_add_comm_group R

end pi_tensor_product
end ring
