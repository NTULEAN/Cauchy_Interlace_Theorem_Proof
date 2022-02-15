/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.operations
import data.set.Union_lift
import ring_theory.subring.pointwise

/-!
# Subalgebras over Commutative Semiring

In this file we define `subalgebra`s and the usual operations on them (`map`, `comap'`).

More lemmas about `adjoin` can be found in `ring_theory.adjoin`.
-/
universes u u' v w w'

open_locale tensor_product big_operators

set_option old_structure_cmd true

/-- A subalgebra is a sub(semi)ring that includes the range of `algebra_map`. -/
structure subalgebra (R : Type u) (A : Type v)
  [comm_semiring R] [semiring A] [algebra R A] extends subsemiring A : Type v :=
(algebra_map_mem' : ∀ r, algebra_map R A r ∈ carrier)
(zero_mem' := (algebra_map R A).map_zero ▸ algebra_map_mem' 0)
(one_mem' := (algebra_map R A).map_one ▸ algebra_map_mem' 1)

/-- Reinterpret a `subalgebra` as a `subsemiring`. -/
add_decl_doc subalgebra.to_subsemiring

namespace subalgebra

variables {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variables [comm_semiring R]
variables [semiring A] [algebra R A] [semiring B] [algebra R B] [semiring C] [algebra R C]
include R

instance : set_like (subalgebra R A) A :=
⟨subalgebra.carrier, λ p q h, by cases p; cases q; congr'⟩

@[simp]
lemma mem_carrier {s : subalgebra R A} {x : A} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

@[ext] theorem ext {S T : subalgebra R A} (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

@[simp] lemma mem_to_subsemiring {S : subalgebra R A} {x} : x ∈ S.to_subsemiring ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_subsemiring (S : subalgebra R A) : (↑S.to_subsemiring : set A) = S := rfl

theorem to_subsemiring_injective :
  function.injective (to_subsemiring : subalgebra R A → subsemiring A) :=
λ S T h, ext $ λ x, by rw [← mem_to_subsemiring, ← mem_to_subsemiring, h]

theorem to_subsemiring_inj {S U : subalgebra R A} : S.to_subsemiring = U.to_subsemiring ↔ S = U :=
to_subsemiring_injective.eq_iff

/-- Copy of a subalgebra with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : subalgebra R A) (s : set A) (hs : s = ↑S) : subalgebra R A :=
{ carrier := s,
  add_mem' := hs.symm ▸ S.add_mem',
  mul_mem' := hs.symm ▸ S.mul_mem',
  algebra_map_mem' := hs.symm ▸ S.algebra_map_mem' }

@[simp] lemma coe_copy (S : subalgebra R A) (s : set A) (hs : s = ↑S) :
  (S.copy s hs : set A) = s := rfl

lemma copy_eq (S : subalgebra R A) (s : set A) (hs : s = ↑S) : S.copy s hs = S :=
set_like.coe_injective hs

variables (S : subalgebra R A)

theorem algebra_map_mem (r : R) : algebra_map R A r ∈ S :=
S.algebra_map_mem' r

theorem srange_le : (algebra_map R A).srange ≤ S.to_subsemiring :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_subset : set.range (algebra_map R A) ⊆ S :=
λ x ⟨r, hr⟩, hr ▸ S.algebra_map_mem r

theorem range_le : set.range (algebra_map R A) ≤ S :=
S.range_subset

theorem one_mem : (1 : A) ∈ S :=
S.to_subsemiring.one_mem

theorem mul_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S :=
S.to_subsemiring.mul_mem hx hy

theorem smul_mem {x : A} (hx : x ∈ S) (r : R) : r • x ∈ S :=
(algebra.smul_def r x).symm ▸ S.mul_mem (S.algebra_map_mem r) hx

theorem pow_mem {x : A} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
S.to_subsemiring.pow_mem hx n

theorem zero_mem : (0 : A) ∈ S :=
S.to_subsemiring.zero_mem

theorem add_mem {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x + y ∈ S :=
S.to_subsemiring.add_mem hx hy

theorem neg_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) : -x ∈ S :=
neg_one_smul R x ▸ S.smul_mem hx _

theorem sub_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x y : A} (hx : x ∈ S) (hy : y ∈ S) : x - y ∈ S :=
by simpa only [sub_eq_add_neg] using S.add_mem hx (S.neg_mem hy)

theorem nsmul_mem {x : A} (hx : x ∈ S) (n : ℕ) : n • x ∈ S :=
S.to_subsemiring.nsmul_mem hx n

theorem zsmul_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) {x : A} (hx : x ∈ S) : ∀ (n : ℤ), n • x ∈ S
| (n : ℕ) := by { rw [coe_nat_zsmul], exact S.nsmul_mem hx n }
| -[1+ n] := by { rw [zsmul_neg_succ_of_nat], exact S.neg_mem (S.nsmul_mem hx _) }

theorem coe_nat_mem (n : ℕ) : (n : A) ∈ S :=
S.to_subsemiring.coe_nat_mem n

theorem coe_int_mem {R : Type u} {A : Type v} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) (n : ℤ) : (n : A) ∈ S :=
int.cases_on n (λ i, S.coe_nat_mem i) (λ i, S.neg_mem $ S.coe_nat_mem $ i + 1)

theorem list_prod_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.prod ∈ S :=
S.to_subsemiring.list_prod_mem h

theorem list_sum_mem {L : list A} (h : ∀ x ∈ L, x ∈ S) : L.sum ∈ S :=
S.to_subsemiring.list_sum_mem h

theorem multiset_prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.prod ∈ S :=
S.to_subsemiring.multiset_prod_mem m h

theorem multiset_sum_mem {m : multiset A} (h : ∀ x ∈ m, x ∈ S) : m.sum ∈ S :=
S.to_subsemiring.multiset_sum_mem m h

theorem prod_mem {R : Type u} {A : Type v} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∏ x in t, f x ∈ S :=
S.to_subsemiring.prod_mem h

theorem sum_mem {ι : Type w} {t : finset ι} {f : ι → A}
  (h : ∀ x ∈ t, f x ∈ S) : ∑ x in t, f x ∈ S :=
S.to_subsemiring.sum_mem h

/-- The projection from a subalgebra of `A` to an additive submonoid of `A`. -/
def to_add_submonoid {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : add_submonoid A :=
S.to_subsemiring.to_add_submonoid

/-- The projection from a subalgebra of `A` to a submonoid of `A`. -/
def to_submonoid {R : Type u} {A : Type v} [comm_semiring R] [semiring A] [algebra R A]
  (S : subalgebra R A) : submonoid A :=
S.to_subsemiring.to_submonoid

/-- A subalgebra over a ring is also a `subring`. -/
def to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  subring A :=
{ neg_mem' := λ _, S.neg_mem,
  .. S.to_subsemiring }

@[simp] lemma mem_to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} {x} : x ∈ S.to_subring ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_subring {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  (S : subalgebra R A) : (↑S.to_subring : set A) = S := rfl

theorem to_subring_injective {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A] :
  function.injective (to_subring : subalgebra R A → subring A) :=
λ S T h, ext $ λ x, by rw [← mem_to_subring, ← mem_to_subring, h]

theorem to_subring_inj {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S U : subalgebra R A} : S.to_subring = U.to_subring ↔ S = U :=
to_subring_injective.eq_iff

instance : inhabited S := ⟨(0 : S.to_subsemiring)⟩

section

/-! `subalgebra`s inherit structure from their `subsemiring` / `semiring` coercions. -/

instance to_semiring {R A}
  [comm_semiring R] [semiring A] [algebra R A] (S : subalgebra R A) :
  semiring S := S.to_subsemiring.to_semiring
instance to_comm_semiring {R A}
  [comm_semiring R] [comm_semiring A] [algebra R A] (S : subalgebra R A) :
  comm_semiring S := S.to_subsemiring.to_comm_semiring
instance to_ring {R A}
  [comm_ring R] [ring A] [algebra R A] (S : subalgebra R A) :
  ring S := S.to_subring.to_ring
instance to_comm_ring {R A}
  [comm_ring R] [comm_ring A] [algebra R A] (S : subalgebra R A) :
  comm_ring S := S.to_subring.to_comm_ring

instance to_ordered_semiring {R A}
  [comm_semiring R] [ordered_semiring A] [algebra R A] (S : subalgebra R A) :
  ordered_semiring S := S.to_subsemiring.to_ordered_semiring
instance to_ordered_comm_semiring {R A}
  [comm_semiring R] [ordered_comm_semiring A] [algebra R A] (S : subalgebra R A) :
  ordered_comm_semiring S := S.to_subsemiring.to_ordered_comm_semiring
instance to_ordered_ring {R A}
  [comm_ring R] [ordered_ring A] [algebra R A] (S : subalgebra R A) :
  ordered_ring S := S.to_subring.to_ordered_ring
instance to_ordered_comm_ring {R A}
  [comm_ring R] [ordered_comm_ring A] [algebra R A] (S : subalgebra R A) :
  ordered_comm_ring S := S.to_subring.to_ordered_comm_ring

instance to_linear_ordered_semiring {R A}
  [comm_semiring R] [linear_ordered_semiring A] [algebra R A] (S : subalgebra R A) :
  linear_ordered_semiring S := S.to_subsemiring.to_linear_ordered_semiring
/-! There is no `linear_ordered_comm_semiring`. -/
instance to_linear_ordered_ring {R A}
  [comm_ring R] [linear_ordered_ring A] [algebra R A] (S : subalgebra R A) :
  linear_ordered_ring S := S.to_subring.to_linear_ordered_ring
instance to_linear_ordered_comm_ring {R A}
  [comm_ring R] [linear_ordered_comm_ring A] [algebra R A] (S : subalgebra R A) :
  linear_ordered_comm_ring S := S.to_subring.to_linear_ordered_comm_ring

end

/-- Convert a `subalgebra` to `submodule` -/
def to_submodule : submodule R A :=
{ carrier := S,
  zero_mem' := (0:S).2,
  add_mem' := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul_mem' := λ c x hx, (algebra.smul_def c x).symm ▸
    (⟨algebra_map R A c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

@[simp] lemma mem_to_submodule {x} : x ∈ S.to_submodule ↔ x ∈ S := iff.rfl

@[simp] lemma coe_to_submodule (S : subalgebra R A) : (↑S.to_submodule : set A) = S := rfl

theorem to_submodule_injective :
  function.injective (to_submodule : subalgebra R A → submodule R A) :=
λ S T h, ext $ λ x, by rw [← mem_to_submodule, ← mem_to_submodule, h]

theorem to_submodule_inj {S U : subalgebra R A} : S.to_submodule = U.to_submodule ↔ S = U :=
to_submodule_injective.eq_iff

section

/-! `subalgebra`s inherit structure from their `submodule` coercions. -/

instance module' [semiring R'] [has_scalar R' R] [module R' A] [is_scalar_tower R' R A] :
  module R' S :=
S.to_submodule.module'
instance : module R S := S.module'

instance [semiring R'] [has_scalar R' R] [module R' A] [is_scalar_tower R' R A] :
  is_scalar_tower R' R S :=
S.to_submodule.is_scalar_tower

instance algebra' [comm_semiring R'] [has_scalar R' R] [algebra R' A]
  [is_scalar_tower R' R A] : algebra R' S :=
{ commutes' := λ c x, subtype.eq $ algebra.commutes _ _,
  smul_def' := λ c x, subtype.eq $ algebra.smul_def _ _,
  .. (algebra_map R' A).cod_srestrict S.to_subsemiring $ λ x, begin
    rw [algebra.algebra_map_eq_smul_one, ←smul_one_smul R x (1 : A),
      ←algebra.algebra_map_eq_smul_one],
    exact algebra_map_mem S _,
  end }
instance : algebra R S := S.algebra'


end

instance nontrivial [nontrivial A] : nontrivial S :=
S.to_subsemiring.nontrivial

instance no_zero_smul_divisors_bot [no_zero_smul_divisors R A] : no_zero_smul_divisors R S :=
⟨λ c x h,
  have c = 0 ∨ (x : A) = 0,
  from eq_zero_or_eq_zero_of_smul_eq_zero (congr_arg coe h),
  this.imp_right (@subtype.ext_iff _ _ x 0).mpr⟩

@[simp, norm_cast] lemma coe_add (x y : S) : (↑(x + y) : A) = ↑x + ↑y := rfl
@[simp, norm_cast] lemma coe_mul (x y : S) : (↑(x * y) : A) = ↑x * ↑y := rfl
@[simp, norm_cast] lemma coe_zero : ((0 : S) : A) = 0 := rfl
@[simp, norm_cast] lemma coe_one : ((1 : S) : A) = 1 := rfl
@[simp, norm_cast] lemma coe_neg {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} (x : S) : (↑(-x) : A) = -↑x := rfl
@[simp, norm_cast] lemma coe_sub {R : Type u} {A : Type v} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} (x y : S) : (↑(x - y) : A) = ↑x - ↑y := rfl
@[simp, norm_cast] lemma coe_smul [semiring R'] [has_scalar R' R] [module R' A]
  [is_scalar_tower R' R A] (r : R') (x : S) : (↑(r • x) : A) = r • ↑x := rfl
@[simp, norm_cast] lemma coe_algebra_map [comm_semiring R'] [has_scalar R' R] [algebra R' A]
  [is_scalar_tower R' R A] (r : R') :
  ↑(algebra_map R' S r) = algebra_map R' A r := rfl

@[simp, norm_cast] lemma coe_pow (x : S) (n : ℕ) : (↑(x^n) : A) = (↑x)^n :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, ih], },
end

@[simp, norm_cast] lemma coe_eq_zero {x : S} : (x : A) = 0 ↔ x = 0 :=
(subtype.ext_iff.symm : (x : A) = (0 : S) ↔ x = 0)
@[simp, norm_cast] lemma coe_eq_one {x : S} : (x : A) = 1 ↔ x = 1 :=
(subtype.ext_iff.symm : (x : A) = (1 : S) ↔ x = 1)

-- todo: standardize on the names these morphisms
-- compare with submodule.subtype

/-- Embedding of a subalgebra into the algebra. -/
def val : S →ₐ[R] A :=
by refine_struct { to_fun := (coe : S → A) }; intros; refl

@[simp] lemma coe_val : (S.val : S → A) = coe := rfl

lemma val_apply (x : S) : S.val x = (x : A) := rfl

@[simp] lemma to_subsemiring_subtype : S.to_subsemiring.subtype = (S.val : S →+* A) :=
rfl

@[simp] lemma to_subring_subtype {R A : Type*} [comm_ring R] [ring A]
  [algebra R A] (S : subalgebra R A) : S.to_subring.subtype = (S.val : S →+* A) :=
rfl


/-- As submodules, subalgebras are idempotent. -/
@[simp] theorem mul_self : S.to_submodule * S.to_submodule = S.to_submodule :=
begin
  apply le_antisymm,
  { rw submodule.mul_le,
    intros y hy z hz,
    exact mul_mem S hy hz },
  { intros x hx1,
    rw ← mul_one x,
    exact submodule.mul_mem_mul hx1 (one_mem S) }
end

/-- Linear equivalence between `S : submodule R A` and `S`. Though these types are equal,
we define it as a `linear_equiv` to avoid type equalities. -/
def to_submodule_equiv (S : subalgebra R A) : S.to_submodule ≃ₗ[R] S :=
linear_equiv.of_eq _ _ rfl

/-- Transport a subalgebra via an algebra homomorphism. -/
def map (S : subalgebra R A) (f : A →ₐ[R] B) : subalgebra R B :=
{ algebra_map_mem' := λ r, f.commutes r ▸ set.mem_image_of_mem _ (S.algebra_map_mem r),
  .. S.to_subsemiring.map (f : A →+* B) }

lemma map_mono {S₁ S₂ : subalgebra R A} {f : A →ₐ[R] B} :
  S₁ ≤ S₂ → S₁.map f ≤ S₂.map f :=
set.image_subset f

lemma map_injective {S₁ S₂ : subalgebra R A} (f : A →ₐ[R] B)
  (hf : function.injective f) (ih : S₁.map f = S₂.map f) : S₁ = S₂ :=
ext $ set.ext_iff.1 $ set.image_injective.2 hf $ set.ext $ set_like.ext_iff.mp ih

@[simp] lemma map_id (S : subalgebra R A) : S.map (alg_hom.id R A) = S :=
set_like.coe_injective $ set.image_id _

lemma map_map (S : subalgebra R A) (g : B →ₐ[R] C) (f : A →ₐ[R] B) :
  (S.map f).map g = S.map (g.comp f) :=
set_like.coe_injective $ set.image_image _ _ _

lemma mem_map {S : subalgebra R A} {f : A →ₐ[R] B} {y : B} :
  y ∈ map S f ↔ ∃ x ∈ S, f x = y :=
subsemiring.mem_map

lemma map_to_submodule {S : subalgebra R A} {f : A →ₐ[R] B} :
  (S.map f).to_submodule = S.to_submodule.map f.to_linear_map :=
set_like.coe_injective rfl

lemma map_to_subsemiring {S : subalgebra R A} {f : A →ₐ[R] B} :
  (S.map f).to_subsemiring = S.to_subsemiring.map f.to_ring_hom :=
set_like.coe_injective rfl

@[simp] lemma coe_map (S : subalgebra R A) (f : A →ₐ[R] B) :
  (S.map f : set B) = f '' S :=
rfl

/-- Preimage of a subalgebra under an algebra homomorphism. -/
def comap' (S : subalgebra R B) (f : A →ₐ[R] B) : subalgebra R A :=
{ algebra_map_mem' := λ r, show f (algebra_map R A r) ∈ S,
    from (f.commutes r).symm ▸ S.algebra_map_mem r,
  .. S.to_subsemiring.comap (f : A →+* B) }

theorem map_le {S : subalgebra R A} {f : A →ₐ[R] B} {U : subalgebra R B} :
  map S f ≤ U ↔ S ≤ comap' U f :=
set.image_subset_iff

lemma gc_map_comap (f : A →ₐ[R] B) : galois_connection (λ S, map S f) (λ S, comap' S f) :=
λ S U, map_le

@[simp] lemma mem_comap (S : subalgebra R B) (f : A →ₐ[R] B) (x : A) :
  x ∈ S.comap' f ↔ f x ∈ S :=
iff.rfl

@[simp, norm_cast] lemma coe_comap (S : subalgebra R B) (f : A →ₐ[R] B) :
  (S.comap' f : set A) = f ⁻¹' (S : set B) :=
rfl

instance no_zero_divisors {R A : Type*} [comm_ring R] [semiring A] [no_zero_divisors A]
  [algebra R A] (S : subalgebra R A) : no_zero_divisors S :=
S.to_subsemiring.no_zero_divisors

instance is_domain {R A : Type*} [comm_ring R] [ring A] [is_domain A] [algebra R A]
  (S : subalgebra R A) : is_domain S :=
subring.is_domain S.to_subring

end subalgebra

namespace alg_hom

variables {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}
variables [comm_semiring R]
variables [semiring A] [algebra R A] [semiring B] [algebra R B] [semiring C] [algebra R C]
variables (φ : A →ₐ[R] B)

/-- Range of an `alg_hom` as a subalgebra. -/
protected def range (φ : A →ₐ[R] B) : subalgebra R B :=
{ algebra_map_mem' := λ r, ⟨algebra_map R A r, φ.commutes r⟩,
  .. φ.to_ring_hom.srange }

@[simp] lemma mem_range (φ : A →ₐ[R] B) {y : B} :
  y ∈ φ.range ↔ ∃ x, φ x = y := ring_hom.mem_srange

theorem mem_range_self (φ : A →ₐ[R] B) (x : A) : φ x ∈ φ.range := φ.mem_range.2 ⟨x, rfl⟩

@[simp] lemma coe_range (φ : A →ₐ[R] B) : (φ.range : set B) = set.range φ :=
by { ext, rw [set_like.mem_coe, mem_range], refl }

theorem range_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range = f.range.map g :=
set_like.coe_injective (set.range_comp g f)

theorem range_comp_le_range (f : A →ₐ[R] B) (g : B →ₐ[R] C) : (g.comp f).range ≤ g.range :=
set_like.coe_mono (set.range_comp_subset_range f g)

/-- Restrict the codomain of an algebra homomorphism. -/
def cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) : A →ₐ[R] S :=
{ commutes' := λ r, subtype.eq $ f.commutes r,
  .. ring_hom.cod_srestrict (f : A →+* B) S.to_subsemiring hf }

@[simp] lemma val_comp_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) :
  S.val.comp (f.cod_restrict S hf) = f :=
alg_hom.ext $ λ _, rfl

@[simp] lemma coe_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) (x : A) :
  ↑(f.cod_restrict S hf x) = f x := rfl

theorem injective_cod_restrict (f : A →ₐ[R] B) (S : subalgebra R B) (hf : ∀ x, f x ∈ S) :
  function.injective (f.cod_restrict S hf) ↔ function.injective f :=
⟨λ H x y hxy, H $ subtype.eq hxy, λ H x y hxy, H (congr_arg subtype.val hxy : _)⟩

/-- Restrict the codomain of a alg_hom `f` to `f.range`.

This is the bundled version of `set.range_factorization`. -/
@[reducible] def range_restrict (f : A →ₐ[R] B) : A →ₐ[R] f.range :=
f.cod_restrict f.range f.mem_range_self

/-- The equalizer of two R-algebra homomorphisms -/
def equalizer (ϕ ψ : A →ₐ[R] B) : subalgebra R A :=
{ carrier := {a | ϕ a = ψ a},
  add_mem' := λ x y (hx : ϕ x = ψ x) (hy : ϕ y = ψ y),
    by rw [set.mem_set_of_eq, ϕ.map_add, ψ.map_add, hx, hy],
  mul_mem' := λ x y (hx : ϕ x = ψ x) (hy : ϕ y = ψ y),
    by rw [set.mem_set_of_eq, ϕ.map_mul, ψ.map_mul, hx, hy],
  algebra_map_mem' := λ x,
    by rw [set.mem_set_of_eq, alg_hom.commutes, alg_hom.commutes] }

@[simp] lemma mem_equalizer (ϕ ψ : A →ₐ[R] B) (x : A) :
  x ∈ ϕ.equalizer ψ ↔ ϕ x = ψ x := iff.rfl

/-- The range of a morphism of algebras is a fintype, if the domain is a fintype.

Note that this instance can cause a diamond with `subtype.fintype` if `B` is also a fintype. -/
instance fintype_range [fintype A] [decidable_eq B] (φ : A →ₐ[R] B) : fintype φ.range :=
set.fintype_range φ

end alg_hom

namespace alg_equiv

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

/-- Restrict an algebra homomorphism with a left inverse to an algebra isomorphism to its range.

This is a computable alternative to `alg_equiv.of_injective`. -/
def of_left_inverse
  {g : B → A} {f : A →ₐ[R] B} (h : function.left_inverse g f) :
  A ≃ₐ[R] f.range :=
{ to_fun := f.range_restrict,
  inv_fun := g ∘ f.range.val,
  left_inv := h,
  right_inv := λ x, subtype.ext $
    let ⟨x', hx'⟩ := f.mem_range.mp x.prop in
    show f (g x) = x, by rw [←hx', h x'],
  ..f.range_restrict }

@[simp] lemma of_left_inverse_apply
  {g : B → A} {f : A →ₐ[R] B} (h : function.left_inverse g f) (x : A) :
  ↑(of_left_inverse h x) = f x := rfl

@[simp] lemma of_left_inverse_symm_apply
  {g : B → A} {f : A →ₐ[R] B} (h : function.left_inverse g f) (x : f.range) :
  (of_left_inverse h).symm x = g x := rfl

/-- Restrict an injective algebra homomorphism to an algebra isomorphism -/
noncomputable def of_injective (f : A →ₐ[R] B) (hf : function.injective f) :
  A ≃ₐ[R] f.range :=
of_left_inverse (classical.some_spec hf.has_left_inverse)

@[simp] lemma of_injective_apply (f : A →ₐ[R] B) (hf : function.injective f) (x : A) :
  ↑(of_injective f hf x) = f x := rfl

/-- Restrict an algebra homomorphism between fields to an algebra isomorphism -/
noncomputable def of_injective_field {E F : Type*} [division_ring E] [semiring F]
  [nontrivial F] [algebra R E] [algebra R F] (f : E →ₐ[R] F) : E ≃ₐ[R] f.range :=
of_injective f f.to_ring_hom.injective

/-- Given an equivalence `e : A ≃ₐ[R] B` of `R`-algebras and a subalgebra `S` of `A`,
`subalgebra_map` is the induced equivalence between `S` and `S.map e` -/
@[simps] def subalgebra_map (e : A ≃ₐ[R] B) (S : subalgebra R A) :
  S ≃ₐ[R] (S.map e.to_alg_hom) :=
{ commutes' := λ r, by { ext, simp },
  ..e.to_ring_equiv.subsemiring_map S.to_subsemiring }

end alg_equiv

namespace algebra

variables (R : Type u) {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- The minimal subalgebra that includes `s`. -/
def adjoin (s : set A) : subalgebra R A :=
{ algebra_map_mem' := λ r, subsemiring.subset_closure $ or.inl ⟨r, rfl⟩,
  .. subsemiring.closure (set.range (algebra_map R A) ∪ s) }
variables {R}

protected lemma gc : galois_connection (adjoin R : set A → subalgebra R A) coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) subsemiring.subset_closure) H,
λ H, show subsemiring.closure (set.range (algebra_map R A) ∪ s) ≤ S.to_subsemiring,
     from subsemiring.closure_le.2 $ set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
protected def gi : galois_insertion (adjoin R : set A → subalgebra R A) coe :=
{ choice := λ s hs, (adjoin R s).copy s $ le_antisymm (algebra.gc.le_u_l s) hs,
  gc := algebra.gc,
  le_l_u := λ S, (algebra.gc (S : set A) (adjoin R S)).1 $ le_rfl,
  choice_eq := λ _ _, subalgebra.copy_eq _ _ _ }

instance : complete_lattice (subalgebra R A) :=
galois_insertion.lift_complete_lattice algebra.gi

@[simp]
lemma coe_top : (↑(⊤ : subalgebra R A) : set A) = set.univ := rfl

@[simp] lemma mem_top {x : A} : x ∈ (⊤ : subalgebra R A) :=
set.mem_univ x

@[simp] lemma top_to_submodule : (⊤ : subalgebra R A).to_submodule = ⊤ := rfl

@[simp] lemma top_to_subsemiring : (⊤ : subalgebra R A).to_subsemiring = ⊤ := rfl

@[simp] lemma top_to_subring {R A : Type*} [comm_ring R] [ring A] [algebra R A] :
  (⊤ : subalgebra R A).to_subring = ⊤ := rfl

@[simp] lemma to_submodule_eq_top {S : subalgebra R A} : S.to_submodule = ⊤ ↔ S = ⊤ :=
subalgebra.to_submodule_injective.eq_iff' top_to_submodule

@[simp] lemma to_subsemiring_eq_top {S : subalgebra R A} : S.to_subsemiring = ⊤ ↔ S = ⊤ :=
subalgebra.to_subsemiring_injective.eq_iff' top_to_subsemiring

@[simp] lemma to_subring_eq_top {R A : Type*} [comm_ring R] [ring A] [algebra R A]
  {S : subalgebra R A} : S.to_subring = ⊤ ↔ S = ⊤ :=
subalgebra.to_subring_injective.eq_iff' top_to_subring

lemma mem_sup_left {S T : subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

lemma mem_sup_right {S T : subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

lemma mul_mem_sup {S T : subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
  x * y ∈ S ⊔ T :=
(S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

lemma map_sup (f : A →ₐ[R] B) (S T : subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
(subalgebra.gc_map_comap f).l_sup

@[simp, norm_cast]
lemma coe_inf (S T : subalgebra R A) : (↑(S ⊓ T) : set A) = S ∩ T := rfl

@[simp]
lemma mem_inf {S T : subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := iff.rfl

@[simp] lemma inf_to_submodule (S T : subalgebra R A) :
  (S ⊓ T).to_submodule = S.to_submodule ⊓ T.to_submodule := rfl

@[simp] lemma inf_to_subsemiring (S T : subalgebra R A) :
  (S ⊓ T).to_subsemiring = S.to_subsemiring ⊓ T.to_subsemiring := rfl

@[simp, norm_cast]
lemma coe_Inf (S : set (subalgebra R A)) : (↑(Inf S) : set A) = ⋂ s ∈ S, ↑s := Inf_image

lemma mem_Inf {S : set (subalgebra R A)} {x : A} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
by simp only [← set_like.mem_coe, coe_Inf, set.mem_Inter₂]

@[simp] lemma Inf_to_submodule (S : set (subalgebra R A)) :
  (Inf S).to_submodule = Inf (subalgebra.to_submodule '' S) :=
set_like.coe_injective $ by simp

@[simp] lemma Inf_to_subsemiring (S : set (subalgebra R A)) :
  (Inf S).to_subsemiring = Inf (subalgebra.to_subsemiring '' S) :=
set_like.coe_injective $ by simp

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → subalgebra R A} : (↑(⨅ i, S i) : set A) = ⋂ i, S i :=
by simp [infi]

lemma mem_infi {ι : Sort*} {S : ι → subalgebra R A} {x : A} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp] lemma infi_to_submodule {ι : Sort*} (S : ι → subalgebra R A) :
  (⨅ i, S i).to_submodule = ⨅ i, (S i).to_submodule :=
set_like.coe_injective $ by simp

instance : inhabited (subalgebra R A) := ⟨⊥⟩

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra R A) ↔ x ∈ set.range (algebra_map R A) :=
suffices (of_id R A).range = (⊥ : subalgebra R A),
by { rw [← this, ←set_like.mem_coe, alg_hom.coe_range], refl },
le_bot_iff.mp (λ x hx, subalgebra.range_le _ ((of_id R A).coe_range ▸ hx))

theorem to_submodule_bot : (⊥ : subalgebra R A).to_submodule = R ∙ 1 :=
by { ext x, simp [mem_bot, -set.singleton_one, submodule.mem_span_singleton, algebra.smul_def] }

@[simp] theorem coe_bot : ((⊥ : subalgebra R A) : set A) = set.range (algebra_map R A) :=
by simp [set.ext_iff, algebra.mem_bot]

theorem eq_top_iff {S : subalgebra R A} :
  S = ⊤ ↔ ∀ x : A, x ∈ S :=
⟨λ h x, by rw h; exact mem_top, λ h, by ext x; exact ⟨λ _, mem_top, λ _, h x⟩⟩

@[simp] theorem range_id : (alg_hom.id R A).range = ⊤ :=
set_like.coe_injective set.range_id

@[simp] theorem map_top (f : A →ₐ[R] B) : subalgebra.map (⊤ : subalgebra R A) f = f.range :=
set_like.coe_injective set.image_univ

@[simp] theorem map_bot (f : A →ₐ[R] B) : subalgebra.map (⊥ : subalgebra R A) f = ⊥ :=
set_like.coe_injective $
  by simp only [← set.range_comp, (∘), algebra.coe_bot, subalgebra.coe_map, f.commutes]

@[simp] theorem comap_top (f : A →ₐ[R] B) : subalgebra.comap' (⊤ : subalgebra R B) f = ⊤ :=
eq_top_iff.2 $ λ x, mem_top

/-- `alg_hom` to `⊤ : subalgebra R A`. -/
def to_top : A →ₐ[R] (⊤ : subalgebra R A) :=
(alg_hom.id R A).cod_restrict ⊤ (λ _, mem_top)

theorem surjective_algebra_map_iff :
  function.surjective (algebra_map R A) ↔ (⊤ : subalgebra R A) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ λ y _, let ⟨x, hx⟩ := h y in hx ▸ subalgebra.algebra_map_mem _ _,
λ h y, algebra.mem_bot.1 $ eq_bot_iff.1 h (algebra.mem_top : y ∈ _)⟩

theorem bijective_algebra_map_iff {R A : Type*} [field R] [semiring A] [nontrivial A]
  [algebra R A] :
  function.bijective (algebra_map R A) ↔ (⊤ : subalgebra R A) = ⊥ :=
⟨λ h, surjective_algebra_map_iff.1 h.2,
λ h, ⟨(algebra_map R A).injective, surjective_algebra_map_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
noncomputable def bot_equiv_of_injective (h : function.injective (algebra_map R A)) :
  (⊥ : subalgebra R A) ≃ₐ[R] R :=
alg_equiv.symm $ alg_equiv.of_bijective (algebra.of_id R _)
⟨λ x y hxy, h (congr_arg subtype.val hxy : _),
 λ ⟨y, hy⟩, let ⟨x, hx⟩ := algebra.mem_bot.1 hy in ⟨x, subtype.eq hx⟩⟩

/-- The bottom subalgebra is isomorphic to the field. -/
@[simps symm_apply]
noncomputable def bot_equiv (F R : Type*) [field F] [semiring R] [nontrivial R] [algebra F R] :
  (⊥ : subalgebra F R) ≃ₐ[F] F :=
bot_equiv_of_injective (ring_hom.injective _)

/-- The top subalgebra is isomorphic to the field. -/
@[simps] def top_equiv : (⊤ : subalgebra R A) ≃ₐ[R] A :=
alg_equiv.of_alg_hom (subalgebra.val ⊤) to_top rfl $ alg_hom.ext $ λ x, subtype.ext rfl

end algebra

namespace subalgebra
open algebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]
variables (S : subalgebra R A)

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_subsingleton [subsingleton A] : subsingleton (subalgebra R A) :=
⟨λ B C, ext (λ x, by { simp only [subsingleton.elim x 0, zero_mem] })⟩

/--
For performance reasons this is not an instance. If you need this instance, add
```
local attribute [instance] alg_hom.subsingleton subalgebra.subsingleton_of_subsingleton
```
in the section that needs it.
-/
-- TODO[gh-6025]: make this an instance once safe to do so
lemma _root_.alg_hom.subsingleton [subsingleton (subalgebra R A)] : subsingleton (A →ₐ[R] B) :=
⟨λ f g, alg_hom.ext $ λ a,
  have a ∈ (⊥ : subalgebra R A) := subsingleton.elim (⊤ : subalgebra R A) ⊥ ▸ mem_top,
  let ⟨x, hx⟩ := set.mem_range.mp (mem_bot.mp this) in
  hx ▸ (f.commutes _).trans (g.commutes _).symm⟩

-- TODO[gh-6025]: make this an instance once safe to do so
lemma _root_.alg_equiv.subsingleton_left [subsingleton (subalgebra R A)] :
  subsingleton (A ≃ₐ[R] B) :=
begin
  haveI : subsingleton (A →ₐ[R] B) := alg_hom.subsingleton,
  exact ⟨λ f g, alg_equiv.ext
    (λ x, alg_hom.ext_iff.mp (subsingleton.elim f.to_alg_hom g.to_alg_hom) x)⟩,
end

-- TODO[gh-6025]: make this an instance once safe to do so
lemma _root_.alg_equiv.subsingleton_right [subsingleton (subalgebra R B)] :
  subsingleton (A ≃ₐ[R] B) :=
begin
  haveI : subsingleton (B ≃ₐ[R] A) := alg_equiv.subsingleton_left,
  exact ⟨λ f g, eq.trans (alg_equiv.symm_symm _).symm
    (by rw [subsingleton.elim f.symm g.symm, alg_equiv.symm_symm])⟩
end

lemma range_val : S.val.range = S :=
ext $ set.ext_iff.1 $ S.val.coe_range.trans subtype.range_val

instance : unique (subalgebra R R) :=
{ uniq :=
  begin
    intro S,
    refine le_antisymm (λ r hr, _) bot_le,
    simp only [set.mem_range, mem_bot, id.map_eq_self, exists_apply_eq_apply, default],
  end
  .. algebra.subalgebra.inhabited }

/-- The map `S → T` when `S` is a subalgebra contained in the subalgebra `T`.

This is the subalgebra version of `submodule.of_le`, or `subring.inclusion`  -/
def inclusion {S T : subalgebra R A} (h : S ≤ T) : S →ₐ[R] T :=
{ to_fun := set.inclusion h,
  map_one' := rfl,
  map_add' := λ _ _, rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  commutes' := λ _, rfl }

lemma inclusion_injective {S T : subalgebra R A} (h : S ≤ T) :
  function.injective (inclusion h) :=
λ _ _, subtype.ext ∘ subtype.mk.inj

@[simp] lemma inclusion_self {S : subalgebra R A}:
  inclusion (le_refl S) = alg_hom.id R S :=
alg_hom.ext $ λ x, subtype.ext rfl

@[simp] lemma inclusion_right {S T : subalgebra R A} (h : S ≤ T) (x : T)
  (m : (x : A) ∈ S) : inclusion h ⟨x, m⟩ = x := subtype.ext rfl

@[simp] lemma inclusion_inclusion {S T U : subalgebra R A} (hst : S ≤ T) (htu : T ≤ U)
  (x : S) : inclusion htu (inclusion hst x) = inclusion (le_trans hst htu) x :=
subtype.ext rfl

@[simp] lemma coe_inclusion {S T : subalgebra R A} (h : S ≤ T) (s : S) :
  (inclusion h s : A) = s := rfl

/-- Two subalgebras that are equal are also equivalent as algebras.

This is the `subalgebra` version of `linear_equiv.of_eq` and `equiv.set.of_eq`. -/
@[simps apply]
def equiv_of_eq (S T : subalgebra R A) (h : S = T) : S ≃ₐ[R] T :=
{ to_fun := λ x, ⟨x, h ▸ x.2⟩,
  inv_fun := λ x, ⟨x, h.symm ▸ x.2⟩,
  map_mul' := λ _ _, rfl,
  commutes' := λ _, rfl,
  .. linear_equiv.of_eq _ _ (congr_arg to_submodule h) }

@[simp] lemma equiv_of_eq_symm (S T : subalgebra R A) (h : S = T) :
  (equiv_of_eq S T h).symm = equiv_of_eq T S h.symm :=
rfl

@[simp] lemma equiv_of_eq_rfl (S : subalgebra R A) :
  equiv_of_eq S S rfl = alg_equiv.refl :=
by { ext, refl }

@[simp] lemma equiv_of_eq_trans (S T U : subalgebra R A) (hST : S = T) (hTU : T = U) :
  (equiv_of_eq S T hST).trans (equiv_of_eq T U hTU) = equiv_of_eq S U (trans hST hTU) :=
rfl

section prod

variables (S₁ : subalgebra R B)

/-- The product of two subalgebras is a subalgebra. -/
def prod : subalgebra R (A × B) :=
{ carrier := (S : set A) ×ˢ (S₁ : set B),
  algebra_map_mem' := λ r, ⟨algebra_map_mem _ _, algebra_map_mem _ _⟩,
  .. S.to_subsemiring.prod S₁.to_subsemiring }

@[simp] lemma coe_prod :
  (prod S S₁ : set (A × B)) = (S : set A) ×ˢ (S₁ : set B):= rfl

lemma prod_to_submodule :
  (S.prod S₁).to_submodule = S.to_submodule.prod S₁.to_submodule := rfl

@[simp] lemma mem_prod {S : subalgebra R A} {S₁ : subalgebra R B} {x : A × B} :
  x ∈ prod S S₁ ↔ x.1 ∈ S ∧ x.2 ∈ S₁ := set.mem_prod

@[simp] lemma prod_top : (prod ⊤ ⊤ : subalgebra R (A × B)) = ⊤ :=
by ext; simp

lemma prod_mono {S T : subalgebra R A} {S₁ T₁ : subalgebra R B} :
  S ≤ T → S₁ ≤ T₁ → prod S S₁ ≤ prod T T₁ := set.prod_mono

@[simp] lemma prod_inf_prod {S T : subalgebra R A} {S₁ T₁ : subalgebra R B} :
  S.prod S₁ ⊓ T.prod T₁ = (S ⊓ T).prod (S₁ ⊓ T₁) :=
set_like.coe_injective set.prod_inter_prod

end prod

section supr_lift
variables {ι : Type*}

lemma coe_supr_of_directed [nonempty ι] {S : ι → subalgebra R A}
  (dir : directed (≤) S) : ↑(supr S) = ⋃ i, (S i : set A) :=
let K : subalgebra R A :=
  { carrier := ⋃ i, (S i),
    mul_mem' := λ x y hx hy,
      let ⟨i, hi⟩ := set.mem_Union.1 hx in
      let ⟨j, hj⟩ := set.mem_Union.1 hy in
      let ⟨k, hik, hjk⟩ := dir i j in
      set.mem_Union.2 ⟨k, subalgebra.mul_mem (S k) (hik hi) (hjk hj)⟩ ,
    add_mem' := λ x y hx hy,
      let ⟨i, hi⟩ := set.mem_Union.1 hx in
      let ⟨j, hj⟩ := set.mem_Union.1 hy in
      let ⟨k, hik, hjk⟩ := dir i j in
      set.mem_Union.2 ⟨k, subalgebra.add_mem (S k) (hik hi) (hjk hj)⟩,
    algebra_map_mem' := λ r, let i := @nonempty.some ι infer_instance in
      set.mem_Union.2 ⟨i, subalgebra.algebra_map_mem _ _⟩ } in
have supr S = K,
  from le_antisymm (supr_le (λ i, set.subset_Union (λ i, ↑(S i)) i))
    (set_like.coe_subset_coe.1
      (set.Union_subset (λ i, set_like.coe_subset_coe.2 (le_supr _ _)))),
this.symm ▸ rfl

/-- Define an algebra homomorphism on a directed supremum of subalgebras by defining
it on each subalgebra, and proving that it agrees on the intersection of subalgebras. -/
noncomputable def supr_lift [nonempty ι]
  (K : ι → subalgebra R A)
  (dir : directed (≤) K)
  (f : Π i, K i →ₐ[R] B)
  (hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h))
  (T : subalgebra R A) (hT : T = supr K) :
  ↥T →ₐ[R] B :=
by subst hT; exact
{ to_fun := set.Union_lift (λ i, ↑(K i)) (λ i x, f i x)
    (λ i j x hxi hxj,
      let ⟨k, hik, hjk⟩ := dir i j in
      begin
        rw [hf i k hik, hf j k hjk],
        refl
      end) ↑(supr K)
    (by rw coe_supr_of_directed dir; refl),
  map_one' := set.Union_lift_const _ (λ _, 1) (λ _, rfl) _ (by simp),
  map_zero' := set.Union_lift_const _ (λ _, 0) (λ _, rfl) _ (by simp),
  map_mul' := set.Union_lift_binary (coe_supr_of_directed dir) dir _
    (λ _, (*)) (λ _ _ _, rfl) _ (by simp),
  map_add' := set.Union_lift_binary (coe_supr_of_directed dir) dir _
    (λ _, (+)) (λ _ _ _, rfl) _ (by simp),
  commutes' := λ r, set.Union_lift_const _ (λ _, algebra_map _ _ r)
    (λ _, rfl) _ (λ i, by erw [alg_hom.commutes (f i)]) }

variables [nonempty ι] {K : ι → subalgebra R A} {dir : directed (≤) K}
  {f : Π i, K i →ₐ[R] B}
  {hf : ∀ (i j : ι) (h : K i ≤ K j), f i = (f j).comp (inclusion h)}
  {T : subalgebra R A} {hT : T = supr K}

@[simp] lemma supr_lift_inclusion {i : ι} (x : K i) (h : K i ≤ T) :
  supr_lift K dir f hf T hT (inclusion h x) = f i x :=
by subst T; exact set.Union_lift_inclusion _ _

@[simp] lemma supr_lift_comp_inclusion {i : ι} (h : K i ≤ T) :
  (supr_lift K dir f hf T hT).comp (inclusion h) = f i :=
by ext; simp

@[simp] lemma supr_lift_mk {i : ι} (x : K i) (hx : (x : A) ∈ T) :
  supr_lift K dir f hf T hT ⟨x, hx⟩ = f i x :=
by subst hT; exact set.Union_lift_mk x hx

lemma supr_lift_of_mem {i : ι} (x : T) (hx : (x : A) ∈ K i) :
  supr_lift K dir f hf T hT x = f i ⟨x, hx⟩ :=
by subst hT; exact set.Union_lift_of_mem x hx

end supr_lift

/-! ## Actions by `subalgebra`s

These are just copies of the definitions about `subsemiring` starting from
`subring.mul_action`.
-/
section actions

variables {α β : Type*}

/-- The action by a subalgebra is the action by the underlying ring. -/
instance [mul_action A α] (S : subalgebra R A) : mul_action S α :=
S.to_subsemiring.mul_action

lemma smul_def [mul_action A α] {S : subalgebra R A} (g : S) (m : α) : g • m = (g : A) • m := rfl

instance smul_comm_class_left
  [mul_action A β] [has_scalar α β] [smul_comm_class A α β] (S : subalgebra R A) :
  smul_comm_class S α β :=
S.to_subsemiring.smul_comm_class_left

instance smul_comm_class_right
  [has_scalar α β] [mul_action A β] [smul_comm_class α A β] (S : subalgebra R A) :
  smul_comm_class α S β :=
S.to_subsemiring.smul_comm_class_right

/-- Note that this provides `is_scalar_tower S R R` which is needed by `smul_mul_assoc`. -/
instance is_scalar_tower_left
  [has_scalar α β] [mul_action A α] [mul_action A β] [is_scalar_tower A α β] (S : subalgebra R A) :
  is_scalar_tower S α β :=
S.to_subsemiring.is_scalar_tower

instance [mul_action A α] [has_faithful_scalar A α] (S : subalgebra R A) :
  has_faithful_scalar S α :=
S.to_subsemiring.has_faithful_scalar

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance [add_monoid α] [distrib_mul_action A α] (S : subalgebra R A) : distrib_mul_action S α :=
S.to_subsemiring.distrib_mul_action

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance module_left [add_comm_monoid α] [module A α] (S : subalgebra R A) : module S α :=
S.to_subsemiring.module

/-- The action by a subalgebra is the action by the underlying algebra. -/
instance to_algebra {R A : Type*} [comm_semiring R] [comm_semiring A] [semiring α]
  [algebra R A] [algebra A α] (S : subalgebra R A) : algebra S α :=
algebra.of_subsemiring S.to_subsemiring

lemma algebra_map_eq {R A : Type*} [comm_semiring R] [comm_semiring A] [semiring α]
  [algebra R A] [algebra A α] (S : subalgebra R A) :
  algebra_map S α = (algebra_map A α).comp S.val := rfl

@[simp] lemma srange_algebra_map {R A : Type*} [comm_semiring R] [comm_semiring A]
  [algebra R A] (S : subalgebra R A) :
  (algebra_map S A).srange = S.to_subsemiring :=
by rw [algebra_map_eq, algebra.id.map_eq_id, ring_hom.id_comp, ← to_subsemiring_subtype,
       subsemiring.srange_subtype]

@[simp] lemma range_algebra_map {R A : Type*} [comm_ring R] [comm_ring A]
  [algebra R A] (S : subalgebra R A) :
  (algebra_map S A).range = S.to_subring :=
by rw [algebra_map_eq, algebra.id.map_eq_id, ring_hom.id_comp, ← to_subring_subtype,
       subring.range_subtype]

instance no_zero_smul_divisors_top [no_zero_divisors A] (S : subalgebra R A) :
  no_zero_smul_divisors S A :=
⟨λ c x h,
  have (c : A) = 0 ∨ x = 0,
  from eq_zero_or_eq_zero_of_mul_eq_zero h,
  this.imp_left (@subtype.ext_iff _ _ c 0).mpr⟩

end actions

section pointwise
variables {R' : Type*} [semiring R'] [mul_semiring_action R' A] [smul_comm_class R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : mul_action R' (subalgebra R A) :=
{ smul := λ a S, S.map (mul_semiring_action.to_alg_hom _ _ a),
  one_smul := λ S,
    (congr_arg (λ f, S.map f) (alg_hom.ext $ by exact one_smul R')).trans S.map_id,
  mul_smul := λ a₁ a₂ S,
    (congr_arg (λ f, S.map f) (alg_hom.ext $ by exact mul_smul _ _)).trans (S.map_map _ _).symm }

localized "attribute [instance] subalgebra.pointwise_mul_action" in pointwise
open_locale pointwise

@[simp] lemma coe_pointwise_smul (m : R') (S : subalgebra R A) : ↑(m • S) = m • (S : set A) := rfl

@[simp] lemma pointwise_smul_to_subsemiring (m : R') (S : subalgebra R A) :
  (m • S).to_subsemiring = m • S.to_subsemiring := rfl

@[simp] lemma pointwise_smul_to_submodule (m : R') (S : subalgebra R A) :
  (m • S).to_submodule = m • S.to_submodule := rfl

@[simp] lemma pointwise_smul_to_subring {R' R A : Type*} [semiring R'] [comm_ring R] [ring A]
  [mul_semiring_action R' A] [algebra R A] [smul_comm_class R' R A] (m : R') (S : subalgebra R A) :
  (m • S).to_subring = m • S.to_subring := rfl

lemma smul_mem_pointwise_smul (m : R') (r : A) (S : subalgebra R A) : r ∈ S → m • r ∈ m • S :=
(set.smul_mem_smul_set : _ → _ ∈ m • (S : set A))

end pointwise

section center

lemma _root_.set.algebra_map_mem_center (r : R) : algebra_map R A r ∈ set.center A :=
by simp [algebra.commutes, set.mem_center_iff]

variables (R A)

/-- The center of an algebra is the set of elements which commute with every element. They form a
subalgebra. -/
def center : subalgebra R A :=
{ algebra_map_mem' := set.algebra_map_mem_center,
  .. subsemiring.center A }

lemma coe_center : (center R A : set A) = set.center A := rfl

@[simp] lemma center_to_subsemiring :
  (center R A).to_subsemiring = subsemiring.center A :=
rfl

@[simp] lemma center_to_subring (R A : Type*) [comm_ring R] [ring A] [algebra R A] :
  (center R A).to_subring = subring.center A :=
rfl

@[simp] lemma center_eq_top (A : Type*) [comm_semiring A] [algebra R A] : center R A = ⊤ :=
set_like.coe_injective (set.center_eq_univ A)

variables {R A}

instance : comm_semiring (center R A) := subsemiring.center.comm_semiring

instance {A : Type*} [ring A] [algebra R A] : comm_ring (center R A) := subring.center.comm_ring

lemma mem_center_iff {a : A} : a ∈ center R A ↔ ∀ (b : A), b*a = a*b := iff.rfl

end center

end subalgebra

section nat

variables {R : Type*} [semiring R]

/-- A subsemiring is a `ℕ`-subalgebra. -/
def subalgebra_of_subsemiring (S : subsemiring R) : subalgebra ℕ R :=
{ algebra_map_mem' := λ i, S.coe_nat_mem i,
  .. S }

@[simp] lemma mem_subalgebra_of_subsemiring {x : R} {S : subsemiring R} :
  x ∈ subalgebra_of_subsemiring S ↔ x ∈ S :=
iff.rfl

end nat

section int

variables {R : Type*} [ring R]

/-- A subring is a `ℤ`-subalgebra. -/
def subalgebra_of_subring (S : subring R) : subalgebra ℤ R :=
{ algebra_map_mem' := λ i, int.induction_on i S.zero_mem
  (λ i ih, S.add_mem ih S.one_mem)
  (λ i ih, show ((-i - 1 : ℤ) : R) ∈ S, by { rw [int.cast_sub, int.cast_one],
    exact S.sub_mem ih S.one_mem }),
  .. S }

variables {S : Type*} [semiring S]

@[simp] lemma mem_subalgebra_of_subring {x : R} {S : subring R} :
  x ∈ subalgebra_of_subring S ↔ x ∈ S :=
iff.rfl

end int
