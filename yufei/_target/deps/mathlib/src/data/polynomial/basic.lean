/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import algebra.monoid_algebra.basic

/-!
# Theory of univariate polynomials

This file defines `polynomial R`, the type of univariate polynomials over the semiring `R`, builds
a semiring structure on it, and gives basic definitions that are expanded in other files in this
directory.

## Main definitions

* `monomial n a` is the polynomial `a X^n`. Note that `monomial n` is defined as an `R`-linear map.
* `C a` is the constant polynomial `a`. Note that `C` is defined as a ring homomorphism.
* `X` is the polynomial `X`, i.e., `monomial 1 1`.
* `p.sum f` is `∑ n in p.support, f n (p.coeff n)`, i.e., one sums the values of functions applied
  to coefficients of the polynomial `p`.
* `p.erase n` is the polynomial `p` in which one removes the `c X^n` term.

There are often two natural variants of lemmas involving sums, depending on whether one acts on the
polynomials, or on the function. The naming convention is that one adds `index` when acting on
the polynomials. For instance,
* `sum_add_index` states that `(p + q).sum f = p.sum f + q.sum f`;
* `sum_add` states that `p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g`.
* Notation to refer to `polynomial R`, as `R[X]` or `R[t]`.

## Implementation

Polynomials are defined using `add_monoid_algebra R ℕ`, where `R` is a commutative semiring, but
through a structure to make them irreducible from the point of view of the kernel. Most operations
are irreducible since Lean can not compute anyway with `add_monoid_algebra`. There are two
exceptions that we make semireducible:
* The zero polynomial, so that its coefficients are definitionally equal to `0`.
* The scalar action, to permit typeclass search to unfold it to resolve potential instance
  diamonds.

The raw implementation of the equivalence between `polynomial R` and `add_monoid_algebra R ℕ` is
done through `of_finsupp` and `to_finsupp` (or, equivalently, `rcases p` when `p` is a polynomial
gives an element `q` of `add_monoid_algebra R ℕ`, and conversely `⟨q⟩` gives back `p`). The
equivalence is also registered as a ring equiv in `polynomial.to_finsupp_iso`. These should
in general not be used once the basic API for polynomials is constructed.
-/

noncomputable theory

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
structure polynomial (R : Type*) [semiring R] := of_finsupp ::
(to_finsupp : add_monoid_algebra R ℕ)

localized "notation R`[X]`:9000 := polynomial R" in polynomial
open finsupp add_monoid_algebra
open_locale big_operators polynomial

namespace polynomial
universes u
variables {R : Type u} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : R[X]}

lemma forall_iff_forall_finsupp (P : R[X] → Prop) :
  (∀ p, P p) ↔ ∀ (q : add_monoid_algebra R ℕ), P ⟨q⟩ :=
⟨λ h q, h ⟨q⟩, λ h ⟨p⟩, h p⟩

lemma exists_iff_exists_finsupp (P : R[X] → Prop) :
  (∃ p, P p) ↔ ∃ (q : add_monoid_algebra R ℕ), P ⟨q⟩ :=
⟨λ ⟨⟨p⟩, hp⟩, ⟨p, hp⟩, λ ⟨q, hq⟩, ⟨⟨q⟩, hq⟩ ⟩

/-- The function version of `monomial`. Use `monomial` instead of this one. -/
@[irreducible] def monomial_fun (n : ℕ) (a : R) : R[X] := ⟨finsupp.single n a⟩
@[irreducible] private def add : R[X] → R[X] → R[X]
| ⟨a⟩ ⟨b⟩ := ⟨a + b⟩
@[irreducible] private def neg {R : Type u} [ring R] : R[X] → R[X]
| ⟨a⟩ := ⟨-a⟩
@[irreducible] private def mul : R[X] → R[X] → R[X]
| ⟨a⟩ ⟨b⟩ := ⟨a * b⟩

instance : has_zero R[X] := ⟨⟨0⟩⟩
instance : has_one R[X] := ⟨monomial_fun 0 (1 : R)⟩
instance : has_add R[X] := ⟨add⟩
instance {R : Type u} [ring R] : has_neg R[X] := ⟨neg⟩
instance : has_mul R[X] := ⟨mul⟩
instance {S : Type*} [monoid S] [distrib_mul_action S R] : has_scalar S R[X] :=
⟨λ r p, ⟨r • p.to_finsupp⟩⟩

lemma zero_to_finsupp : (⟨0⟩ : R[X]) = 0 :=
rfl

lemma one_to_finsupp : (⟨1⟩ : R[X]) = 1 :=
begin
  change (⟨1⟩ : R[X]) = monomial_fun 0 (1 : R),
  rw [monomial_fun],
  refl
end

lemma add_to_finsupp {a b} : (⟨a⟩ + ⟨b⟩ : R[X]) = ⟨a + b⟩ := show add _ _ = _, by rw add
lemma neg_to_finsupp {R : Type u} [ring R] {a} : (-⟨a⟩ : R[X]) = ⟨-a⟩ :=
show neg _ = _, by rw neg
lemma mul_to_finsupp {a b} : (⟨a⟩ * ⟨b⟩ : R[X]) = ⟨a * b⟩ := show mul _ _ = _, by rw mul
lemma smul_to_finsupp {S : Type*} [monoid S] [distrib_mul_action S R] {a : S} {b} :
  (a • ⟨b⟩ : R[X]) = ⟨a • b⟩ := rfl

lemma _root_.is_smul_regular.polynomial {S : Type*} [monoid S] [distrib_mul_action S R] {a : S}
  (ha : is_smul_regular R a) : is_smul_regular R[X] a
| ⟨x⟩ ⟨y⟩ h := congr_arg _ $ ha.finsupp (polynomial.of_finsupp.inj h)

instance : inhabited R[X] := ⟨0⟩

instance : semiring R[X] :=
by refine_struct
{ zero := (0 : R[X]),
  one := 1,
  mul := (*),
  add := (+),
  nsmul := (•),
  npow := npow_rec,
  npow_zero' := λ x, rfl,
  npow_succ' := λ n x, rfl };
{ repeat { rintro ⟨_⟩, };
  simp [← zero_to_finsupp, ← one_to_finsupp, add_to_finsupp, mul_to_finsupp, mul_assoc, mul_add,
    add_mul, smul_to_finsupp, nat.succ_eq_one_add]; abel }

instance {S} [monoid S] [distrib_mul_action S R] : distrib_mul_action S R[X] :=
{ smul := (•),
  one_smul := by { rintros ⟨⟩, simp [smul_to_finsupp] },
  mul_smul := by { rintros _ _ ⟨⟩, simp [smul_to_finsupp, mul_smul], },
  smul_add := by { rintros _ ⟨⟩ ⟨⟩, simp [smul_to_finsupp, add_to_finsupp] },
  smul_zero := by { rintros _, simp [← zero_to_finsupp, smul_to_finsupp] } }

instance {S} [monoid S] [distrib_mul_action S R] [has_faithful_scalar S R] :
  has_faithful_scalar S R[X] :=
{ eq_of_smul_eq_smul := λ s₁ s₂ h, eq_of_smul_eq_smul $ λ a : ℕ →₀ R, congr_arg to_finsupp (h ⟨a⟩) }

instance {S} [semiring S] [module S R] : module S R[X] :=
{ smul := (•),
  add_smul := by { rintros _ _ ⟨⟩, simp [smul_to_finsupp, add_to_finsupp, add_smul] },
  zero_smul := by { rintros ⟨⟩, simp [smul_to_finsupp, ← zero_to_finsupp] },
  ..polynomial.distrib_mul_action }

instance {S₁ S₂} [monoid S₁] [monoid S₂] [distrib_mul_action S₁ R] [distrib_mul_action S₂ R]
  [smul_comm_class S₁ S₂ R] : smul_comm_class S₁ S₂ R[X] :=
⟨by { rintros _ _ ⟨⟩, simp [smul_to_finsupp, smul_comm] }⟩

instance {S₁ S₂} [has_scalar S₁ S₂] [monoid S₁] [monoid S₂] [distrib_mul_action S₁ R]
  [distrib_mul_action S₂ R] [is_scalar_tower S₁ S₂ R] : is_scalar_tower S₁ S₂ R[X] :=
⟨by { rintros _ _ ⟨⟩, simp [smul_to_finsupp] }⟩

instance {S} [monoid S] [distrib_mul_action S R] [distrib_mul_action Sᵐᵒᵖ R]
  [is_central_scalar S R] : is_central_scalar S R[X] :=
⟨by { rintros _ ⟨⟩, simp [smul_to_finsupp, op_smul_eq_smul] }⟩

instance [subsingleton R] : unique R[X] :=
{ uniq := by { rintros ⟨x⟩, change (⟨x⟩ : R[X]) = 0, rw [← zero_to_finsupp], simp },
.. polynomial.inhabited }

variable (R)

/-- Ring isomorphism between `R[X]` and `add_monoid_algebra R ℕ`. This is just an
implementation detail, but it can be useful to transfer results from `finsupp` to polynomials. -/
@[simps]
def to_finsupp_iso : R[X] ≃+* add_monoid_algebra R ℕ :=
{ to_fun := λ p, p.to_finsupp,
  inv_fun := λ p, ⟨p⟩,
  left_inv := λ ⟨p⟩, rfl,
  right_inv := λ p, rfl,
  map_mul' := by { rintros ⟨⟩ ⟨⟩, simp [mul_to_finsupp] },
  map_add' := by { rintros ⟨⟩ ⟨⟩, simp [add_to_finsupp] } }

/-- Ring isomorphism between `R[X]ᵐᵒᵖ` and `R[X]ᵐᵒᵖ`. -/
@[simps]
def op_ring_equiv : R[X]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[X] :=
((to_finsupp_iso R).op.trans add_monoid_algebra.op_ring_equiv).trans (to_finsupp_iso _).symm

variable {R}

lemma sum_to_finsupp {ι : Type*} (s : finset ι) (f : ι → add_monoid_algebra R ℕ) :
  ∑ i in s, (⟨f i⟩ : R[X]) = ⟨∑ i in s, f i⟩ :=
((to_finsupp_iso R).symm.to_add_monoid_hom.map_sum f s).symm

/--
The set of all `n` such that `X^n` has a non-zero coefficient.
-/
def support : R[X] → finset ℕ
| ⟨p⟩ := p.support

@[simp] lemma support_zero : (0 : R[X]).support = ∅ :=
rfl

@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 :=
by { rcases p, simp [support, ← zero_to_finsupp] }

lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 :=
by simp

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] R[X] :=
{ to_fun := monomial_fun n,
  map_add' := by simp [monomial_fun, add_to_finsupp],
  map_smul' := by simp [monomial_fun, smul_to_finsupp] }

@[simp]
lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
(monomial n).map_zero

-- This is not a `simp` lemma as `monomial_zero_left` is more general.
lemma monomial_zero_one : monomial 0 (1 : R) = 1 := rfl

-- TODO: can't we just delete this one?
lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
(monomial n).map_add _ _

lemma monomial_mul_monomial (n m : ℕ) (r s : R) :
  monomial n r * monomial m s = monomial (n + m) (r * s) :=
by simp only [monomial, monomial_fun, linear_map.coe_mk, mul_to_finsupp,
  add_monoid_algebra.single_mul_single]

@[simp]
lemma monomial_pow (n : ℕ) (r : R) (k : ℕ) :
  (monomial n r)^k = monomial (n*k) (r^k) :=
begin
  induction k with k ih,
  { simp [pow_zero, monomial_zero_one], },
  { simp [pow_succ, ih, monomial_mul_monomial, nat.succ_eq_add_one, mul_add, add_comm] },
end

lemma smul_monomial {S} [monoid S] [distrib_mul_action S R] (a : S) (n : ℕ) (b : R) :
  a • monomial n b = monomial n (a • b) :=
by simp [monomial, monomial_fun, smul_to_finsupp]

@[simp] lemma to_finsupp_iso_monomial : (to_finsupp_iso R) (monomial n a) = single n a :=
by simp [to_finsupp_iso, monomial, monomial_fun]

@[simp] lemma to_finsupp_iso_symm_single : (to_finsupp_iso R).symm (single n a) = monomial n a :=
by simp [to_finsupp_iso, monomial, monomial_fun]

lemma monomial_injective (n : ℕ) :
  function.injective (monomial n : R → R[X]) :=
begin
  convert (to_finsupp_iso R).symm.injective.comp (single_injective n),
  ext,
  simp
end

@[simp] lemma monomial_eq_zero_iff (t : R) (n : ℕ) :
  monomial n t = 0 ↔ t = 0 :=
linear_map.map_eq_zero_iff _ (polynomial.monomial_injective n)

lemma support_add : (p + q).support ⊆ p.support ∪ q.support :=
begin
  rcases p, rcases q,
  simp only [add_to_finsupp, support],
  exact support_add
end

/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* R[X] :=
{ map_one' := by simp [monomial_zero_one],
  map_mul' := by simp [monomial_mul_monomial],
  map_zero' := by simp,
  .. monomial 0 }

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma C_0 : C (0 : R) = 0 := by simp

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp] lemma smul_C {S} [monoid S] [distrib_mul_action S R] (s : S) (r : R) :
  s • C r = C (s • r) :=
smul_monomial _ _ r

@[simp] lemma C_bit0 : C (bit0 a) = bit0 (C a) := C_add

@[simp] lemma C_bit1 : C (bit1 a) = bit1 (C a) := by simp [bit1, C_bit0]

lemma C_pow : C (a ^ n) = C a ^ n := C.map_pow a n

@[simp]
lemma C_eq_nat_cast (n : ℕ) : C (n : R) = (n : R[X]) :=
map_nat_cast C n

@[simp] lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, zero_add]

@[simp] lemma monomial_mul_C : monomial n a * C b = monomial n (a * b) :=
by simp only [←monomial_zero_left, monomial_mul_monomial, add_zero]

/-- `X` is the polynomial variable (aka indeterminate). -/
def X : R[X] := monomial 1 1

lemma monomial_one_one_eq_X : monomial 1 (1 : R) = X := rfl

lemma monomial_one_right_eq_X_pow (n : ℕ) : monomial n (1 : R) = X^n :=
begin
  induction n with n ih,
  { simp [monomial_zero_one], },
  { rw [pow_succ, ←ih, ←monomial_one_one_eq_X, monomial_mul_monomial, add_comm, one_mul], }
end

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
begin
  rcases p,
  simp only [X, monomial, monomial_fun, mul_to_finsupp, linear_map.coe_mk],
  ext,
  simp [add_monoid_algebra.mul_apply, sum_single_index, add_comm],
  congr; ext; congr,
end

lemma X_pow_mul {n : ℕ} : X^n * p = p * X^n :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs { rw pow_succ', },
    rw [mul_assoc, X_mul, ←mul_assoc, ih, mul_assoc, ←pow_succ'], }
end

lemma X_pow_mul_assoc {n : ℕ} : (p * X^n) * q = (p * q) * X^n :=
by rw [mul_assoc, X_pow_mul, ←mul_assoc]

lemma commute_X (p : R[X]) : commute X p := X_mul

lemma commute_X_pow (p : R[X]) (n : ℕ) : commute (X ^ n) p := X_pow_mul

@[simp]
lemma monomial_mul_X (n : ℕ) (r : R) : monomial n r * X = monomial (n+1) r :=
by erw [monomial_mul_monomial, mul_one]

@[simp]
lemma monomial_mul_X_pow (n : ℕ) (r : R) (k : ℕ) : monomial n r * X^k = monomial (n+k) r :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih, pow_succ', ←mul_assoc, add_assoc], },
end

@[simp]
lemma X_mul_monomial (n : ℕ) (r : R) : X * monomial n r = monomial (n+1) r :=
by rw [X_mul, monomial_mul_X]

@[simp]
lemma X_pow_mul_monomial (k n : ℕ) (r : R) : X^k * monomial n r = monomial (n+k) r :=
by rw [X_pow_mul, monomial_mul_X_pow]

/-- `coeff p n` (often denoted `p.coeff n`) is the coefficient of `X^n` in `p`. -/
def coeff : R[X] → ℕ → R
| ⟨p⟩ n := p n

lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
by { simp only [monomial, monomial_fun, coeff, linear_map.coe_mk], rw finsupp.single_apply }

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : R[X]) n = 0 := rfl

@[simp] lemma coeff_one_zero : coeff (1 : R[X]) 0 = 1 :=
by { rw [← monomial_zero_one, coeff_monomial], simp }

@[simp] lemma coeff_X_one : coeff (X : R[X]) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : R[X]) 0 = 0 := coeff_monomial

@[simp] lemma coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 :=
by simp [coeff_monomial]

lemma coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 0 := coeff_monomial

lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : R[X]) n = 0 :=
by rw [coeff_X, if_neg hn.symm]

@[simp] lemma mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 :=
by { rcases p, simp [support, coeff] }

lemma not_mem_support_iff : n ∉ p.support ↔ p.coeff n = 0 :=
by simp

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by { convert coeff_monomial using 2, simp [eq_comm], }

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 :=
by rw [coeff_C, if_neg h]

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : nontrivial R :=
⟨⟨0, 1, λ h01 : 0 = 1, h $
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

lemma monomial_eq_C_mul_X : ∀{n}, monomial n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc monomial (n + 1) a = monomial n a * X : by { rw [X, monomial_mul_monomial, mul_one], }
    ... = (C a * X^n) * X : by rw [monomial_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

@[simp] lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
calc C a = 0 ↔ C a = C 0 : by rw C_0
         ... ↔ a = 0 : C_inj

theorem ext_iff {p q : R[X]} : p = q ↔ ∀ n, coeff p n = coeff q n :=
by { rcases p, rcases q, simp [coeff, finsupp.ext_iff] }

@[ext] lemma ext {p q : R[X]} : (∀ n, coeff p n = coeff q n) → p = q :=
ext_iff.2

/-- Monomials generate the additive monoid of polynomials. -/
lemma add_submonoid_closure_set_of_eq_monomial :
  add_submonoid.closure {p : R[X] | ∃ n a, p = monomial n a} = ⊤ :=
begin
  apply top_unique,
  rw [← add_submonoid.map_equiv_top (to_finsupp_iso R).symm.to_add_equiv,
    ← finsupp.add_closure_set_of_eq_single, add_monoid_hom.map_mclosure],
  refine add_submonoid.closure_mono (set.image_subset_iff.2 _),
  rintro _ ⟨n, a, rfl⟩,
  exact ⟨n, a, polynomial.to_finsupp_iso_symm_single⟩,
end

lemma add_hom_ext {M : Type*} [add_monoid M] {f g : R[X] →+ M}
  (h : ∀ n a, f (monomial n a) = g (monomial n a)) :
  f = g :=
add_monoid_hom.eq_of_eq_on_mdense add_submonoid_closure_set_of_eq_monomial $
  by { rintro p ⟨n, a, rfl⟩, exact h n a }

@[ext] lemma add_hom_ext' {M : Type*} [add_monoid M] {f g : R[X] →+ M}
  (h : ∀ n, f.comp (monomial n).to_add_monoid_hom = g.comp (monomial n).to_add_monoid_hom) :
  f = g :=
add_hom_ext (λ n, add_monoid_hom.congr_fun (h n))

@[ext] lemma lhom_ext' {M : Type*} [add_comm_monoid M] [module R M] {f g : R[X] →ₗ[R] M}
  (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
  f = g :=
linear_map.to_add_monoid_hom_injective $ add_hom_ext $ λ n, linear_map.congr_fun (h n)

-- this has the same content as the subsingleton
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : R[X]) : p = 0 :=
by rw [←one_smul R p, ←h, zero_smul]

lemma support_monomial (n) (a : R) (H : a ≠ 0) : (monomial n a).support = singleton n :=
by simp [monomial, monomial_fun, support, finsupp.support_single_ne_zero H]

lemma support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n :=
by simp [monomial, monomial_fun, support, finsupp.support_single_subset]

lemma X_pow_eq_monomial (n) : X ^ n = monomial n (1:R) :=
begin
  induction n with n hn,
  { rw [pow_zero, monomial_zero_one] },
  { rw [pow_succ', hn, X, monomial_mul_monomial, one_mul] },
end

lemma monomial_eq_smul_X {n} : monomial n (a : R) = a • X^n :=
calc monomial n a = monomial n (a * 1) : by simp
  ... = a • monomial n 1 : by simp [monomial, monomial_fun, smul_to_finsupp]
  ... = a • X^n  : by rw X_pow_eq_monomial

lemma support_X_pow (H : ¬ (1:R) = 0) (n : ℕ) : (X^n : R[X]).support = singleton n :=
begin
  convert support_monomial n 1 H,
  exact X_pow_eq_monomial n,
end

lemma support_X_empty (H : (1:R)=0) : (X : R[X]).support = ∅ :=
begin
  rw [X, H, monomial_zero_right, support_zero],
end

lemma support_X (H : ¬ (1 : R) = 0) : (X : R[X]).support = singleton 1 :=
begin
  rw [← pow_one X, support_X_pow H 1],
end

lemma monomial_left_inj {R : Type*} [semiring R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
  (monomial i a) = (monomial j a) ↔ i = j :=
by simp [monomial, monomial_fun, finsupp.single_left_inj ha]

lemma nat_cast_mul {R : Type*} [semiring R] (n : ℕ) (p : R[X]) :
  (n : R[X]) * p = n • p :=
(nsmul_eq_mul _ _).symm

/-- Summing the values of a function applied to the coefficients of a polynomial -/
def sum {S : Type*} [add_comm_monoid S] (p : R[X]) (f : ℕ → R → S) : S :=
∑ n in p.support, f n (p.coeff n)

lemma sum_def {S : Type*} [add_comm_monoid S] (p : R[X]) (f : ℕ → R → S) :
  p.sum f = ∑ n in p.support, f n (p.coeff n) := rfl

lemma sum_eq_of_subset {S : Type*} [add_comm_monoid S] (p : R[X])
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) (s : finset ℕ) (hs : p.support ⊆ s) :
  p.sum f = ∑ n in s, f n (p.coeff n) :=
begin
  apply finset.sum_subset hs (λ n hn h'n, _),
  rw not_mem_support_iff at h'n,
  simp [h'n, hf]
end

/-- Expressing the product of two polynomials as a double sum. -/
lemma mul_eq_sum_sum :
  p * q = ∑ i in p.support, q.sum (λ j a, (monomial (i + j)) (p.coeff i * a)) :=
begin
  rcases p, rcases q,
  simp [mul_to_finsupp, support, monomial, sum, monomial_fun, coeff, sum_to_finsupp],
  refl
end

@[simp] lemma sum_zero_index {S : Type*} [add_comm_monoid S] (f : ℕ → R → S) :
  (0 : R[X]).sum f = 0 :=
by simp [sum]

@[simp] lemma sum_monomial_index {S : Type*} [add_comm_monoid S]
  (n : ℕ) (a : R) (f : ℕ → R → S) (hf : f n 0 = 0) :
  (monomial n a : R[X]).sum f = f n a :=
begin
  by_cases h : a = 0,
  { simp [h, hf] },
  { simp [sum, support_monomial, h, coeff_monomial] }
end

@[simp] lemma sum_C_index {a} {β} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a :=
sum_monomial_index 0 a f h

-- the assumption `hf` is only necessary when the ring is trivial
@[simp] lemma sum_X_index {S : Type*} [add_comm_monoid S] {f : ℕ → R → S} (hf : f 1 0 = 0) :
  (X : R[X]).sum f = f 1 1 :=
sum_monomial_index 1 1 f hf

lemma sum_add_index {S : Type*} [add_comm_monoid S] (p q : R[X])
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) (h_add : ∀a b₁ b₂, f a (b₁ + b₂) = f a b₁ + f a b₂) :
  (p + q).sum f = p.sum f + q.sum f :=
begin
  rcases p, rcases q,
  simp only [add_to_finsupp, sum, support, coeff, pi.add_apply, coe_add],
  exact finsupp.sum_add_index hf h_add,
end

lemma sum_add' {S : Type*} [add_comm_monoid S] (p : R[X]) (f g : ℕ → R → S) :
  p.sum (f + g) = p.sum f + p.sum g :=
by simp [sum_def, finset.sum_add_distrib]

lemma sum_add {S : Type*} [add_comm_monoid S] (p : R[X]) (f g : ℕ → R → S) :
  p.sum (λ n x, f n x + g n x) = p.sum f + p.sum g :=
sum_add' _ _ _

lemma sum_smul_index {S : Type*} [add_comm_monoid S] (p : R[X]) (b : R)
  (f : ℕ → R → S) (hf : ∀ i, f i 0 = 0) : (b • p).sum f = p.sum (λ n a, f n (b * a)) :=
begin
  rcases p,
  simp [smul_to_finsupp, sum, support, coeff],
  exact finsupp.sum_smul_index hf,
end

/-- `erase p n` is the polynomial `p` in which the `X^n` term has been erased. -/
@[irreducible] definition erase (n : ℕ) : R[X] → R[X]
| ⟨p⟩ := ⟨p.erase n⟩

@[simp] lemma support_erase (p : R[X]) (n : ℕ) :
  support (p.erase n) = (support p).erase n :=
by { rcases p, simp only [support, erase, support_erase] }

lemma monomial_add_erase (p : R[X]) (n : ℕ) : monomial n (coeff p n) + p.erase n = p :=
begin
  rcases p,
  simp [add_to_finsupp, monomial, monomial_fun, coeff, erase],
  exact finsupp.single_add_erase _ _
end

lemma coeff_erase (p : R[X]) (n i : ℕ) :
  (p.erase n).coeff i = if i = n then 0 else p.coeff i :=
begin
  rcases p,
  simp only [erase, coeff],
  convert rfl
end

@[simp] lemma erase_zero (n : ℕ) : (0 : R[X]).erase n = 0 :=
by simp [← zero_to_finsupp, erase]

@[simp] lemma erase_monomial {n : ℕ} {a : R} : erase n (monomial n a) = 0 :=
by simp [monomial, monomial_fun, erase, ← zero_to_finsupp]

@[simp] lemma erase_same (p : R[X]) (n : ℕ) : coeff (p.erase n) n = 0 :=
by simp [coeff_erase]

@[simp] lemma erase_ne (p : R[X]) (n i : ℕ) (h : i ≠ n) :
  coeff (p.erase n) i = coeff p i :=
by simp [coeff_erase, h]

section update

/-- Replace the coefficient of a `p : polynomial p` at a given degree `n : ℕ`
by a given value `a : R`. If `a = 0`, this is equal to `p.erase n`
If `p.nat_degree < n` and `a ≠ 0`, this increases the degree to `n`.  -/
def update (p : R[X]) (n : ℕ) (a : R) :
  R[X] :=
polynomial.of_finsupp (p.to_finsupp.update n a)

lemma coeff_update (p : R[X]) (n : ℕ) (a : R) :
  (p.update n a).coeff = function.update p.coeff n a :=
begin
  ext,
  cases p,
  simp only [coeff, update, function.update_apply, coe_update],
end

lemma coeff_update_apply (p : R[X]) (n : ℕ) (a : R) (i : ℕ) :
  (p.update n a).coeff i = if (i = n) then a else p.coeff i :=
by rw [coeff_update, function.update_apply]

@[simp] lemma coeff_update_same (p : R[X]) (n : ℕ) (a : R) :
  (p.update n a).coeff n = a :=
by rw [p.coeff_update_apply, if_pos rfl]

lemma coeff_update_ne (p : R[X]) {n : ℕ} (a : R) {i : ℕ} (h : i ≠ n) :
  (p.update n a).coeff i = p.coeff i :=
by rw [p.coeff_update_apply, if_neg h]

@[simp] lemma update_zero_eq_erase (p : R[X]) (n : ℕ) :
  p.update n 0 = p.erase n :=
by { ext, rw [coeff_update_apply, coeff_erase] }

lemma support_update (p : R[X]) (n : ℕ) (a : R) [decidable (a = 0)] :
  support (p.update n a) = if a = 0 then p.support.erase n else insert n p.support :=
by { cases p, simp only [support, update, support_update], congr }

lemma support_update_zero (p : R[X]) (n : ℕ) :
  support (p.update n 0) = p.support.erase n :=
by rw [update_zero_eq_erase, support_erase]

lemma support_update_ne_zero (p : R[X]) (n : ℕ) {a : R} (ha : a ≠ 0) :
  support (p.update n a) = insert n p.support :=
by classical; rw [support_update, if_neg ha]

end update

end semiring

section comm_semiring
variables [comm_semiring R]

instance : comm_semiring R[X] :=
{ mul_comm := by { rintros ⟨⟩ ⟨⟩, simp [mul_to_finsupp, mul_comm] }, .. polynomial.semiring }

end comm_semiring

section ring
variables [ring R]

instance : ring R[X] :=
{ neg := has_neg.neg,
  add_left_neg := by { rintros ⟨⟩, simp [neg_to_finsupp, add_to_finsupp, ← zero_to_finsupp] },
  zsmul := (•),
  zsmul_zero' := by { rintro ⟨⟩, simp [smul_to_finsupp, ← zero_to_finsupp] },
  zsmul_succ' := by { rintros n ⟨⟩, simp [smul_to_finsupp, add_to_finsupp, add_smul, add_comm] },
  zsmul_neg' := by { rintros n ⟨⟩,
    simp only [smul_to_finsupp, neg_to_finsupp], simp [add_smul, add_mul] },
  .. polynomial.semiring }

@[simp] lemma coeff_neg (p : R[X]) (n : ℕ) : coeff (-p) n = -coeff p n :=
by { rcases p, simp [coeff, neg_to_finsupp] }

@[simp]
lemma coeff_sub (p q : R[X]) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n :=
by { rcases p, rcases q, simp [coeff, sub_eq_add_neg, add_to_finsupp, neg_to_finsupp] }

@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) :=
by rw [eq_neg_iff_add_eq_zero, ←monomial_add, neg_add_self, monomial_zero_right]

@[simp] lemma support_neg {p : R[X]} : (-p).support = p.support :=
by { rcases p, simp [support, neg_to_finsupp] }

end ring

instance [comm_ring R] : comm_ring R[X] :=
{ .. polynomial.comm_semiring, .. polynomial.ring }

section nonzero_semiring

variables [semiring R] [nontrivial R]
instance : nontrivial R[X] :=
begin
  have h : nontrivial (add_monoid_algebra R ℕ) := by apply_instance,
  rcases h.exists_pair_ne with ⟨x, y, hxy⟩,
  refine ⟨⟨⟨x⟩, ⟨y⟩, _⟩⟩,
  simp [hxy],
end

lemma X_ne_zero : (X : R[X]) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

end nonzero_semiring

section repr
variables [semiring R]
open_locale classical

instance [has_repr R] : has_repr R[X] :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

end repr

end polynomial
