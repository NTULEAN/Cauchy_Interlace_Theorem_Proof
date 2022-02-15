/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.degree.definitions
import algebra.geom_sum

/-!
# Theory of univariate polynomials

The main defs here are `eval₂`, `eval`, and `map`.
We give several lemmas about their interaction with each other and with module operations.
-/

noncomputable theory

open finset add_monoid_algebra
open_locale big_operators polynomial

namespace polynomial
universes u v w y
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section semiring
variables [semiring R] {p q r : R[X]}

section
variables [semiring S]
variables (f : R →+* S) (x : S)

/-- Evaluate a polynomial `p` given a ring hom `f` from the scalar ring
  to the target and a value `x` for the variable in the target -/
def eval₂ (p : R[X]) : S :=
p.sum (λ e a, f a * x ^ e)

lemma eval₂_eq_sum {f : R →+* S} {x : S} : p.eval₂ f x = p.sum (λ e a, f a * x ^ e) := rfl

lemma eval₂_congr {R S : Type*} [semiring R] [semiring S]
  {f g : R →+* S} {s t : S} {φ ψ : R[X]} :
  f = g → s = t → φ = ψ → eval₂ f s φ = eval₂ g t ψ :=
by rintro rfl rfl rfl; refl

@[simp] lemma eval₂_at_zero : p.eval₂ f 0 = f (coeff p 0) :=
by simp only [eval₂_eq_sum, zero_pow_eq, mul_ite, mul_zero, mul_one, sum, not_not, mem_support_iff,
  sum_ite_eq', ite_eq_left_iff, ring_hom.map_zero, implies_true_iff, eq_self_iff_true]
  {contextual := tt}

@[simp] lemma eval₂_zero : (0 : R[X]).eval₂ f x = 0 :=
by simp [eval₂_eq_sum]

@[simp] lemma eval₂_C : (C a).eval₂ f x = f a :=
by simp [eval₂_eq_sum]

@[simp] lemma eval₂_X : X.eval₂ f x = x :=
by simp [eval₂_eq_sum]

@[simp] lemma eval₂_monomial {n : ℕ} {r : R} : (monomial n r).eval₂ f x = (f r) * x^n :=
by simp [eval₂_eq_sum]

@[simp] lemma eval₂_X_pow {n : ℕ} : (X^n).eval₂ f x = x^n :=
begin
  rw X_pow_eq_monomial,
  convert eval₂_monomial f x,
  simp,
end

@[simp] lemma eval₂_add : (p + q).eval₂ f x = p.eval₂ f x + q.eval₂ f x :=
by { apply sum_add_index; simp [add_mul] }

@[simp] lemma eval₂_one : (1 : R[X]).eval₂ f x = 1 :=
by rw [← C_1, eval₂_C, f.map_one]

@[simp] lemma eval₂_bit0 : (bit0 p).eval₂ f x = bit0 (p.eval₂ f x) :=
by rw [bit0, eval₂_add, bit0]

@[simp] lemma eval₂_bit1 : (bit1 p).eval₂ f x = bit1 (p.eval₂ f x) :=
by rw [bit1, eval₂_add, eval₂_bit0, eval₂_one, bit1]

@[simp] lemma eval₂_smul (g : R →+* S) (p : R[X]) (x : S) {s : R} :
  eval₂ g x (s • p) = g s * eval₂ g x p :=
begin
  have A : p.nat_degree < p.nat_degree.succ := nat.lt_succ_self _,
  have B : (s • p).nat_degree < p.nat_degree.succ := (nat_degree_smul_le _ _).trans_lt A,
  rw [eval₂_eq_sum, eval₂_eq_sum, sum_over_range' _ _ _ A, sum_over_range' _ _ _ B];
  simp [mul_sum, mul_assoc],
end

@[simp] lemma eval₂_C_X : eval₂ C X p = p :=
polynomial.induction_on' p (λ p q hp hq, by simp [hp, hq])
  (λ n x, by rw [eval₂_monomial, monomial_eq_smul_X, C_mul'])

/-- `eval₂_add_monoid_hom (f : R →+* S) (x : S)` is the `add_monoid_hom` from
`polynomial R` to `S` obtained by evaluating the pushforward of `p` along `f` at `x`. -/
@[simps] def eval₂_add_monoid_hom : R[X] →+ S :=
{ to_fun := eval₂ f x,
  map_zero' := eval₂_zero _ _,
  map_add' := λ _ _, eval₂_add _ _ }

@[simp] lemma eval₂_nat_cast (n : ℕ) : (n : R[X]).eval₂ f x = n :=
begin
  induction n with n ih,
  { simp only [eval₂_zero, nat.cast_zero] },
  { rw [n.cast_succ, eval₂_add, ih, eval₂_one, n.cast_succ] }
end

variables [semiring T]
lemma eval₂_sum (p : T[X]) (g : ℕ → T → R[X]) (x : S) :
  (p.sum g).eval₂ f x = p.sum (λ n a, (g n a).eval₂ f x) :=
begin
  let T : R[X] →+ S :=
    { to_fun := eval₂ f x, map_zero' := eval₂_zero _ _, map_add' := λ p q, eval₂_add _ _ },
  have A : ∀ y, eval₂ f x y = T y := λ y, rfl,
  simp only [A],
  rw [sum, T.map_sum, sum]
end

lemma eval₂_finset_sum (s : finset ι) (g : ι → R[X]) (x : S) :
  (∑ i in s, g i).eval₂ f x = ∑ i in s, (g i).eval₂ f x :=
begin
  classical,
  induction s using finset.induction with p hp s hs, simp,
  rw [sum_insert, eval₂_add, hs, sum_insert]; assumption,
end

lemma eval₂_to_finsupp_eq_lift_nc {f : R →+* S} {x : S} {p : add_monoid_algebra R ℕ} :
  eval₂ f x (⟨p⟩ : R[X]) = lift_nc ↑f (powers_hom S x) p :=
by { simp only [eval₂_eq_sum, sum, sum_to_finsupp, support, coeff], refl }

lemma eval₂_mul_noncomm (hf : ∀ k, commute (f $ q.coeff k) x) :
  eval₂ f x (p * q) = eval₂ f x p * eval₂ f x q :=
begin
  rcases p, rcases q,
  simp only [coeff] at hf,
  simp only [mul_to_finsupp, eval₂_to_finsupp_eq_lift_nc],
  exact lift_nc_mul _ _ p q (λ k n hn, (hf k).pow_right n)
end

@[simp] lemma eval₂_mul_X : eval₂ f x (p * X) = eval₂ f x p * x :=
begin
  refine trans (eval₂_mul_noncomm _ _ $ λ k, _) (by rw eval₂_X),
  rcases em (k = 1) with (rfl|hk),
  { simp },
  { simp [coeff_X_of_ne_one hk] }
end

@[simp] lemma eval₂_X_mul : eval₂ f x (X * p) = eval₂ f x p * x :=
by rw [X_mul, eval₂_mul_X]

lemma eval₂_mul_C' (h : commute (f a) x) : eval₂ f x (p * C a) = eval₂ f x p * f a :=
begin
  rw [eval₂_mul_noncomm, eval₂_C],
  intro k,
  by_cases hk : k = 0,
  { simp only [hk, h, coeff_C_zero, coeff_C_ne_zero] },
  { simp only [coeff_C_ne_zero hk, ring_hom.map_zero, commute.zero_left] }
end

lemma eval₂_list_prod_noncomm (ps : list R[X])
  (hf : ∀ (p ∈ ps) k, commute (f $ coeff p k) x) :
  eval₂ f x ps.prod = (ps.map (polynomial.eval₂ f x)).prod :=
begin
  induction ps using list.reverse_rec_on with ps p ihp,
  { simp },
  { simp only [list.forall_mem_append, list.forall_mem_singleton] at hf,
    simp [eval₂_mul_noncomm _ _ hf.2, ihp hf.1] }
end

/-- `eval₂` as a `ring_hom` for noncommutative rings -/
def eval₂_ring_hom' (f : R →+* S) (x : S) (hf : ∀ a, commute (f a) x) : R[X] →+* S :=
{ to_fun := eval₂ f x,
  map_add' := λ _ _, eval₂_add _ _,
  map_zero' := eval₂_zero _ _,
  map_mul' := λ p q, eval₂_mul_noncomm f x (λ k, hf $ coeff q k),
  map_one' := eval₂_one _ _ }

end

/-!
We next prove that eval₂ is multiplicative
as long as target ring is commutative
(even if the source ring is not).
-/
section eval₂
variables [comm_semiring S]
variables (f : R →+* S) (x : S)

@[simp] lemma eval₂_mul : (p * q).eval₂ f x = p.eval₂ f x * q.eval₂ f x :=
eval₂_mul_noncomm _ _ $ λ k, commute.all _ _

lemma eval₂_mul_eq_zero_of_left (q : R[X]) (hp : p.eval₂ f x = 0) :
  (p * q).eval₂ f x = 0 :=
begin
  rw eval₂_mul f x,
  exact mul_eq_zero_of_left hp (q.eval₂ f x)
end

lemma eval₂_mul_eq_zero_of_right (p : R[X]) (hq : q.eval₂ f x = 0) :
  (p * q).eval₂ f x = 0 :=
begin
  rw eval₂_mul f x,
  exact mul_eq_zero_of_right (p.eval₂ f x) hq
end

/-- `eval₂` as a `ring_hom` -/
def eval₂_ring_hom (f : R →+* S) (x : S) : R[X] →+* S :=
{ map_one' := eval₂_one _ _,
  map_mul' := λ _ _, eval₂_mul _ _,
  ..eval₂_add_monoid_hom f x }

@[simp] lemma coe_eval₂_ring_hom (f : R →+* S) (x) : ⇑(eval₂_ring_hom f x) = eval₂ f x := rfl

lemma eval₂_pow (n : ℕ) : (p ^ n).eval₂ f x = p.eval₂ f x ^ n := (eval₂_ring_hom _ _).map_pow _ _

lemma eval₂_eq_sum_range :
  p.eval₂ f x = ∑ i in finset.range (p.nat_degree + 1), f (p.coeff i) * x^i :=
trans (congr_arg _ p.as_sum_range) (trans (eval₂_finset_sum f _ _ x) (congr_arg _ (by simp)))

lemma eval₂_eq_sum_range' (f : R →+* S) {p : R[X]} {n : ℕ} (hn : p.nat_degree < n) (x : S) :
  eval₂ f x p = ∑ i in finset.range n, f (p.coeff i) * x ^ i :=
begin
  rw [eval₂_eq_sum, p.sum_over_range' _ _ hn],
  intro i,
  rw [f.map_zero, zero_mul]
end

lemma eval₂_dvd : p ∣ q → eval₂ f x p ∣ eval₂ f x q :=
(eval₂_ring_hom f x).map_dvd

lemma eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) :
  eval₂ f x q = 0 :=
zero_dvd_iff.mp (h0 ▸ eval₂_dvd f x h)

end eval₂

section eval
variables {x : R}

/-- `eval x p` is the evaluation of the polynomial `p` at `x` -/
def eval : R → R[X] → R := eval₂ (ring_hom.id _)

lemma eval_eq_sum : p.eval x = p.sum (λ e a, a * x ^ e) :=
rfl

lemma eval_eq_finset_sum (p : R[X]) (x : R) :
  p.eval x = ∑ i in range (p.nat_degree + 1), p.coeff i * x ^ i :=
by { rw [eval_eq_sum, sum_over_range], simp }

lemma eval_eq_finset_sum' (P : R[X]) :
  (λ x, eval x P) = (λ x, ∑ i in range (P.nat_degree + 1), P.coeff i * x ^ i) :=
begin
  ext,
  exact P.eval_eq_finset_sum x
end

@[simp] lemma eval₂_at_apply {S : Type*} [semiring S] (f : R →+* S) (r : R) :
  p.eval₂ f (f r) = f (p.eval r) :=
begin
  rw [eval₂_eq_sum, eval_eq_sum, sum, sum, f.map_sum],
  simp only [f.map_mul, f.map_pow],
end

@[simp] lemma eval₂_at_one {S : Type*} [semiring S] (f : R →+* S) : p.eval₂ f 1 = f (p.eval 1) :=
begin
  convert eval₂_at_apply f 1,
  simp,
end

@[simp] lemma eval₂_at_nat_cast {S : Type*} [semiring S] (f : R →+* S) (n : ℕ) :
  p.eval₂ f n = f (p.eval n) :=
begin
  convert eval₂_at_apply f n,
  simp,
end

@[simp] lemma eval_C : (C a).eval x = a := eval₂_C _ _

@[simp] lemma eval_nat_cast {n : ℕ} : (n : R[X]).eval x = n :=
by simp only [←C_eq_nat_cast, eval_C]

@[simp] lemma eval_X : X.eval x = x := eval₂_X _ _

@[simp] lemma eval_monomial {n a} : (monomial n a).eval x = a * x^n :=
eval₂_monomial _ _

@[simp] lemma eval_zero : (0 : R[X]).eval x = 0 :=  eval₂_zero _ _

@[simp] lemma eval_add : (p + q).eval x = p.eval x + q.eval x := eval₂_add _ _

@[simp] lemma eval_one : (1 : R[X]).eval x = 1 := eval₂_one _ _

@[simp] lemma eval_bit0 : (bit0 p).eval x = bit0 (p.eval x) := eval₂_bit0 _ _

@[simp] lemma eval_bit1 : (bit1 p).eval x = bit1 (p.eval x) := eval₂_bit1 _ _

@[simp] lemma eval_smul (p : R[X]) (x : R) {s : R} :
  (s • p).eval x = s * p.eval x :=
eval₂_smul (ring_hom.id _) _ _

@[simp] lemma eval_C_mul : (C a * p).eval x = a * p.eval x :=
begin
  apply polynomial.induction_on' p,
  { intros p q ph qh,
    simp only [mul_add, eval_add, ph, qh], },
  { intros n b,
    simp only [mul_assoc, C_mul_monomial, eval_monomial], }
end

/-- `polynomial.eval` as linear map -/
@[simps] def leval {R : Type*} [semiring R] (r : R) : R[X] →ₗ[R] R :=
{ to_fun := λ f, f.eval r,
  map_add' := λ f g, eval_add,
  map_smul' := λ c f, eval_smul f r }

@[simp] lemma eval_nat_cast_mul {n : ℕ} : ((n : R[X]) * p).eval x = n * p.eval x :=
by rw [←C_eq_nat_cast, eval_C_mul]

@[simp] lemma eval_mul_X : (p * X).eval x = p.eval x * x :=
begin
  apply polynomial.induction_on' p,
  { intros p q ph qh,
    simp only [add_mul, eval_add, ph, qh], },
  { intros n a,
    simp only [←monomial_one_one_eq_X, monomial_mul_monomial, eval_monomial,
      mul_one, pow_succ', mul_assoc], }
end

@[simp] lemma eval_mul_X_pow {k : ℕ} : (p * X^k).eval x = p.eval x * x^k :=
begin
  induction k with k ih,
  { simp, },
  { simp [pow_succ', ←mul_assoc, ih], }
end

lemma eval_sum (p : R[X]) (f : ℕ → R → R[X]) (x : R) :
  (p.sum f).eval x = p.sum (λ n a, (f n a).eval x) :=
eval₂_sum _ _ _ _

lemma eval_finset_sum (s : finset ι) (g : ι → R[X]) (x : R) :
  (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x := eval₂_finset_sum _ _ _ _

/-- `is_root p x` implies `x` is a root of `p`. The evaluation of `p` at `x` is zero -/
def is_root (p : R[X]) (a : R) : Prop := p.eval a = 0

instance [decidable_eq R] : decidable (is_root p a) := by unfold is_root; apply_instance

@[simp] lemma is_root.def : is_root p a ↔ p.eval a = 0 := iff.rfl

lemma is_root.eq_zero (h : is_root p x) : eval x p = 0 := h

lemma coeff_zero_eq_eval_zero (p : R[X]) :
  coeff p 0 = p.eval 0 :=
calc coeff p 0 = coeff p 0 * 0 ^ 0 : by simp
... = p.eval 0 : eq.symm $
  finset.sum_eq_single _ (λ b _ hb, by simp [zero_pow (nat.pos_of_ne_zero hb)]) (by simp)

lemma zero_is_root_of_coeff_zero_eq_zero {p : R[X]} (hp : p.coeff 0 = 0) :
  is_root p 0 :=
by rwa coeff_zero_eq_eval_zero at hp

lemma is_root.dvd {R : Type*} [comm_semiring R] {p q : R[X]} {x : R}
  (h : p.is_root x) (hpq : p ∣ q) : q.is_root x :=
by rwa [is_root, eval, eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hpq]

lemma not_is_root_C (r a : R) (hr : r ≠ 0) : ¬ is_root (C r) a :=
by simpa using hr

end eval

section comp

/-- The composition of polynomials as a polynomial. -/
def comp (p q : R[X]) : R[X] := p.eval₂ C q

lemma comp_eq_sum_left : p.comp q = p.sum (λ e a, C a * q ^ e) :=
rfl

@[simp] lemma comp_X : p.comp X = p :=
begin
  simp only [comp, eval₂, ← monomial_eq_C_mul_X],
  exact sum_monomial_eq _,
end

@[simp] lemma X_comp : X.comp p = p := eval₂_X _ _

@[simp] lemma comp_C : p.comp (C a) = C (p.eval a) :=
by simp [comp, (C : R →+* _).map_sum]

@[simp] lemma C_comp : (C a).comp p = C a := eval₂_C _ _

@[simp] lemma nat_cast_comp {n : ℕ} : (n : R[X]).comp p = n :=
by rw [←C_eq_nat_cast, C_comp]

@[simp] lemma comp_zero : p.comp (0 : R[X]) = C (p.eval 0) :=
by rw [← C_0, comp_C]

@[simp] lemma zero_comp : comp (0 : R[X]) p = 0 :=
by rw [← C_0, C_comp]

@[simp] lemma comp_one : p.comp 1 = C (p.eval 1) :=
by rw [← C_1, comp_C]

@[simp] lemma one_comp : comp (1 : R[X]) p = 1 :=
by rw [← C_1, C_comp]

@[simp] lemma add_comp : (p + q).comp r = p.comp r + q.comp r := eval₂_add _ _

@[simp] lemma monomial_comp (n : ℕ) : (monomial n a).comp p = C a * p^n :=
eval₂_monomial _ _

@[simp] lemma mul_X_comp : (p * X).comp r = p.comp r * r :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp only [hp, hq, add_mul, add_comp] },
  { intros n b, simp only [pow_succ', mul_assoc, monomial_mul_X, monomial_comp] }
end

@[simp] lemma X_pow_comp {k : ℕ} : (X^k).comp p = p^k :=
begin
  induction k with k ih,
  { simp, },
  { simp [pow_succ', mul_X_comp, ih], },
end

@[simp] lemma mul_X_pow_comp {k : ℕ} : (p * X^k).comp r = p.comp r * r^k :=
begin
  induction k with k ih,
  { simp, },
  { simp [ih, pow_succ', ←mul_assoc, mul_X_comp], },
end

@[simp] lemma C_mul_comp : (C a * p).comp r = C a * p.comp r :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp [hp, hq, mul_add], },
  { intros n b, simp [mul_assoc], }
end

@[simp] lemma nat_cast_mul_comp {n : ℕ} : ((n : R[X]) * p).comp r = n * p.comp r :=
by rw [←C_eq_nat_cast, C_mul_comp, C_eq_nat_cast]

@[simp] lemma mul_comp {R : Type*} [comm_semiring R] (p q r : R[X]) :
  (p * q).comp r = p.comp r * q.comp r := eval₂_mul _ _

lemma prod_comp {R : Type*} [comm_semiring R] (s : multiset R[X]) (p : R[X]) :
  s.prod.comp p = (s.map (λ q : R[X], q.comp p)).prod :=
(s.prod_hom (monoid_hom.mk (λ q : R[X], q.comp p) one_comp (λ q r, mul_comp q r p))).symm

@[simp] lemma pow_comp {R : Type*} [comm_semiring R] (p q : R[X]) (n : ℕ) :
  (p^n).comp q = (p.comp q)^n :=
((monoid_hom.mk (λ r : R[X], r.comp q)) one_comp (λ r s, mul_comp r s q)).map_pow p n

@[simp] lemma bit0_comp : comp (bit0 p : R[X]) q = bit0 (p.comp q) :=
by simp only [bit0, add_comp]

@[simp] lemma bit1_comp : comp (bit1 p : R[X]) q = bit1 (p.comp q) :=
by simp only [bit1, add_comp, bit0_comp, one_comp]

lemma comp_assoc {R : Type*} [comm_semiring R] (φ ψ χ : R[X]) :
  (φ.comp ψ).comp χ = φ.comp (ψ.comp χ) :=
begin
  apply polynomial.induction_on φ;
  { intros, simp only [add_comp, mul_comp, C_comp, X_comp, pow_succ', ← mul_assoc, *] at * }
end

end comp

section map
variables [semiring S]
variables (f : R →+* S)

/-- `map f p` maps a polynomial `p` across a ring hom `f` -/
def map : R[X] → S[X] := eval₂ (C.comp f) X

@[simp] lemma map_C : (C a).map f = C (f a) := eval₂_C _ _

@[simp] lemma map_X : X.map f = X := eval₂_X _ _

@[simp] lemma map_monomial {n a} : (monomial n a).map f = monomial n (f a) :=
begin
  dsimp only [map],
  rw [eval₂_monomial, monomial_eq_C_mul_X], refl,
end

@[simp] lemma map_zero : (0 : R[X]).map f = 0 :=  eval₂_zero _ _

@[simp] lemma map_add : (p + q).map f = p.map f + q.map f := eval₂_add _ _

@[simp] lemma map_one : (1 : R[X]).map f = 1 := eval₂_one _ _

@[simp] lemma map_mul : (p * q).map f = p.map f * q.map f :=
by { rw [map, eval₂_mul_noncomm], exact λ k, (commute_X _).symm }

@[simp] lemma map_smul (r : R) : (r • p).map f = f r • p.map f :=
by rw [map, eval₂_smul, ring_hom.comp_apply, C_mul']

/-- `polynomial.map` as a `ring_hom`. -/
-- `map` is a ring-hom unconditionally, and theoretically the definition could be replaced,
-- but this turns out not to be easy because `p.map f` does not resolve to `polynomial.map`
-- if `map` is a `ring_hom` instead of a plain function; the elaborator does not try to coerce
-- to a function before trying field (dot) notation (this may be technically infeasible);
-- the relevant code is (both lines): https://github.com/leanprover-community/
-- lean/blob/487ac5d7e9b34800502e1ddf3c7c806c01cf9d51/src/frontends/lean/elaborator.cpp#L1876-L1913
def map_ring_hom (f : R →+* S) : R[X] →+* S[X] :=
{ to_fun := polynomial.map f,
  map_add' := λ _ _, map_add f,
  map_zero' := map_zero f,
  map_mul' := λ _ _, map_mul f,
  map_one' := map_one f }

@[simp] lemma coe_map_ring_hom (f : R →+* S) : ⇑(map_ring_hom f) = map f := rfl

-- This is protected to not clash with the global `map_nat_cast`.
@[simp] protected theorem map_nat_cast (n : ℕ) : (n : R[X]).map f = n :=
map_nat_cast (map_ring_hom f) n

@[simp]
lemma coeff_map (n : ℕ) : coeff (p.map f) n = f (coeff p n) :=
begin
  rw [map, eval₂, coeff_sum, sum],
  conv_rhs { rw [← sum_C_mul_X_eq p, coeff_sum, sum, ring_hom.map_sum], },
  refine finset.sum_congr rfl (λ x hx, _),
  simp [function.comp, coeff_C_mul_X_pow, f.map_mul],
  split_ifs; simp [f.map_zero],
end

/-- If `R` and `S` are isomorphic, then so are their polynomial rings. -/
@[simps] def map_equiv (e : R ≃+* S) : R[X] ≃+* S[X] :=
ring_equiv.of_hom_inv
  (map_ring_hom e)
  (map_ring_hom e.symm)
  (by ext; simp)
  (by ext; simp)

lemma map_map [semiring T] (g : S →+* T)
  (p : R[X]) : (p.map f).map g = p.map (g.comp f) :=
ext (by simp [coeff_map])

@[simp] lemma map_id : p.map (ring_hom.id _) = p := by simp [polynomial.ext_iff, coeff_map]

lemma eval₂_eq_eval_map {x : S} : p.eval₂ f x = (p.map f).eval x :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp [hp, hq], },
  { intros n r, simp, }
end

lemma map_injective (hf : function.injective f) : function.injective (map f) :=
λ p q h, ext $ λ m, hf $ by rw [← coeff_map f, ← coeff_map f, h]

lemma map_surjective (hf : function.surjective f) : function.surjective (map f) :=
λ p, polynomial.induction_on' p
 (λ p q hp hq, let ⟨p', hp'⟩ := hp, ⟨q', hq'⟩ := hq in ⟨p' + q', by rw [map_add f, hp', hq']⟩)
 (λ n s, let ⟨r, hr⟩ := hf s in ⟨monomial n r, by rw [map_monomial f, hr]⟩)

lemma degree_map_le (p : R[X]) : degree (p.map f) ≤ degree p :=
begin
  apply (degree_le_iff_coeff_zero _ _).2 (λ m hm, _),
  rw degree_lt_iff_coeff_zero at hm,
  simp [hm m le_rfl],
end

lemma nat_degree_map_le (p : R[X]) : nat_degree (p.map f) ≤ nat_degree p :=
nat_degree_le_nat_degree (degree_map_le f p)

variables {f}

lemma map_monic_eq_zero_iff (hp : p.monic) : p.map f = 0 ↔ ∀ x, f x = 0 :=
⟨ λ hfp x, calc f x = f x * f p.leading_coeff : by simp only [mul_one, hp.leading_coeff, f.map_one]
                ... = f x * (p.map f).coeff p.nat_degree : congr_arg _ (coeff_map _ _).symm
                ... = 0 : by simp only [hfp, mul_zero, coeff_zero],
  λ h, ext (λ n, by simp only [h, coeff_map, coeff_zero]) ⟩

lemma map_monic_ne_zero (hp : p.monic) [nontrivial S] : p.map f ≠ 0 :=
λ h, f.map_one_ne_zero ((map_monic_eq_zero_iff hp).mp h _)

lemma degree_map_eq_of_leading_coeff_ne_zero (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : degree (p.map f) = degree p :=
le_antisymm (degree_map_le f _) $
  have hp0 : p ≠ 0, from leading_coeff_ne_zero.mp (λ hp0, hf (trans (congr_arg _ hp0) f.map_zero)),
  begin
    rw [degree_eq_nat_degree hp0],
    refine le_degree_of_ne_zero _,
    rw [coeff_map], exact hf
  end

lemma nat_degree_map_of_leading_coeff_ne_zero (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : nat_degree (p.map f) = nat_degree p :=
nat_degree_eq_of_degree_eq (degree_map_eq_of_leading_coeff_ne_zero f hf)

lemma leading_coeff_map_of_leading_coeff_ne_zero (f : R →+* S)
  (hf : f (leading_coeff p) ≠ 0) : leading_coeff (p.map f) = f (leading_coeff p) :=
begin
  unfold leading_coeff,
  rw [coeff_map, nat_degree_map_of_leading_coeff_ne_zero f hf],
end

variables (f)

@[simp] lemma map_ring_hom_id : map_ring_hom (ring_hom.id R) = ring_hom.id R[X] :=
ring_hom.ext $ λ x, map_id

@[simp] lemma map_ring_hom_comp [semiring T] (f : S →+* T) (g : R →+* S) :
  (map_ring_hom f).comp (map_ring_hom g) = map_ring_hom (f.comp g) :=
ring_hom.ext $ polynomial.map_map g f

lemma map_list_prod (L : list R[X]) : L.prod.map f = (L.map $ map f).prod :=
eq.symm $ list.prod_hom _ (map_ring_hom f).to_monoid_hom

@[simp] protected lemma map_pow (n : ℕ) : (p ^ n).map f = p.map f ^ n :=
(map_ring_hom f).map_pow _ _

lemma mem_map_srange {p : S[X]} :
  p ∈ (map_ring_hom f).srange ↔ ∀ n, p.coeff n ∈ f.srange :=
begin
  split,
  { rintro ⟨p, rfl⟩ n, rw [coe_map_ring_hom, coeff_map], exact set.mem_range_self _ },
  { intro h, rw p.as_sum_range_C_mul_X_pow,
    refine (map_ring_hom f).srange.sum_mem _,
    intros i hi,
    rcases h i with ⟨c, hc⟩,
    use [C c * X^i],
    rw [coe_map_ring_hom, map_mul, map_C, hc, polynomial.map_pow, map_X] }
end

lemma mem_map_range {R S : Type*} [ring R] [ring S] (f : R →+* S)
  {p : S[X]} : p ∈ (map_ring_hom f).range ↔ ∀ n, p.coeff n ∈ f.range :=
mem_map_srange f

lemma eval₂_map [semiring T] (g : S →+* T) (x : T) :
  (p.map f).eval₂ g x = p.eval₂ (g.comp f) x :=
begin
  have A : nat_degree (p.map f) < p.nat_degree.succ :=
    (nat_degree_map_le _ _).trans_lt (nat.lt_succ_self _),
  conv_lhs { rw [eval₂_eq_sum], },
  rw [sum_over_range' _ _ _ A],
  { simp only [coeff_map, eval₂_eq_sum, sum_over_range, forall_const, zero_mul, ring_hom.map_zero,
      function.comp_app, ring_hom.coe_comp] },
  { simp only [forall_const, zero_mul, ring_hom.map_zero] }
end

lemma eval_map (x : S) : (p.map f).eval x = p.eval₂ f x :=
eval₂_map f (ring_hom.id _) x

lemma map_sum {ι : Type*} (g : ι → R[X]) (s : finset ι) :
  (∑ i in s, g i).map f = ∑ i in s, (g i).map f :=
(map_ring_hom f).map_sum _ _

lemma map_comp (p q : R[X]) : map f (p.comp q) = (map f p).comp (map f q) :=
polynomial.induction_on p
  (by simp only [map_C, forall_const, C_comp, eq_self_iff_true])
  (by simp only [map_add, add_comp, forall_const, implies_true_iff, eq_self_iff_true]
        {contextual := tt})
  (by simp only [pow_succ', ←mul_assoc, comp, forall_const, eval₂_mul_X, implies_true_iff,
        eq_self_iff_true, map_X, map_mul] {contextual := tt})

@[simp]
lemma eval_zero_map (f : R →+* S) (p : R[X]) :
  (p.map f).eval 0 = f (p.eval 0) :=
by simp [←coeff_zero_eq_eval_zero]

@[simp]
lemma eval_one_map (f : R →+* S) (p : R[X]) :
  (p.map f).eval 1 = f (p.eval 1) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp only [hp, hq, map_add, ring_hom.map_add, eval_add] },
  { intros n r, simp only [one_pow, mul_one, eval_monomial, map_monomial] }
end

@[simp]
lemma eval_nat_cast_map (f : R →+* S) (p : R[X]) (n : ℕ) :
  (p.map f).eval n = f (p.eval n) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp only [hp, hq, map_add, ring_hom.map_add, eval_add] },
  { intros n r, simp only [map_nat_cast f, eval_monomial, map_monomial, f.map_pow, f.map_mul] }
end

@[simp]
lemma eval_int_cast_map {R S : Type*} [ring R] [ring S]
  (f : R →+* S) (p : R[X]) (i : ℤ) :
  (p.map f).eval i = f (p.eval i) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, simp only [hp, hq, map_add, ring_hom.map_add, eval_add] },
  { intros n r, simp only [f.map_int_cast, eval_monomial, map_monomial, f.map_pow, f.map_mul] }
end

end map

/-!
After having set up the basic theory of `eval₂`, `eval`, `comp`, and `map`,
we make `eval₂` irreducible.

Perhaps we can make the others irreducible too?
-/
attribute [irreducible] polynomial.eval₂

section hom_eval₂

variables [semiring S] [semiring T]  (f : R →+* S) (g : S →+* T) (p)

lemma hom_eval₂ (x : S) : g (p.eval₂ f x) = p.eval₂ (g.comp f) (g x) :=
by rw [←eval₂_map, eval₂_at_apply, eval_map]

end hom_eval₂


end semiring

section comm_semiring

section eval

variables [comm_semiring R] {p q : R[X]} {x : R}

lemma eval₂_comp [comm_semiring S] (f : R →+* S) {x : S} :
  eval₂ f x (p.comp q) = eval₂ f (eval₂ f x q) p :=
by rw [comp, p.as_sum_range]; simp [eval₂_finset_sum, eval₂_pow]

@[simp] lemma eval_mul : (p * q).eval x = p.eval x * q.eval x := eval₂_mul _ _

/-- `eval r`, regarded as a ring homomorphism from `polynomial R` to `R`. -/
def eval_ring_hom : R → R[X] →+* R := eval₂_ring_hom (ring_hom.id _)

@[simp] lemma coe_eval_ring_hom (r : R) : ((eval_ring_hom r) : R[X] → R) = eval r := rfl

@[simp] lemma eval_pow (n : ℕ) : (p ^ n).eval x = p.eval x ^ n := eval₂_pow _ _ _

@[simp]
lemma eval_comp : (p.comp q).eval x = p.eval (q.eval x) :=
begin
  apply polynomial.induction_on' p,
  { intros r s hr hs, simp [add_comp, hr, hs], },
  { intros n a, simp, }
end

/-- `comp p`, regarded as a ring homomorphism from `polynomial R` to itself. -/
def comp_ring_hom : R[X] → R[X] →+* R[X] :=
eval₂_ring_hom C

lemma eval₂_hom [comm_semiring S] (f : R →+* S) (x : R) :
  p.eval₂ f (f x) = f (p.eval x) :=
(ring_hom.comp_id f) ▸ (hom_eval₂ p (ring_hom.id R) f x).symm

lemma root_mul_left_of_is_root (p : R[X]) {q : R[X]} :
  is_root q a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, mul_zero]

lemma root_mul_right_of_is_root {p : R[X]} (q : R[X]) :
  is_root p a → is_root (p * q) a :=
λ H, by rw [is_root, eval_mul, is_root.def.1 H, zero_mul]

/--
Polynomial evaluation commutes with `list.prod`
-/
lemma eval_list_prod (l : list R[X]) (x : R) :
  eval x l.prod = (l.map (eval x)).prod :=
(eval_ring_hom x).map_list_prod l

/--
Polynomial evaluation commutes with `multiset.prod`
-/
lemma eval_multiset_prod (s : multiset R[X]) (x : R) :
  eval x s.prod = (s.map (eval x)).prod :=
(eval_ring_hom x).map_multiset_prod s

/--
Polynomial evaluation commutes with `finset.prod`
-/
lemma eval_prod {ι : Type*} (s : finset ι) (p : ι → R[X]) (x : R) :
  eval x (∏ j in s, p j) = ∏ j in s, eval x (p j) :=
(eval_ring_hom x).map_prod _ _

lemma is_root_prod {R} [comm_ring R] [is_domain R] {ι : Type*}
  (s : finset ι) (p : ι → R[X]) (x : R) :
  is_root (∏ j in s, p j) x ↔ ∃ i ∈ s, is_root (p i) x :=
by simp only [is_root, eval_prod, finset.prod_eq_zero_iff]

lemma eval_dvd : p ∣ q → eval x p ∣ eval x q :=
eval₂_dvd _ _

lemma eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q → eval x p = 0 → eval x q = 0 :=
eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

@[simp]
lemma eval_geom_sum {R} [comm_semiring R] {n : ℕ} {x : R} : eval x (geom_sum X n) = geom_sum x n :=
by simp [geom_sum_def, eval_finset_sum]

end eval

section map

variables [comm_semiring R] [comm_semiring S] (f : R →+* S)

lemma map_multiset_prod (m : multiset R[X]) : m.prod.map f = (m.map $ map f).prod :=
eq.symm $ multiset.prod_hom _ (map_ring_hom f).to_monoid_hom

lemma map_prod {ι : Type*} (g : ι → R[X]) (s : finset ι) :
  (∏ i in s, g i).map f = ∏ i in s, (g i).map f :=
(map_ring_hom f).map_prod _ _

lemma support_map_subset (p : R[X]) : (map f p).support ⊆ p.support :=
begin
  intros x,
  simp only [mem_support_iff],
  contrapose!,
  rw coeff_map,
  intro hx,
  rw hx,
  exact ring_hom.map_zero f,
end

lemma is_root.map {f : R →+* S} {x : R} {p : R[X]} (h : is_root p x) :
  is_root (p.map f) (f x) :=
by rw [is_root, eval_map, eval₂_hom, h.eq_zero, f.map_zero]

lemma is_root.of_map {R} [comm_ring R] {f : R →+* S} {x : R} {p : R[X]}
  (h : is_root (p.map f) (f x)) (hf : function.injective f) : is_root p x :=
by rwa [is_root, ←f.injective_iff'.mp hf, ←eval₂_hom, ←eval_map]

lemma is_root_map_iff {R : Type*} [comm_ring R] {f : R →+* S} {x : R} {p : R[X]}
  (hf : function.injective f) : is_root (p.map f) (f x) ↔ is_root p x :=
⟨λ h, h.of_map hf, λ h, h.map⟩

end map

end comm_semiring

section ring
variables [ring R] {p q r : R[X]}

lemma C_neg : C (-a) = -C a := ring_hom.map_neg C a

lemma C_sub : C (a - b) = C a - C b := ring_hom.map_sub C a b

@[simp] lemma map_sub {S} [ring S] (f : R →+* S) :
  (p - q).map f = p.map f - q.map f :=
(map_ring_hom f).map_sub p q

@[simp] lemma map_neg {S} [ring S] (f : R →+* S) :
  (-p).map f = -(p.map f) :=
(map_ring_hom f).map_neg p

@[simp] lemma map_int_cast {S} [ring S] (f : R →+* S) (n : ℤ) :
  map f ↑n = ↑n :=
(map_ring_hom f).map_int_cast n

@[simp] lemma eval_int_cast {n : ℤ} {x : R} : (n : R[X]).eval x = n :=
by simp only [←C_eq_int_cast, eval_C]

@[simp] lemma eval₂_neg {S} [ring S] (f : R →+* S) {x : S} :
  (-p).eval₂ f x = -p.eval₂ f x :=
by rw [eq_neg_iff_add_eq_zero, ←eval₂_add, add_left_neg, eval₂_zero]

@[simp] lemma eval₂_sub {S} [ring S] (f : R →+* S) {x : S} :
  (p - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x :=
by rw [sub_eq_add_neg, eval₂_add, eval₂_neg, sub_eq_add_neg]

@[simp] lemma eval_neg (p : R[X]) (x : R) : (-p).eval x = -p.eval x :=
eval₂_neg _

@[simp] lemma eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.eval x - q.eval x :=
eval₂_sub _

lemma root_X_sub_C : is_root (X - C a) b ↔ a = b :=
by rw [is_root.def, eval_sub, eval_X, eval_C, sub_eq_zero, eq_comm]

@[simp] lemma neg_comp : (-p).comp q = -p.comp q := eval₂_neg _

@[simp] lemma sub_comp : (p - q).comp r = p.comp r - q.comp r := eval₂_sub _

@[simp] lemma cast_int_comp (i : ℤ) : comp (i : R[X]) p = i :=
by cases i; simp

end ring

end polynomial
