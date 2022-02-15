/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import algebra.order.absolute_value
import algebra.field_power
import ring_theory.int.basic
import tactic.basic
import tactic.ring_exp
import number_theory.divisors
import data.nat.factorization

/-!
# p-adic norm

This file defines the p-adic valuation and the p-adic norm on ℚ.

The p-adic valuation on ℚ is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on p.

The valuation induces a norm on ℚ. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Notations

This file uses the local notation `/.` for `rat.mk`.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[fact (prime p)]` as a type class argument.

## References

* [F. Q. Gouêva, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/

universe u

open nat

open_locale rat

open multiplicity

/--
For `p ≠ 1`, the p-adic valuation of an integer `z ≠ 0` is the largest natural number `n` such that
p^n divides z.

`padic_val_rat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.denom`.
If `q = 0` or `p = 1`, then `padic_val_rat p q` defaults to 0.
-/
def padic_val_rat (p : ℕ) (q : ℚ) : ℤ :=
if h : q ≠ 0 ∧ p ≠ 1
then (multiplicity (p : ℤ) q.num).get
    (multiplicity.finite_int_iff.2 ⟨h.2, rat.num_ne_zero_of_ne_zero h.1⟩) -
  (multiplicity (p : ℤ) q.denom).get
    (multiplicity.finite_int_iff.2 ⟨h.2, by exact_mod_cast rat.denom_ne_zero _⟩)
else 0

/--
A simplification of the definition of `padic_val_rat p q` when `q ≠ 0` and `p` is prime.
-/
lemma padic_val_rat_def (p : ℕ) [hp : fact p.prime] {q : ℚ} (hq : q ≠ 0) : padic_val_rat p q =
  (multiplicity (p : ℤ) q.num).get (finite_int_iff.2 ⟨hp.1.ne_one, rat.num_ne_zero_of_ne_zero hq⟩) -
  (multiplicity (p : ℤ) q.denom).get
    (finite_int_iff.2 ⟨hp.1.ne_one, by exact_mod_cast rat.denom_ne_zero _⟩) :=
dif_pos ⟨hq, hp.1.ne_one⟩

namespace padic_val_rat
open multiplicity
variables {p : ℕ}

/--
`padic_val_rat p q` is symmetric in `q`.
-/
@[simp] protected lemma neg (q : ℚ) : padic_val_rat p (-q) = padic_val_rat p q :=
begin
  unfold padic_val_rat,
  split_ifs,
  { simp [-add_comm]; refl },
  { exfalso, simp * at * },
  { exfalso, simp * at * },
  { refl }
end

/--
`padic_val_rat p 0` is 0 for any `p`.
-/
@[simp]
protected lemma zero (m : nat) : padic_val_rat m 0 = 0 := rfl

/--
`padic_val_rat p 1` is 0 for any `p`.
-/
@[simp] protected lemma one : padic_val_rat p 1 = 0 :=
by unfold padic_val_rat; split_ifs; simp *

/--
For `p ≠ 0, p ≠ 1, `padic_val_rat p p` is 1.
-/
@[simp] lemma padic_val_rat_self (hp : 1 < p) : padic_val_rat p p = 1 :=
by unfold padic_val_rat; split_ifs; simp [*, nat.one_lt_iff_ne_zero_and_ne_one] at *

/--
The p-adic value of an integer `z ≠ 0` is the multiplicity of `p` in `z`.
-/
lemma padic_val_rat_of_int (z : ℤ) (hp : p ≠ 1) (hz : z ≠ 0) :
  padic_val_rat p (z : ℚ) = (multiplicity (p : ℤ) z).get
    (finite_int_iff.2 ⟨hp, hz⟩) :=
by rw [padic_val_rat, dif_pos]; simp *; refl

end padic_val_rat

/--
A convenience function for the case of `padic_val_rat` when both inputs are natural numbers.
-/
def padic_val_nat (p : ℕ) (n : ℕ) : ℕ :=
int.to_nat (padic_val_rat p n)

section padic_val_nat

/--
`padic_val_nat` is defined as an `int.to_nat` cast;
this lemma ensures that the cast is well-behaved.
-/
lemma zero_le_padic_val_rat_of_nat (p n : ℕ) : 0 ≤ padic_val_rat p n :=
begin
  unfold padic_val_rat,
  split_ifs,
  { simp, },
  { trivial, },
end

/--
`padic_val_rat` coincides with `padic_val_nat`.
-/
@[simp, norm_cast] lemma padic_val_rat_of_nat (p n : ℕ) :
  ↑(padic_val_nat p n) = padic_val_rat p n :=
begin
  unfold padic_val_nat,
  rw int.to_nat_of_nonneg (zero_le_padic_val_rat_of_nat p n),
end

/--
A simplification of `padic_val_nat` when one input is prime, by analogy with `padic_val_rat_def`.
-/
lemma padic_val_nat_def {p : ℕ} [hp : fact p.prime] {n : ℕ} (hn : n ≠ 0) :
  padic_val_nat p n =
  (multiplicity p n).get
    (multiplicity.finite_nat_iff.2 ⟨nat.prime.ne_one hp.1, bot_lt_iff_ne_bot.mpr hn⟩) :=
begin
  have n_nonzero : (n : ℚ) ≠ 0, by simpa only [cast_eq_zero, ne.def],
  -- Infinite loop with @simp padic_val_rat_of_nat unless we restrict the available lemmas here,
  -- hence the very long list
  simpa only
    [ int.coe_nat_multiplicity p n, rat.coe_nat_denom n, (padic_val_rat_of_nat p n).symm,
      int.coe_nat_zero, int.coe_nat_inj', sub_zero, get_one_right, int.coe_nat_succ, zero_add,
      rat.coe_nat_num ]
    using padic_val_rat_def p n_nonzero,
end

@[simp] lemma padic_val_nat_self (p : ℕ) [fact p.prime] : padic_val_nat p p = 1 :=
by simp [padic_val_nat_def (fact.out p.prime).ne_zero]

lemma one_le_padic_val_nat_of_dvd
  {n p : nat} [prime : fact p.prime] (nonzero : n ≠ 0) (div : p ∣ n) :
  1 ≤ padic_val_nat p n :=
begin
  rw @padic_val_nat_def _ prime _ nonzero,
  let one_le_mul : _ ≤ multiplicity p n :=
    @multiplicity.le_multiplicity_of_pow_dvd _ _ _ p n 1 (begin norm_num, exact div end),
  simp only [nat.cast_one] at one_le_mul,
  rcases one_le_mul with ⟨_, q⟩,
  dsimp at q,
  solve_by_elim,
end

@[simp]
lemma padic_val_nat_zero (m : nat) : padic_val_nat m 0 = 0 := rfl

@[simp]
lemma padic_val_nat_one (m : nat) : padic_val_nat m 1 = 0 := by simp [padic_val_nat]

end padic_val_nat

namespace padic_val_rat
open multiplicity
variables (p : ℕ) [p_prime : fact p.prime]
include p_prime

/--
The multiplicity of `p : ℕ` in `a : ℤ` is finite exactly when `a ≠ 0`.
-/
lemma finite_int_prime_iff {p : ℕ} [p_prime : fact p.prime] {a : ℤ} : finite (p : ℤ) a ↔ a ≠ 0 :=
by simp [finite_int_iff, ne.symm (ne_of_lt (p_prime.1.one_lt))]

/--
A rewrite lemma for `padic_val_rat p q` when `q` is expressed in terms of `rat.mk`.
-/
protected lemma defn {q : ℚ} {n d : ℤ} (hqz : q ≠ 0) (qdf : q = n /. d) :
  padic_val_rat p q = (multiplicity (p : ℤ) n).get (finite_int_iff.2
    ⟨ne.symm $ ne_of_lt p_prime.1.one_lt, λ hn, by simp * at *⟩) -
  (multiplicity (p : ℤ) d).get (finite_int_iff.2 ⟨ne.symm $ ne_of_lt p_prime.1.one_lt,
    λ hd, by simp * at *⟩) :=
have hn : n ≠ 0, from rat.mk_num_ne_zero_of_ne_zero hqz qdf,
have hd : d ≠ 0, from rat.mk_denom_ne_zero_of_ne_zero hqz qdf,
let ⟨c, hc1, hc2⟩ := rat.num_denom_mk hn hd qdf in
by rw [padic_val_rat, dif_pos];
  simp [hc1, hc2, multiplicity.mul' (nat.prime_iff_prime_int.1 p_prime.1),
    (ne.symm (ne_of_lt p_prime.1.one_lt)), hqz]

/--
A rewrite lemma for `padic_val_rat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected lemma mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q * r) = padic_val_rat p q + padic_val_rat p r :=
have q*r = (q.num * r.num) /. (↑q.denom * ↑r.denom), by rw_mod_cast rat.mul_num_denom,
have hq' : q.num /. q.denom ≠ 0, by rw rat.num_denom; exact hq,
have hr' : r.num /. r.denom ≠ 0, by rw rat.num_denom; exact hr,
have hp' : _root_.prime (p : ℤ), from nat.prime_iff_prime_int.1 p_prime.1,
begin
  rw [padic_val_rat.defn p (mul_ne_zero hq hr) this],
  conv_rhs { rw [←(@rat.num_denom q), padic_val_rat.defn p hq',
    ←(@rat.num_denom r), padic_val_rat.defn p hr'] },
  rw [multiplicity.mul' hp', multiplicity.mul' hp']; simp [add_comm, add_left_comm, sub_eq_add_neg]
end

/--
A rewrite lemma for `padic_val_rat p (q^k)` with condition `q ≠ 0`.
-/
protected lemma pow {q : ℚ} (hq : q ≠ 0) {k : ℕ} :
    padic_val_rat p (q ^ k) = k * padic_val_rat p q :=
by induction k; simp [*, padic_val_rat.mul _ hq (pow_ne_zero _ hq),
  pow_succ, add_mul, add_comm]

/--
A rewrite lemma for `padic_val_rat p (q⁻¹)` with condition `q ≠ 0`.
-/
protected lemma inv {q : ℚ} (hq : q ≠ 0) :
  padic_val_rat p (q⁻¹) = -padic_val_rat p q :=
by rw [eq_neg_iff_add_eq_zero, ← padic_val_rat.mul p (inv_ne_zero hq) hq,
    inv_mul_cancel hq, padic_val_rat.one]

/--
A rewrite lemma for `padic_val_rat p (q / r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected lemma div {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_rat p (q / r) = padic_val_rat p q - padic_val_rat p r :=
by rw [div_eq_mul_inv, padic_val_rat.mul p hq (inv_ne_zero hr),
    padic_val_rat.inv p hr, sub_eq_add_neg]

/--
A condition for `padic_val_rat p (n₁ / d₁) ≤ padic_val_rat p (n₂ / d₂),
in terms of divisibility by `p^n`.
-/
lemma padic_val_rat_le_padic_val_rat_iff {n₁ n₂ d₁ d₂ : ℤ}
  (hn₁ : n₁ ≠ 0) (hn₂ : n₂ ≠ 0) (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) :
  padic_val_rat p (n₁ /. d₁) ≤ padic_val_rat p (n₂ /. d₂) ↔
  ∀ (n : ℕ), ↑p ^ n ∣ n₁ * d₂ → ↑p ^ n ∣ n₂ * d₁ :=
have hf1 : finite (p : ℤ) (n₁ * d₂),
  from finite_int_prime_iff.2 (mul_ne_zero hn₁ hd₂),
have hf2 : finite (p : ℤ) (n₂ * d₁),
  from finite_int_prime_iff.2 (mul_ne_zero hn₂ hd₁),
  by conv
  { to_lhs,
    rw [padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₁ hd₁) rfl,
      padic_val_rat.defn p (rat.mk_ne_zero_of_ne_zero hn₂ hd₂) rfl,
      sub_le_iff_le_add',
      ← add_sub_assoc,
      le_sub_iff_add_le],
    norm_cast,
    rw [← multiplicity.mul' (nat.prime_iff_prime_int.1 p_prime.1) hf1, add_comm,
      ← multiplicity.mul' (nat.prime_iff_prime_int.1 p_prime.1) hf2,
      enat.get_le_get, multiplicity_le_multiplicity_iff] }

/--
Sufficient conditions to show that the p-adic valuation of `q` is less than or equal to the
p-adic vlauation of `q + r`.
-/
theorem le_padic_val_rat_add_of_le {q r : ℚ}
  (hqr : q + r ≠ 0)
  (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_val_rat p q ≤ padic_val_rat p (q + r) :=
if hq : q = 0 then by simpa [hq] using h else
if hr : r = 0 then by simp [hr] else
have hqn : q.num ≠ 0, from rat.num_ne_zero_of_ne_zero hq,
have hqd : (q.denom : ℤ) ≠ 0, by exact_mod_cast rat.denom_ne_zero _,
have hrn : r.num ≠ 0, from rat.num_ne_zero_of_ne_zero hr,
have hrd : (r.denom : ℤ) ≠ 0, by exact_mod_cast rat.denom_ne_zero _,
have hqreq : q + r = (((q.num * r.denom + q.denom * r.num : ℤ)) /. (↑q.denom * ↑r.denom : ℤ)),
  from rat.add_num_denom _ _,
have hqrd : q.num * ↑(r.denom) + ↑(q.denom) * r.num ≠ 0,
  from rat.mk_num_ne_zero_of_ne_zero hqr hqreq,
begin
  conv_lhs { rw ←(@rat.num_denom q) },
  rw [hqreq, padic_val_rat_le_padic_val_rat_iff p hqn hqrd hqd (mul_ne_zero hqd hrd),
    ← multiplicity_le_multiplicity_iff, mul_left_comm,
    multiplicity.mul (nat.prime_iff_prime_int.1 p_prime.1), add_mul],
  rw [←(@rat.num_denom q), ←(@rat.num_denom r),
    padic_val_rat_le_padic_val_rat_iff p hqn hrn hqd hrd, ← multiplicity_le_multiplicity_iff] at h,
  calc _ ≤ min (multiplicity ↑p (q.num * ↑(r.denom) * ↑(q.denom)))
    (multiplicity ↑p (↑(q.denom) * r.num * ↑(q.denom))) : (le_min
    (by rw [@multiplicity.mul _ _ _ _ (_ * _) _ (nat.prime_iff_prime_int.1 p_prime.1), add_comm])
    (by rw [mul_assoc, @multiplicity.mul _ _ _ _ (q.denom : ℤ)
        (_ * _) (nat.prime_iff_prime_int.1 p_prime.1)];
      exact add_le_add_left h _))
    ... ≤ _ : min_le_multiplicity_add
end

/--
The minimum of the valuations of `q` and `r` is less than or equal to the valuation of `q + r`.
-/
theorem min_le_padic_val_rat_add {q r : ℚ} (hqr : q + r ≠ 0) :
  min (padic_val_rat p q) (padic_val_rat p r) ≤ padic_val_rat p (q + r) :=
(le_total (padic_val_rat p q) (padic_val_rat p r)).elim
  (λ h, by rw [min_eq_left h]; exact le_padic_val_rat_add_of_le _ hqr h)
  (λ h, by rw [min_eq_right h, add_comm]; exact le_padic_val_rat_add_of_le _
    (by rwa add_comm) h)

open_locale big_operators

/-- A finite sum of rationals with positive p-adic valuation has positive p-adic valuation
  (if the sum is non-zero). -/
theorem sum_pos_of_pos {n : ℕ} {F : ℕ → ℚ}
  (hF : ∀ i, i < n → 0 < padic_val_rat p (F i)) (hn0 : ∑ i in finset.range n, F i ≠ 0) :
  0 < padic_val_rat p (∑ i in finset.range n, F i) :=
begin
  induction n with d hd,
  { exact false.elim (hn0 rfl) },
  { rw finset.sum_range_succ at hn0 ⊢,
    by_cases h : ∑ (x : ℕ) in finset.range d, F x = 0,
    { rw [h, zero_add],
      exact hF d (lt_add_one _) },
    { refine lt_of_lt_of_le _ (min_le_padic_val_rat_add p hn0),
      { refine lt_min (hd (λ i hi, _) h) (hF d (lt_add_one _)),
        exact hF _ (lt_trans hi (lt_add_one _)) }, } }
end

end padic_val_rat

namespace padic_val_nat

/--
A rewrite lemma for `padic_val_nat p (q * r)` with conditions `q ≠ 0`, `r ≠ 0`.
-/
protected lemma mul (p : ℕ) [p_prime : fact p.prime] {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) :
  padic_val_nat p (q * r) = padic_val_nat p q + padic_val_nat p r :=
begin
  apply int.coe_nat_inj,
  simp only [padic_val_rat_of_nat, nat.cast_mul],
  rw padic_val_rat.mul,
  norm_cast,
  exact cast_ne_zero.mpr hq,
  exact cast_ne_zero.mpr hr,
end

protected lemma div_of_dvd (p : ℕ) [hp : fact p.prime] {a b : ℕ} (h : b ∣ a) :
  padic_val_nat p (a / b) = padic_val_nat p a - padic_val_nat p b :=
begin
  rcases eq_or_ne a 0 with rfl | ha,
  { simp },
  obtain ⟨k, rfl⟩ := h,
  obtain ⟨hb, hk⟩ := mul_ne_zero_iff.mp ha,
  rw [mul_comm, k.mul_div_cancel hb.bot_lt, padic_val_nat.mul p hk hb, nat.add_sub_cancel]
end

/--
Dividing out by a prime factor reduces the padic_val_nat by 1.
-/
protected lemma div {p : ℕ} [p_prime : fact p.prime] {b : ℕ} (dvd : p ∣ b) :
  (padic_val_nat p (b / p)) = (padic_val_nat p b) - 1 :=
begin
  convert padic_val_nat.div_of_dvd p dvd,
  rw padic_val_nat_self p
end

/-- A version of `padic_val_rat.pow` for `padic_val_nat` -/
protected lemma pow (p q n : ℕ) [fact p.prime] (hq : q ≠ 0) :
  padic_val_nat p (q ^ n) = n * padic_val_nat p q :=
begin
  apply @nat.cast_injective ℤ,
  push_cast,
  exact padic_val_rat.pow _ (cast_ne_zero.mpr hq),
end

@[simp] protected lemma prime_pow (p n : ℕ) [fact p.prime] : padic_val_nat p (p ^ n) = n :=
by rw [padic_val_nat.pow p _ _ (fact.out p.prime).ne_zero, padic_val_nat_self p, mul_one]

protected lemma div_pow {p : ℕ} [p_prime : fact p.prime] {b k : ℕ} (dvd : p ^ k ∣ b) :
  (padic_val_nat p (b / p ^ k)) = (padic_val_nat p b) - k :=
begin
  convert padic_val_nat.div_of_dvd p dvd,
  rw padic_val_nat.prime_pow
end

end padic_val_nat

section padic_val_nat

/--
If a prime doesn't appear in `n`, `padic_val_nat p n` is `0`.
-/
lemma padic_val_nat_of_not_dvd {p : ℕ} [fact p.prime] {n : ℕ} (not_dvd : ¬(p ∣ n)) :
  padic_val_nat p n = 0 :=
begin
  by_cases hn : n = 0,
  { subst hn, simp at not_dvd, trivial, },
  { rw padic_val_nat_def hn,
    exact (@multiplicity.unique' _ _ _ p n 0 (by simp) (by simpa using not_dvd)).symm,
    assumption, },
end

lemma dvd_of_one_le_padic_val_nat {n p : nat} [prime : fact p.prime] (hp : 1 ≤ padic_val_nat p n) :
  p ∣ n :=
begin
  by_contra h,
  rw padic_val_nat_of_not_dvd h at hp,
  exact lt_irrefl 0 (lt_of_lt_of_le zero_lt_one hp),
end

lemma pow_padic_val_nat_dvd {p n : ℕ} [fact (nat.prime p)] : p ^ (padic_val_nat p n) ∣ n :=
begin
  cases nat.eq_zero_or_pos n with hn hn,
  { rw hn, exact dvd_zero (p ^ padic_val_nat p 0) },
  { rw multiplicity.pow_dvd_iff_le_multiplicity,
    apply le_of_eq,
    rw padic_val_nat_def (ne_of_gt hn),
    { apply enat.coe_get },
    { apply_instance } }
end

lemma pow_succ_padic_val_nat_not_dvd {p n : ℕ} [hp : fact (nat.prime p)] (hn : 0 < n) :
  ¬ p ^ (padic_val_nat p n + 1) ∣ n :=
begin
  { rw multiplicity.pow_dvd_iff_le_multiplicity,
    rw padic_val_nat_def (ne_of_gt hn),
    { rw [nat.cast_add, enat.coe_get],
      simp only [nat.cast_one, not_le],
      apply enat.lt_add_one (ne_top_iff_finite.2 (finite_nat_iff.2 ⟨hp.elim.ne_one, hn⟩)) },
    { apply_instance } }
end

lemma padic_val_nat_primes {p q : ℕ} [p_prime : fact p.prime] [q_prime : fact q.prime]
  (neq : p ≠ q) : padic_val_nat p q = 0 :=
@padic_val_nat_of_not_dvd p p_prime q $
(not_congr (iff.symm (prime_dvd_prime_iff_eq p_prime.1 q_prime.1))).mp neq

protected lemma padic_val_nat.div' {p : ℕ} [p_prime : fact p.prime] :
  ∀ {m : ℕ} (cpm : coprime p m) {b : ℕ} (dvd : m ∣ b), padic_val_nat p (b / m) = padic_val_nat p b
| 0 := λ cpm b dvd, by { rw zero_dvd_iff at dvd, rw [dvd, nat.zero_div], }
| (n + 1) :=
  λ cpm b dvd,
  begin
    rcases dvd with ⟨c, rfl⟩,
    rw [mul_div_right c (nat.succ_pos _)],by_cases hc : c = 0,
    { rw [hc, mul_zero] },
    { rw padic_val_nat.mul,
      { suffices : ¬ p ∣ (n+1),
        { rw [padic_val_nat_of_not_dvd this, zero_add] },
        contrapose! cpm,
        exact p_prime.1.dvd_iff_not_coprime.mp cpm },
      { exact nat.succ_ne_zero _ },
      { exact hc } },
  end

lemma padic_val_nat_eq_factorization (p : ℕ) [hp : fact p.prime] :
  ∀ (n : ℕ), padic_val_nat p n = n.factorization p
| 0 := by simp
| 1 := by simp
| (m + 2) :=
let n := m + 2 in
let q := min_fac n in
have hq : fact q.prime := ⟨min_fac_prime (show m + 2 ≠ 1, by linarith)⟩,
have wf : n / q < n := nat.div_lt_self (nat.succ_pos _) hq.1.one_lt,
begin
  rw [←factors_count_eq, factors_add_two],
  show padic_val_nat p n = list.count p (q :: (factors (n / q))),
  rw [list.count_cons', factors_count_eq, ← padic_val_nat_eq_factorization],
  split_ifs with h,
  { have hp : p ∣ n := h.symm ▸ nat.min_fac_dvd n,
    rw [←h, padic_val_nat.div hp],
    exact (tsub_eq_iff_eq_add_of_le $ one_le_padic_val_nat_of_dvd (by linarith) hp).mp rfl, },
  { suffices : p.coprime q,
    { rw [padic_val_nat.div' this (min_fac_dvd n), add_zero] },
    rwa nat.coprime_primes hp.1 hq.1, },
end

open_locale big_operators

lemma prod_pow_prime_padic_val_nat (n : nat) (hn : n ≠ 0) (m : nat) (pr : n < m) :
  ∏ p in finset.filter nat.prime (finset.range m), p ^ (padic_val_nat p n) = n :=
begin
  nth_rewrite_rhs 0 ←factorization_prod_pow_eq_self hn,
  rw eq_comm,
  apply finset.prod_subset_one_on_sdiff,
  { exact λ p hp, finset.mem_filter.mpr
      ⟨finset.mem_range.mpr (gt_of_gt_of_ge pr (le_of_mem_factorization hp)),
       prime_of_mem_factorization hp⟩ },
  { intros p hp,
    cases finset.mem_sdiff.mp hp with hp1 hp2,
    haveI := fact_iff.mpr (finset.mem_filter.mp hp1).2,
    rw padic_val_nat_eq_factorization p n,
    simp [finsupp.not_mem_support_iff.mp hp2] },
  { intros p hp,
    haveI := fact_iff.mpr (prime_of_mem_factorization hp),
    simp [padic_val_nat_eq_factorization] }
end

lemma range_pow_padic_val_nat_subset_divisors {n : ℕ} (p : ℕ) [fact p.prime] (hn : n ≠ 0) :
  (finset.range (padic_val_nat p n + 1)).image (pow p) ⊆ n.divisors :=
begin
  intros t ht,
  simp only [exists_prop, finset.mem_image, finset.mem_range] at ht,
  obtain ⟨k, hk, rfl⟩ := ht,
  rw nat.mem_divisors,
  exact ⟨(pow_dvd_pow p $ by linarith).trans pow_padic_val_nat_dvd, hn⟩
end

lemma range_pow_padic_val_nat_subset_divisors' {n : ℕ} (p : ℕ) [h : fact p.prime] :
  (finset.range (padic_val_nat p n)).image (λ t, p ^ (t + 1)) ⊆ (n.divisors \ {1}) :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp },
  intros t ht,
  simp only [exists_prop, finset.mem_image, finset.mem_range] at ht,
  obtain ⟨k, hk, rfl⟩ := ht,
  rw [finset.mem_sdiff, nat.mem_divisors],
  refine ⟨⟨(pow_dvd_pow p $ by linarith).trans pow_padic_val_nat_dvd, hn⟩, _⟩,
  rw [finset.mem_singleton],
  nth_rewrite 1 ←one_pow (k + 1),
  exact (nat.pow_lt_pow_of_lt_left h.1.one_lt $ nat.succ_pos k).ne',
end

end padic_val_nat

/--
If `q ≠ 0`, the p-adic norm of a rational `q` is `p ^ (-(padic_val_rat p q))`.
If `q = 0`, the p-adic norm of `q` is 0.
-/
def padic_norm (p : ℕ) (q : ℚ) : ℚ :=
if q = 0 then 0 else (↑p : ℚ) ^ (-(padic_val_rat p q))

namespace padic_norm

section padic_norm
open padic_val_rat
variables (p : ℕ)

/--
Unfolds the definition of the p-adic norm of `q` when `q ≠ 0`.
-/
@[simp] protected lemma eq_zpow_of_nonzero {q : ℚ} (hq : q ≠ 0) :
  padic_norm p q = p ^ (-(padic_val_rat p q)) :=
by simp [hq, padic_norm]

/--
The p-adic norm is nonnegative.
-/
protected lemma nonneg (q : ℚ) : 0 ≤ padic_norm p q :=
if hq : q = 0 then by simp [hq, padic_norm]
else
  begin
    unfold padic_norm; split_ifs,
    apply zpow_nonneg,
    exact_mod_cast nat.zero_le _
  end

/--
The p-adic norm of 0 is 0.
-/
@[simp] protected lemma zero : padic_norm p 0 = 0 := by simp [padic_norm]

/--
The p-adic norm of 1 is 1.
-/
@[simp] protected lemma one : padic_norm p 1 = 1 := by simp [padic_norm]

/--
The p-adic norm of `p` is `1/p` if `p > 1`.

See also `padic_norm.padic_norm_p_of_prime` for a version that assumes `p` is prime.
-/
lemma padic_norm_p {p : ℕ} (hp : 1 < p) : padic_norm p p = 1 / p :=
by simp [padic_norm, (show p ≠ 0, by linarith), padic_val_rat.padic_val_rat_self hp]

/--
The p-adic norm of `p` is `1/p` if `p` is prime.

See also `padic_norm.padic_norm_p` for a version that assumes `1 < p`.
-/
@[simp] lemma padic_norm_p_of_prime (p : ℕ) [fact p.prime] : padic_norm p p = 1 / p :=
padic_norm_p $ nat.prime.one_lt (fact.out _)

/-- The p-adic norm of `q` is `1` if `q` is prime and not equal to `p`. -/
lemma padic_norm_of_prime_of_ne {p q : ℕ} [p_prime : fact p.prime] [q_prime : fact q.prime]
  (neq : p ≠ q) : padic_norm p q = 1 :=
begin
  have p : padic_val_rat p q = 0,
  { exact_mod_cast @padic_val_nat_primes p q p_prime q_prime neq },
  simp [padic_norm, p, q_prime.1.1, q_prime.1.ne_zero],
end

/--
The p-adic norm of `p` is less than 1 if `1 < p`.

See also `padic_norm.padic_norm_p_lt_one_of_prime` for a version assuming `prime p`.
-/
lemma padic_norm_p_lt_one {p : ℕ} (hp : 1 < p) : padic_norm p p < 1 :=
begin
  rw [padic_norm_p hp, div_lt_iff, one_mul],
  { exact_mod_cast hp },
  { exact_mod_cast zero_lt_one.trans hp },
end

/--
The p-adic norm of `p` is less than 1 if `p` is prime.

See also `padic_norm.padic_norm_p_lt_one` for a version assuming `1 < p`.
-/
lemma padic_norm_p_lt_one_of_prime (p : ℕ) [fact p.prime] : padic_norm p p < 1 :=
padic_norm_p_lt_one $ nat.prime.one_lt (fact.out _)

/--
`padic_norm p q` takes discrete values `p ^ -z` for `z : ℤ`.
-/
protected theorem values_discrete {q : ℚ} (hq : q ≠ 0) : ∃ z : ℤ, padic_norm p q = p ^ (-z) :=
⟨ (padic_val_rat p q), by simp [padic_norm, hq] ⟩

/--
`padic_norm p` is symmetric.
-/
@[simp] protected lemma neg (q : ℚ) : padic_norm p (-q) = padic_norm p q :=
if hq : q = 0 then by simp [hq]
else by simp [padic_norm, hq]

variable [hp : fact p.prime]
include hp

/--
If `q ≠ 0`, then `padic_norm p q ≠ 0`.
-/
protected lemma nonzero {q : ℚ} (hq : q ≠ 0) : padic_norm p q ≠ 0 :=
begin
  rw padic_norm.eq_zpow_of_nonzero p hq,
  apply zpow_ne_zero_of_ne_zero,
  exact_mod_cast ne_of_gt hp.1.pos
end

/--
If the p-adic norm of `q` is 0, then `q` is 0.
-/
lemma zero_of_padic_norm_eq_zero {q : ℚ} (h : padic_norm p q = 0) : q = 0 :=
begin
  apply by_contradiction, intro hq,
  unfold padic_norm at h, rw if_neg hq at h,
  apply absurd h,
  apply zpow_ne_zero_of_ne_zero,
  exact_mod_cast hp.1.ne_zero
end

/--
The p-adic norm is multiplicative.
-/
@[simp] protected theorem mul (q r : ℚ) : padic_norm p (q*r) = padic_norm p q * padic_norm p r :=
if hq : q = 0 then
  by simp [hq]
else if hr : r = 0 then
  by simp [hr]
else
  have q*r ≠ 0, from mul_ne_zero hq hr,
  have (↑p : ℚ) ≠ 0, by simp [hp.1.ne_zero],
  by simp [padic_norm, *, padic_val_rat.mul, zpow_add₀ this, mul_comm]

/--
The p-adic norm respects division.
-/
@[simp] protected theorem div (q r : ℚ) : padic_norm p (q / r) = padic_norm p q / padic_norm p r :=
if hr : r = 0 then by simp [hr] else
eq_div_of_mul_eq (padic_norm.nonzero _ hr) (by rw [←padic_norm.mul, div_mul_cancel _ hr])

/--
The p-adic norm of an integer is at most 1.
-/
protected theorem of_int (z : ℤ) : padic_norm p ↑z ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one] else
begin
  unfold padic_norm,
  rw [if_neg _],
  { refine zpow_le_one_of_nonpos _ _,
    { exact_mod_cast le_of_lt hp.1.one_lt, },
    { rw [padic_val_rat_of_int _ hp.1.ne_one hz, neg_nonpos],
      norm_cast, simp }},
  exact_mod_cast hz
end

private lemma nonarchimedean_aux {q r : ℚ} (h : padic_val_rat p q ≤ padic_val_rat p r) :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
have hnqp : padic_norm p q ≥ 0, from padic_norm.nonneg _ _,
have hnrp : padic_norm p r ≥ 0, from padic_norm.nonneg _ _,
if hq : q = 0 then
  by simp [hq, max_eq_right hnrp, le_max_right]
else if hr : r = 0 then
  by simp [hr, max_eq_left hnqp, le_max_left]
else if hqr : q + r = 0 then
  le_trans (by simpa [hqr] using hnqp) (le_max_left _ _)
else
  begin
    unfold padic_norm, split_ifs,
    apply le_max_iff.2,
    left,
    apply zpow_le_of_le,
    { exact_mod_cast le_of_lt hp.1.one_lt },
    { apply neg_le_neg,
      have : padic_val_rat p q =
              min (padic_val_rat p q) (padic_val_rat p r),
        from (min_eq_left h).symm,
      rw this,
      apply min_le_padic_val_rat_add; assumption }
  end

/--
The p-adic norm is nonarchimedean: the norm of `p + q` is at most the max of the norm of `p` and
the norm of `q`.
-/
protected theorem nonarchimedean {q r : ℚ} :
  padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) :=
begin
    wlog hle := le_total (padic_val_rat p q) (padic_val_rat p r) using [q r],
    exact nonarchimedean_aux p hle
end

/--
The p-adic norm respects the triangle inequality: the norm of `p + q` is at most the norm of `p`
plus the norm of `q`.
-/
theorem triangle_ineq (q r : ℚ) : padic_norm p (q + r) ≤ padic_norm p q + padic_norm p r :=
calc padic_norm p (q + r) ≤ max (padic_norm p q) (padic_norm p r) : padic_norm.nonarchimedean p
                       ... ≤ padic_norm p q + padic_norm p r :
                         max_le_add_of_nonneg (padic_norm.nonneg p _) (padic_norm.nonneg p _)

/--
The p-adic norm of a difference is at most the max of each component. Restates the archimedean
property of the p-adic norm.
-/
protected theorem sub {q r : ℚ} : padic_norm p (q - r) ≤ max (padic_norm p q) (padic_norm p r) :=
by rw [sub_eq_add_neg, ←padic_norm.neg p r]; apply padic_norm.nonarchimedean

/--
If the p-adic norms of `q` and `r` are different, then the norm of `q + r` is equal to the max of
the norms of `q` and `r`.
-/
lemma add_eq_max_of_ne {q r : ℚ} (hne : padic_norm p q ≠ padic_norm p r) :
  padic_norm p (q + r) = max (padic_norm p q) (padic_norm p r) :=
begin
  wlog hle := le_total (padic_norm p r) (padic_norm p q) using [q r],
  have hlt : padic_norm p r < padic_norm p q, from lt_of_le_of_ne hle hne.symm,
  have : padic_norm p q ≤ max (padic_norm p (q + r)) (padic_norm p r), from calc
   padic_norm p q = padic_norm p (q + r - r) : by congr; ring
               ... ≤ max (padic_norm p (q + r)) (padic_norm p (-r)) : padic_norm.nonarchimedean p
               ... = max (padic_norm p (q + r)) (padic_norm p r) : by simp,
  have hnge : padic_norm p r ≤ padic_norm p (q + r),
  { apply le_of_not_gt,
    intro hgt,
    rw max_eq_right_of_lt hgt at this,
    apply not_lt_of_ge this,
    assumption },
  have : padic_norm p q ≤ padic_norm p (q + r), by rwa [max_eq_left hnge] at this,
  apply _root_.le_antisymm,
  { apply padic_norm.nonarchimedean p },
  { rw max_eq_left_of_lt hlt,
    assumption }
end

/--
The p-adic norm is an absolute value: positive-definite and multiplicative, satisfying the triangle
inequality.
-/
instance : is_absolute_value (padic_norm p) :=
{ abv_nonneg := padic_norm.nonneg p,
  abv_eq_zero :=
    begin
      intros,
      constructor; intro,
      { apply zero_of_padic_norm_eq_zero p, assumption },
      { simp [*] }
    end,
  abv_add := padic_norm.triangle_ineq p,
  abv_mul := padic_norm.mul p }

variable {p}

lemma dvd_iff_norm_le {n : ℕ} {z : ℤ} : ↑(p^n) ∣ z ↔ padic_norm p z ≤ ↑p ^ (-n : ℤ) :=
begin
  unfold padic_norm, split_ifs with hz,
  { norm_cast at hz,
    have : 0 ≤ (p^n : ℚ), {apply pow_nonneg, exact_mod_cast le_of_lt hp.1.pos },
    simp [hz, this] },
  { rw [zpow_le_iff_le, neg_le_neg_iff, padic_val_rat_of_int _ hp.1.ne_one _],
    { norm_cast,
      rw [← enat.coe_le_coe, enat.coe_get, ← multiplicity.pow_dvd_iff_le_multiplicity],
      simp },
    { exact_mod_cast hz },
    { exact_mod_cast hp.1.one_lt } }
end

end padic_norm
end padic_norm
