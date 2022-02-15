/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.polynomial.degree.definitions

/-!
# Cancel the leading terms of two polynomials

## Definition

* `cancel_leads p q`: the polynomial formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting.

## Main Results
The degree of `cancel_leads` is less than that of the larger of the two polynomials being cancelled.
Thus it is useful for induction or minimal-degree arguments.
-/
namespace polynomial
noncomputable theory
open_locale polynomial

variables {R : Type*}

section comm_ring
variables [comm_ring R] (p q : R[X])

/-- `cancel_leads p q` is formed by multiplying `p` and `q` by monomials so that they
  have the same leading term, and then subtracting. -/
def cancel_leads : R[X] :=
C p.leading_coeff * X ^ (p.nat_degree - q.nat_degree) * q -
C q.leading_coeff * X ^ (q.nat_degree - p.nat_degree) * p

variables {p q}

@[simp] lemma neg_cancel_leads : - p.cancel_leads q = q.cancel_leads p := neg_sub _ _

lemma dvd_cancel_leads_of_dvd_of_dvd {r : R[X]} (pq : p ∣ q) (pr : p ∣ r) :
  p ∣ q.cancel_leads r :=
dvd_sub (pr.trans (dvd.intro_left _ rfl)) (pq.trans (dvd.intro_left _ rfl))

end comm_ring

lemma nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree [comm_ring R] [is_domain R]
  {p q : R[X]} (h : p.nat_degree ≤ q.nat_degree) (hq : 0 < q.nat_degree) :
  (p.cancel_leads q).nat_degree < q.nat_degree :=
begin
  by_cases hp : p = 0,
  { convert hq,
    simp [hp, cancel_leads], },
  rw [cancel_leads, sub_eq_add_neg, tsub_eq_zero_iff_le.mpr h, pow_zero, mul_one],
  by_cases h0 :
      C p.leading_coeff * q + -(C q.leading_coeff * X ^ (q.nat_degree - p.nat_degree) * p) = 0,
  { convert hq,
    simp only [h0, nat_degree_zero], },
  have hq0 : ¬ q = 0,
  { contrapose! hq,
    simp [hq] },
  apply lt_of_le_of_ne,
  { rw [← with_bot.coe_le_coe, ← degree_eq_nat_degree h0, ← degree_eq_nat_degree hq0],
    apply le_trans (degree_add_le _ _),
    rw ← leading_coeff_eq_zero at hp hq0,
    simp only [max_le_iff, degree_C hp, degree_C hq0, le_refl q.degree, true_and, nat.cast_with_bot,
      nsmul_one, degree_neg, degree_mul, zero_add, degree_X, degree_pow],
    rw leading_coeff_eq_zero at hp hq0,
    rw [degree_eq_nat_degree hp, degree_eq_nat_degree hq0, ← with_bot.coe_add, with_bot.coe_le_coe,
      tsub_add_cancel_of_le h], },
  { contrapose! h0,
    rw [← leading_coeff_eq_zero, leading_coeff, h0, mul_assoc, mul_comm _ p,
      ← tsub_add_cancel_of_le h, add_comm _ p.nat_degree],
    simp only [coeff_mul_X_pow, coeff_neg, coeff_C_mul, add_tsub_cancel_left, coeff_add],
    rw [add_comm p.nat_degree, tsub_add_cancel_of_le h, ← leading_coeff, ← leading_coeff,
      mul_comm _ q.leading_coeff, ← sub_eq_add_neg, ← mul_sub, sub_self, mul_zero] }
end

end polynomial
