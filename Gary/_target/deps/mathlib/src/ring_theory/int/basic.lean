/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Aaron Anderson
-/
import ring_theory.coprime.basic
import ring_theory.principal_ideal_domain

/-!
# Divisibility over ℕ and ℤ

This file collects results for the integers and natural numbers that use abstract algebra in
their proofs or cases of ℕ and ℤ being examples of structures in abstract algebra.

## Main statements

* `nat.factors_eq`: the multiset of elements of `nat.factors` is equal to the factors
   given by the `unique_factorization_monoid` instance
* ℤ is a `normalization_monoid`
* ℤ is a `gcd_monoid`

## Tags

prime, irreducible, natural numbers, integers, normalization monoid, gcd monoid,
greatest common divisor, prime factorization, prime factors, unique factorization,
unique factors
-/

namespace nat

instance : wf_dvd_monoid ℕ :=
⟨begin
  refine rel_hom_class.well_founded
    (⟨λ (x : ℕ), if x = 0 then (⊤ : with_top ℕ) else x, _⟩ : dvd_not_unit →r (<))
    (with_top.well_founded_lt nat.lt_wf),
  intros a b h,
  cases a,
  { exfalso, revert h, simp [dvd_not_unit] },
  cases b,
  { simp [succ_ne_zero, with_top.coe_lt_top] },
  cases dvd_and_not_dvd_iff.2 h with h1 h2,
  simp only [succ_ne_zero, with_top.coe_lt_coe, if_false],
  apply lt_of_le_of_ne (nat.le_of_dvd (nat.succ_pos _) h1) (λ con, h2 _),
  rw con,
end⟩

instance : unique_factorization_monoid ℕ :=
⟨λ _, nat.irreducible_iff_prime⟩

end nat

/-- `ℕ` is a gcd_monoid. -/
instance : gcd_monoid ℕ :=
{ gcd := nat.gcd,
  lcm := nat.lcm,
  gcd_dvd_left := nat.gcd_dvd_left ,
  gcd_dvd_right := nat.gcd_dvd_right,
  dvd_gcd := λ a b c, nat.dvd_gcd,
  gcd_mul_lcm := λ a b, by rw [nat.gcd_mul_lcm],
  lcm_zero_left := nat.lcm_zero_left,
  lcm_zero_right := nat.lcm_zero_right }

instance : normalized_gcd_monoid ℕ :=
{ normalize_gcd := λ a b, normalize_eq _,
  normalize_lcm := λ a b, normalize_eq _,
  .. (infer_instance : gcd_monoid ℕ),
  .. (infer_instance : normalization_monoid ℕ) }

lemma gcd_eq_nat_gcd (m n : ℕ) : gcd m n = nat.gcd m n := rfl

lemma lcm_eq_nat_lcm (m n : ℕ) : lcm m n = nat.lcm m n := rfl

namespace int

section normalization_monoid

instance : normalization_monoid ℤ :=
{ norm_unit      := λa:ℤ, if 0 ≤ a then 1 else -1,
  norm_unit_zero := if_pos le_rfl,
  norm_unit_mul  := assume a b hna hnb,
  begin
    cases hna.lt_or_lt with ha ha; cases hnb.lt_or_lt with hb hb;
      simp [mul_nonneg_iff, ha.le, ha.not_le, hb.le, hb.not_le]
  end,
  norm_unit_coe_units := assume u, (units_eq_one_or u).elim
    (assume eq, eq.symm ▸ if_pos zero_le_one)
    (assume eq, eq.symm ▸ if_neg (not_le_of_gt $ show (-1:ℤ) < 0, by dec_trivial)), }

lemma normalize_of_nonneg {z : ℤ} (h : 0 ≤ z) : normalize z = z :=
show z * ↑(ite _ _ _) = z, by rw [if_pos h, units.coe_one, mul_one]

lemma normalize_of_neg {z : ℤ} (h : z < 0) : normalize z = -z :=
show z * ↑(ite _ _ _) = -z,
by rw [if_neg (not_le_of_gt h), units.coe_neg, units.coe_one, mul_neg_one]

lemma normalize_coe_nat (n : ℕ) : normalize (n : ℤ) = n :=
normalize_of_nonneg (coe_nat_le_coe_nat_of_le $ nat.zero_le n)

theorem coe_nat_abs_eq_normalize (z : ℤ) : (z.nat_abs : ℤ) = normalize z :=
begin
  by_cases 0 ≤ z,
  { simp [nat_abs_of_nonneg h, normalize_of_nonneg h] },
  { simp [of_nat_nat_abs_of_nonpos (le_of_not_ge h), normalize_of_neg (lt_of_not_ge h)] }
end

lemma nonneg_of_normalize_eq_self {z : ℤ} (hz : normalize z = z) : 0 ≤ z :=
calc 0 ≤ (z.nat_abs : ℤ) : coe_zero_le _
... = normalize z : coe_nat_abs_eq_normalize _
... = z : hz

lemma nonneg_iff_normalize_eq_self (z : ℤ) : normalize z = z ↔ 0 ≤ z :=
⟨nonneg_of_normalize_eq_self, normalize_of_nonneg⟩

lemma eq_of_associated_of_nonneg {a b : ℤ} (h : associated a b) (ha : 0 ≤ a) (hb : 0 ≤ b) : a = b :=
dvd_antisymm_of_normalize_eq (normalize_of_nonneg ha) (normalize_of_nonneg hb) h.dvd h.symm.dvd

end normalization_monoid

section gcd_monoid

instance : gcd_monoid ℤ :=
{ gcd            := λa b, int.gcd a b,
  lcm            := λa b, int.lcm a b,
  gcd_dvd_left   := assume a b, int.gcd_dvd_left _ _,
  gcd_dvd_right  := assume a b, int.gcd_dvd_right _ _,
  dvd_gcd        := assume a b c, dvd_gcd,
  gcd_mul_lcm    := λ a b, by
  { rw [← int.coe_nat_mul, gcd_mul_lcm, coe_nat_abs_eq_normalize],
    exact normalize_associated (a * b) },
  lcm_zero_left  := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_left _,
  lcm_zero_right := assume a, coe_nat_eq_zero.2 $ nat.lcm_zero_right _}

instance : normalized_gcd_monoid ℤ :=
{ normalize_gcd  := λ a b, normalize_coe_nat _,
  normalize_lcm  := λ a b, normalize_coe_nat _,
  .. int.normalization_monoid,
  .. (infer_instance : gcd_monoid ℤ) }

lemma coe_gcd (i j : ℤ) : ↑(int.gcd i j) = gcd_monoid.gcd i j := rfl
lemma coe_lcm (i j : ℤ) : ↑(int.lcm i j) = gcd_monoid.lcm i j := rfl

lemma nat_abs_gcd (i j : ℤ) : nat_abs (gcd_monoid.gcd i j) = int.gcd i j := rfl
lemma nat_abs_lcm (i j : ℤ) : nat_abs (gcd_monoid.lcm i j) = int.lcm i j := rfl

end gcd_monoid

lemma exists_unit_of_abs (a : ℤ) : ∃ (u : ℤ) (h : is_unit u), (int.nat_abs a : ℤ) = u * a :=
begin
  cases (nat_abs_eq a) with h,
  { use [1, is_unit_one], rw [← h, one_mul], },
  { use [-1, is_unit_one.neg], rw [ ← neg_eq_iff_neg_eq.mp (eq.symm h)],
    simp only [neg_mul, one_mul] }
end

lemma gcd_eq_nat_abs {a b : ℤ} : int.gcd a b = nat.gcd a.nat_abs b.nat_abs := rfl

lemma gcd_eq_one_iff_coprime {a b : ℤ} : int.gcd a b = 1 ↔ is_coprime a b :=
begin
  split,
  { intro hg,
    obtain ⟨ua, hua, ha⟩ := exists_unit_of_abs a,
    obtain ⟨ub, hub, hb⟩ := exists_unit_of_abs b,
    use [(nat.gcd_a (int.nat_abs a) (int.nat_abs b)) * ua,
        (nat.gcd_b (int.nat_abs a) (int.nat_abs b)) * ub],
    rw [mul_assoc, ← ha, mul_assoc, ← hb, mul_comm, mul_comm _ (int.nat_abs b : ℤ),
      ← nat.gcd_eq_gcd_ab, ←gcd_eq_nat_abs, hg, int.coe_nat_one] },
  { rintro ⟨r, s, h⟩,
    by_contradiction hg,
    obtain ⟨p, ⟨hp, ha, hb⟩⟩ := nat.prime.not_coprime_iff_dvd.mp hg,
    apply nat.prime.not_dvd_one hp,
    rw [←coe_nat_dvd, int.coe_nat_one, ← h],
    exact dvd_add ((coe_nat_dvd_left.mpr ha).mul_left _)
      ((coe_nat_dvd_left.mpr hb).mul_left _) }
end

lemma coprime_iff_nat_coprime {a b : ℤ} : is_coprime a b ↔ nat.coprime a.nat_abs b.nat_abs :=
by rw [←gcd_eq_one_iff_coprime, nat.coprime_iff_gcd_eq_one, gcd_eq_nat_abs]

lemma sq_of_gcd_eq_one {a b c : ℤ} (h : int.gcd a b = 1) (heq : a * b = c ^ 2) :
  ∃ (a0 : ℤ), a = a0 ^ 2 ∨ a = - (a0 ^ 2) :=
begin
  have h' : is_unit (gcd_monoid.gcd a b), { rw [← coe_gcd, h, int.coe_nat_one], exact is_unit_one },
  obtain ⟨d, ⟨u, hu⟩⟩ := exists_associated_pow_of_mul_eq_pow h' heq,
  use d,
  rw ← hu,
  cases int.units_eq_one_or u with hu' hu'; { rw hu', simp }
end

lemma sq_of_coprime {a b c : ℤ} (h : is_coprime a b) (heq : a * b = c ^ 2) :
  ∃ (a0 : ℤ), a = a0 ^ 2 ∨ a = - (a0 ^ 2) := sq_of_gcd_eq_one (gcd_eq_one_iff_coprime.mpr h) heq

lemma nat_abs_euclidean_domain_gcd (a b : ℤ) :
  int.nat_abs (euclidean_domain.gcd a b) = int.gcd a b :=
begin
  apply nat.dvd_antisymm; rw ← int.coe_nat_dvd,
  { rw int.nat_abs_dvd,
    exact int.dvd_gcd (euclidean_domain.gcd_dvd_left _ _) (euclidean_domain.gcd_dvd_right _ _) },
  { rw int.dvd_nat_abs,
    exact euclidean_domain.dvd_gcd (int.gcd_dvd_left _ _) (int.gcd_dvd_right _ _) }
end

end int

lemma nat.prime_iff_prime_int {p : ℕ} : p.prime ↔ _root_.prime (p : ℤ) :=
⟨λ hp, ⟨int.coe_nat_ne_zero_iff_pos.2 hp.pos, mt int.is_unit_iff_nat_abs_eq.1 hp.ne_one,
  λ a b h, by rw [← int.dvd_nat_abs, int.coe_nat_dvd, int.nat_abs_mul, hp.dvd_mul] at h;
    rwa [← int.dvd_nat_abs, int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd]⟩,
  λ hp, nat.prime_iff.2 ⟨int.coe_nat_ne_zero.1 hp.1,
      mt nat.is_unit_iff.1 $ λ h, by simpa [h, not_prime_one] using hp,
    λ a b, by simpa only [int.coe_nat_dvd, (int.coe_nat_mul _ _).symm] using hp.2.2 a b⟩⟩

/-- Maps an associate class of integers consisting of `-n, n` to `n : ℕ` -/
def associates_int_equiv_nat : associates ℤ ≃ ℕ :=
begin
  refine ⟨λz, z.out.nat_abs, λn, associates.mk n, _, _⟩,
  { refine (assume a, quotient.induction_on' a $ assume a,
      associates.mk_eq_mk_iff_associated.2 $ associated.symm $ ⟨norm_unit a, _⟩),
    show normalize a = int.nat_abs (normalize a),
    rw [int.coe_nat_abs_eq_normalize, normalize_idem] },
  { intro n,
    dsimp,
    rw [←normalize_apply, ← int.coe_nat_abs_eq_normalize, int.nat_abs_of_nat, int.nat_abs_of_nat] }
end

lemma int.prime.dvd_mul {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : p ∣ m.nat_abs ∨ p ∣ n.nat_abs :=
begin
  apply (nat.prime.dvd_mul hp).mp,
  rw ← int.nat_abs_mul,
  exact int.coe_nat_dvd_left.mp h
end

lemma int.prime.dvd_mul' {m n : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ m * n) : (p : ℤ) ∣ m ∨ (p : ℤ) ∣ n :=
begin
  rw [int.coe_nat_dvd_left, int.coe_nat_dvd_left],
  exact int.prime.dvd_mul hp h
end

lemma int.prime.dvd_pow {n : ℤ} {k p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ n ^ k) : p  ∣ n.nat_abs :=
begin
  apply @nat.prime.dvd_of_dvd_pow _ _ k hp,
  rw ← int.nat_abs_pow,
  exact int.coe_nat_dvd_left.mp h
end

lemma int.prime.dvd_pow' {n : ℤ} {k p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ n ^ k) : (p : ℤ)  ∣ n :=
begin
  rw int.coe_nat_dvd_left,
  exact int.prime.dvd_pow hp h
end

lemma prime_two_or_dvd_of_dvd_two_mul_pow_self_two {m : ℤ} {p : ℕ}
  (hp : nat.prime p) (h : (p : ℤ) ∣ 2 * m ^ 2) : p = 2 ∨ p ∣ int.nat_abs m :=
begin
  cases int.prime.dvd_mul hp h with hp2 hpp,
  { apply or.intro_left,
    exact le_antisymm (nat.le_of_dvd zero_lt_two hp2) (nat.prime.two_le hp) },
  { apply or.intro_right,
    rw [sq, int.nat_abs_mul] at hpp,
    exact (or_self _).mp ((nat.prime.dvd_mul hp).mp hpp)}
end

lemma int.exists_prime_and_dvd {n : ℤ} (n2 : 2 ≤ n.nat_abs) : ∃ p, prime p ∧ p ∣ n :=
begin
  obtain ⟨p, pp, pd⟩ := nat.exists_prime_and_dvd n2,
  exact ⟨p, nat.prime_iff_prime_int.mp pp, int.coe_nat_dvd_left.mpr pd⟩,
end

open unique_factorization_monoid

theorem nat.factors_eq {n : ℕ} : normalized_factors n = n.factors :=
begin
  cases n, { simp },
  rw [← multiset.rel_eq, ← associated_eq_eq],
  apply factors_unique (irreducible_of_normalized_factor) _,
  { rw [multiset.coe_prod, nat.prod_factors n.succ_ne_zero],
    apply normalized_factors_prod (nat.succ_ne_zero _) },
  { apply_instance },
  { intros x hx,
    rw [nat.irreducible_iff_prime, ← nat.prime_iff],
    exact nat.prime_of_mem_factors hx }
end

lemma nat.factors_multiset_prod_of_irreducible
  {s : multiset ℕ} (h : ∀ (x : ℕ), x ∈ s → irreducible x) :
  normalized_factors (s.prod) = s :=
begin
  rw [← multiset.rel_eq, ← associated_eq_eq],
  apply unique_factorization_monoid.factors_unique irreducible_of_normalized_factor h
    (normalized_factors_prod _),
  rw [ne.def, multiset.prod_eq_zero_iff],
  intro con,
  exact not_irreducible_zero (h 0 con),
end

namespace multiplicity

lemma finite_int_iff_nat_abs_finite {a b : ℤ} : finite a b ↔ finite a.nat_abs b.nat_abs :=
by simp only [finite_def, ← int.nat_abs_dvd_iff_dvd, int.nat_abs_pow]

lemma finite_int_iff {a b : ℤ} : finite a b ↔ (a.nat_abs ≠ 1 ∧ b ≠ 0) :=
by rw [finite_int_iff_nat_abs_finite, finite_nat_iff, pos_iff_ne_zero, int.nat_abs_ne_zero]

instance decidable_nat : decidable_rel (λ a b : ℕ, (multiplicity a b).dom) :=
λ a b, decidable_of_iff _ finite_nat_iff.symm

instance decidable_int : decidable_rel (λ a b : ℤ, (multiplicity a b).dom) :=
λ a b, decidable_of_iff _ finite_int_iff.symm

end multiplicity

lemma induction_on_primes {P : ℕ → Prop} (h₀ : P 0) (h₁ : P 1)
  (h : ∀ p a : ℕ, p.prime → P a → P (p * a)) (n : ℕ) : P n :=
begin
  apply unique_factorization_monoid.induction_on_prime,
  exact h₀,
  { intros n h,
    rw nat.is_unit_iff.1 h,
    exact h₁, },
  { intros a p _ hp ha,
    exact h p a (nat.prime_iff.2 hp) ha, },
end

lemma int.associated_nat_abs (k : ℤ) : associated k k.nat_abs :=
associated_of_dvd_dvd (int.coe_nat_dvd_right.mpr dvd_rfl) (int.nat_abs_dvd.mpr dvd_rfl)

lemma int.prime_iff_nat_abs_prime {k : ℤ} : prime k ↔ nat.prime k.nat_abs :=
(int.associated_nat_abs k).prime_iff.trans nat.prime_iff_prime_int.symm

theorem int.associated_iff_nat_abs {a b : ℤ} : associated a b ↔ a.nat_abs = b.nat_abs :=
begin
  rw [←dvd_dvd_iff_associated, ←int.nat_abs_dvd_iff_dvd,
      ←int.nat_abs_dvd_iff_dvd, dvd_dvd_iff_associated],
  exact associated_iff_eq,
end

lemma int.associated_iff {a b : ℤ} : associated a b ↔ (a = b ∨ a = -b) :=
begin
  rw int.associated_iff_nat_abs,
  exact int.nat_abs_eq_nat_abs_iff,
end

namespace int

lemma zmultiples_nat_abs (a : ℤ) :
  add_subgroup.zmultiples (a.nat_abs : ℤ) = add_subgroup.zmultiples a :=
le_antisymm
  (add_subgroup.zmultiples_subset (mem_zmultiples_iff.mpr (dvd_nat_abs.mpr (dvd_refl a))))
  (add_subgroup.zmultiples_subset (mem_zmultiples_iff.mpr (nat_abs_dvd.mpr (dvd_refl a))))

lemma span_nat_abs (a : ℤ) : ideal.span ({a.nat_abs} : set ℤ) = ideal.span {a} :=
by { rw ideal.span_singleton_eq_span_singleton, exact (associated_nat_abs _).symm }

theorem eq_pow_of_mul_eq_pow_bit1_left {a b c : ℤ}
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ (bit1 k)) : ∃ d, a = d ^ (bit1 k) :=
begin
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hab h,
  replace hd := hd.symm,
  rw [associated_iff_nat_abs, nat_abs_eq_nat_abs_iff, ←neg_pow_bit1] at hd,
  obtain rfl|rfl := hd; exact ⟨_, rfl⟩,
end

theorem eq_pow_of_mul_eq_pow_bit1_right {a b c : ℤ}
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ (bit1 k)) : ∃ d, b = d ^ (bit1 k) :=
eq_pow_of_mul_eq_pow_bit1_left hab.symm (by rwa mul_comm at h)

theorem eq_pow_of_mul_eq_pow_bit1 {a b c : ℤ}
  (hab : is_coprime a b) {k : ℕ} (h : a * b = c ^ (bit1 k)) :
  (∃ d, a = d ^ (bit1 k)) ∧ (∃ e, b = e ^ (bit1 k)) :=
⟨eq_pow_of_mul_eq_pow_bit1_left hab h, eq_pow_of_mul_eq_pow_bit1_right hab h⟩

end int
