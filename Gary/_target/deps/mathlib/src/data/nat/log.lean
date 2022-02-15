/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Yaël Dillies
-/
import data.nat.pow
import tactic.by_contra

/-!
# Natural number logarithms

This file defines two `ℕ`-valued analogs of the logarithm of `n` with base `b`:
* `log b n`: Lower logarithm, or floor **log**. Greatest `k` such that `b^k ≤ n`.
* `clog b n`: Upper logarithm, or **c**eil **log**. Least `k` such that `n ≤ b^k`.

These are interesting because, for `1 < b`, `nat.log b` and `nat.clog b` are respectively right and
left adjoints of `nat.pow b`. See `pow_le_iff_le_log` and `le_pow_iff_clog_le`.
-/

namespace nat

/-! ### Floor logarithm -/

/-- `log b n`, is the logarithm of natural number `n` in base `b`. It returns the largest `k : ℕ`
such that `b^k ≤ n`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot] def log (b : ℕ) : ℕ → ℕ
| n :=
  if h : b ≤ n ∧ 1 < b then
    have n / b < n,
      from div_lt_self ((zero_lt_one.trans h.2).trans_le h.1) h.2,
    log (n / b) + 1
  else 0

lemma log_eq_zero {b n : ℕ} (hnb : n < b ∨ b ≤ 1) : log b n = 0 :=
begin
  rw [or_iff_not_and_not, not_lt, not_le] at hnb,
  rw [log, ←ite_not, if_pos hnb],
end

lemma log_of_one_lt_of_le {b n : ℕ} (h : 1 < b) (hn : b ≤ n) : log b n = log b (n / b) + 1 :=
begin
  rw log,
  exact if_pos ⟨hn, h⟩,
end

lemma log_of_lt {b n : ℕ} (hnb : n < b) : log b n = 0 :=
by rw [log, if_neg (λ h : b ≤ n ∧ 1 < b, h.1.not_lt hnb)]

lemma log_of_left_le_one {b n : ℕ} (hb : b ≤ 1) : log b n = 0 :=
by rw [log, if_neg (λ h : b ≤ n ∧ 1 < b, h.2.not_le hb)]

lemma log_eq_zero_iff {b n : ℕ} : log b n = 0 ↔ n < b ∨ b ≤ 1 :=
begin
  refine ⟨λ h_log, _, log_eq_zero⟩,
  by_contra' h,
  have := log_of_one_lt_of_le h.2 h.1,
  rw h_log at this,
  exact succ_ne_zero _ this.symm
end

lemma log_eq_one_iff {b n : ℕ} : log b n = 1 ↔ n < b * b ∧ 1 < b ∧ b ≤ n :=
-- This is best possible: if b = 2, n = 5, then 1 < b and b ≤ n but n > b * b.
begin
  refine ⟨λ h_log, _, _⟩,
  { have bound : 1 < b ∧ b ≤ n,
    { contrapose h_log,
      rw [not_and_distrib, not_lt, not_le, or_comm, ←log_eq_zero_iff] at h_log,
      rw h_log,
      exact nat.zero_ne_one, },
    cases bound with one_lt_b b_le_n,
    refine ⟨_, one_lt_b, b_le_n⟩,
    rw [log_of_one_lt_of_le one_lt_b b_le_n, succ_inj',
        log_eq_zero_iff, nat.div_lt_iff_lt_mul _ _ (lt_trans zero_lt_one one_lt_b)] at h_log,
    exact h_log.resolve_right (λ b_small, lt_irrefl _ (lt_of_lt_of_le one_lt_b b_small)), },
  { rintros ⟨h, one_lt_b, b_le_n⟩,
    rw [log_of_one_lt_of_le one_lt_b b_le_n, succ_inj',
        log_eq_zero_iff, nat.div_lt_iff_lt_mul _ _ (lt_trans zero_lt_one one_lt_b)],
    exact or.inl h, },
end

@[simp] lemma log_zero_left (n : ℕ) : log 0 n = 0 :=
log_of_left_le_one zero_le_one

@[simp] lemma log_zero_right (b : ℕ) : log b 0 = 0 :=
by { rw log, cases b; refl }

@[simp] lemma log_one_left (n : ℕ) : log 1 n = 0 :=
log_of_left_le_one le_rfl

@[simp] lemma log_one_right (b : ℕ) : log b 1 = 0 :=
if h : b ≤ 1 then
  log_of_left_le_one h
else
  log_of_lt (not_le.mp h)

/-- `pow b` and `log b` (almost) form a Galois connection. -/
lemma pow_le_iff_le_log {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : 0 < y) :
  b^x ≤ y ↔ x ≤ log b y :=
begin
  induction y using nat.strong_induction_on with y ih generalizing x,
  cases x,
  { exact iff_of_true hy (zero_le _) },
  rw log, split_ifs,
  { have b_pos : 0 < b := zero_le_one.trans_lt hb,
    rw [succ_eq_add_one, add_le_add_iff_right, ←ih (y / b) (div_lt_self hy hb)
      (nat.div_pos h.1 b_pos), le_div_iff_mul_le _ _ b_pos, pow_succ'] },
  { refine iff_of_false (λ hby, h ⟨le_trans _ hby, hb⟩) (not_succ_le_zero _),
    convert pow_mono hb.le (zero_lt_succ x),
    exact (pow_one b).symm }
end

lemma log_pow {b : ℕ} (hb : 1 < b) (x : ℕ) : log b (b ^ x) = x :=
eq_of_forall_le_iff $ λ z,
by { rw ←pow_le_iff_le_log hb (pow_pos (zero_lt_one.trans hb) _),
    exact (pow_right_strict_mono hb).le_iff_le }

lemma log_pos {b n : ℕ} (hb : 1 < b) (hn : b ≤ n) : 0 < log b n :=
by { rwa [←succ_le_iff, ←pow_le_iff_le_log hb (hb.le.trans hn), pow_one] }

lemma log_mul_base (b n : ℕ) (hb : 1 < b) (hn : 0 < n) : log b (n * b) = log b n + 1 :=
eq_of_forall_le_iff $ λ z,
begin
  cases z,
  { simp },
  have : 0 < b := zero_lt_one.trans hb,
  rw [←pow_le_iff_le_log hb, pow_succ', (strict_mono_mul_right_of_pos this).le_iff_le,
      pow_le_iff_le_log hb hn, nat.succ_le_succ_iff],
  simp [hn, this]
end

lemma lt_pow_succ_log_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 0 < x) :
  x < b ^ (log b x).succ :=
begin
  rw [←not_le, pow_le_iff_le_log hb hx, not_le],
  exact lt_succ_self _,
end

lemma pow_log_le_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 0 < x) : b ^ log b x ≤ x :=
(pow_le_iff_le_log hb hx).2 le_rfl

lemma log_le_log_of_le {b n m : ℕ} (h : n ≤ m) : log b n ≤ log b m :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw log_of_left_le_one hb, exact zero_le _ },
  { cases nat.eq_zero_or_pos n with hn hn,
    { rw [hn, log_zero_right], exact zero_le _ },
    { rw ←pow_le_iff_le_log hb (hn.trans_le h),
      exact (pow_log_le_self hb hn).trans h } }
end

lemma log_le_log_of_left_ge {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : log b n ≤ log c n :=
begin
  cases n, { simp },
  rw ← pow_le_iff_le_log hc (zero_lt_succ n),
  calc
    c ^ log b n.succ ≤ b ^ log b n.succ : pow_le_pow_of_le_left
                                            (le_of_lt $ zero_lt_one.trans hc) hb _
                 ... ≤ n.succ           : pow_log_le_self (lt_of_lt_of_le hc hb)
                                            (zero_lt_succ n)
end

lemma log_monotone {b : ℕ} : monotone (λ n : ℕ, log b n) :=
λ x y, log_le_log_of_le

lemma log_antitone_left {n : ℕ} : antitone_on (λ b, log b n) (set.Ioi 1) :=
λ _ hc _ _ hb, log_le_log_of_left_ge (set.mem_Iio.1 hc) hb

@[simp] lemma log_div_mul_self (b n : ℕ) : log b (n / b * b) = log b n :=
begin
  refine eq_of_forall_le_iff (λ z, _),
  split,
  { intro h,
    exact h.trans (log_monotone (div_mul_le_self _ _)) },
  { intro h,
    rcases b with _|_|b,
    { simpa using h },
    { simpa using h },
    rcases n.zero_le.eq_or_lt with rfl|hn,
    { simpa using h },
    cases le_or_lt b.succ.succ n with hb hb,
    { cases z,
      { simp },
      have : 0 < b.succ.succ := nat.succ_pos',
      rw [←pow_le_iff_le_log, pow_succ'] at h ⊢,
      { rwa [(strict_mono_mul_right_of_pos this).le_iff_le,
             nat.le_div_iff_mul_le _ _ nat.succ_pos'] },
      all_goals { simp [hn, nat.div_pos hb nat.succ_pos'] } },
    { simpa [div_eq_of_lt, hb, log_eq_zero] using h } }
end

@[simp] lemma log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 :=
begin
  cases lt_or_le n b with h h,
  { simp [div_eq_of_lt, h, log_eq_zero] },
  rcases n.zero_le.eq_or_lt with rfl|hn,
  { simp },
  rcases b with _|_|b,
  { simp },
  { simp },
  rw [←succ_inj', ←succ_inj'],
  simp_rw succ_eq_add_one,
  rw [nat.sub_add_cancel, ←log_mul_base];
  { simp [succ_le_iff, log_pos, h, nat.div_pos] },
end


private lemma add_pred_div_lt {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : (n + b - 1)/b < n :=
begin
  rw [div_lt_iff_lt_mul _ _ (zero_lt_one.trans hb), ←succ_le_iff, ←pred_eq_sub_one,
    succ_pred_eq_of_pos (add_pos (zero_lt_one.trans hn) (zero_lt_one.trans hb))],
  exact add_le_mul hn hb,
end

/-! ### Ceil logarithm -/

/-- `clog b n`, is the upper logarithm of natural number `n` in base `b`. It returns the smallest
`k : ℕ` such that `n ≤ b^k`, so if `b^k = n`, it returns exactly `k`. -/
@[pp_nodot] def clog (b : ℕ) : ℕ → ℕ
| n :=
  if h : 1 < b ∧ 1 < n then
    have (n + b - 1)/b < n := add_pred_div_lt h.1 h.2,
    clog ((n + b - 1)/b) + 1
  else 0

lemma clog_of_left_le_one {b : ℕ} (hb : b ≤ 1) (n : ℕ) : clog b n = 0 :=
by rw [clog, if_neg (λ h : 1 < b ∧ 1 < n, h.1.not_le hb)]

lemma clog_of_right_le_one {n : ℕ} (hn : n ≤ 1) (b : ℕ) : clog b n = 0 :=
by rw [clog, if_neg (λ h : 1 < b ∧ 1 < n, h.2.not_le hn)]

@[simp] lemma clog_zero_left (n : ℕ) : clog 0 n = 0 :=
clog_of_left_le_one zero_le_one _

@[simp] lemma clog_zero_right (b : ℕ) : clog b 0 = 0 :=
clog_of_right_le_one zero_le_one _

@[simp] lemma clog_one_left (n : ℕ) : clog 1 n = 0 :=
clog_of_left_le_one le_rfl _

@[simp] lemma clog_one_right (b : ℕ) : clog b 1 = 0 :=
clog_of_right_le_one le_rfl _

lemma clog_of_two_le {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) :
  clog b n = clog b ((n + b - 1)/b) + 1 :=
by rw [clog, if_pos (⟨hb, hn⟩ : 1 < b ∧ 1 < n)]

lemma clog_pos {b n : ℕ} (hb : 1 < b) (hn : 2 ≤ n) : 0 < clog b n :=
by { rw clog_of_two_le hb hn, exact zero_lt_succ _ }

lemma clog_eq_one {b n : ℕ} (hn : 2 ≤ n) (h : n ≤ b) : clog b n = 1 :=
begin
  rw [clog_of_two_le (hn.trans h) hn, clog_of_right_le_one],
  have n_pos : 0 < n := zero_lt_two.trans_le hn,
  rw [←lt_succ_iff, nat.div_lt_iff_lt_mul _ _ (n_pos.trans_le h), ←succ_le_iff,
    ←pred_eq_sub_one, succ_pred_eq_of_pos (add_pos n_pos (n_pos.trans_le h)), succ_mul, one_mul],
  exact add_le_add_right h _,
end

/--`clog b` and `pow b` form a Galois connection. -/
lemma le_pow_iff_clog_le {b : ℕ} (hb : 1 < b) {x y : ℕ} :
  x ≤ b^y ↔ clog b x ≤ y :=
begin
  induction x using nat.strong_induction_on with x ih generalizing y,
  cases y,
  { rw [pow_zero],
    refine ⟨λ h, (clog_of_right_le_one h b).le, _⟩,
    simp_rw ←not_lt,
    contrapose!,
    exact clog_pos hb },
  have b_pos : 0 < b := zero_lt_two.trans_le hb,
  rw clog, split_ifs,
  { rw [succ_eq_add_one, add_le_add_iff_right, ←ih ((x + b - 1)/b) (add_pred_div_lt hb h.2),
      nat.div_le_iff_le_mul_add_pred b_pos,
      ← pow_succ, add_tsub_assoc_of_le (nat.succ_le_of_lt b_pos), add_le_add_iff_right] },
  { exact iff_of_true ((not_lt.1 (not_and.1 h hb)).trans $ succ_le_of_lt $ pow_pos b_pos _)
    (zero_le _) }
end

lemma clog_pow (b x : ℕ) (hb : 1 < b) : clog b (b ^ x) = x :=
eq_of_forall_ge_iff $ λ z,
by { rw ←le_pow_iff_clog_le hb, exact (pow_right_strict_mono hb).le_iff_le }

lemma pow_pred_clog_lt_self {b : ℕ} (hb : 1 < b) {x : ℕ} (hx : 1 < x) :
  b ^ (clog b x).pred < x :=
begin
  rw [←not_le, le_pow_iff_clog_le hb, not_le],
  exact pred_lt (clog_pos hb hx).ne',
end

lemma le_pow_clog {b : ℕ} (hb : 1 < b) (x : ℕ) : x ≤ b ^ clog b x :=
(le_pow_iff_clog_le hb).2 le_rfl

lemma clog_le_clog_of_le (b : ℕ) {n m : ℕ} (h : n ≤ m) : clog b n ≤ clog b m :=
begin
  cases le_or_lt b 1 with hb hb,
  { rw clog_of_left_le_one hb, exact zero_le _ },
  { rw ←le_pow_iff_clog_le hb,
    exact h.trans (le_pow_clog hb _) }
end

lemma clog_le_clog_of_left_ge {b c n : ℕ} (hc : 1 < c) (hb : c ≤ b) : clog b n ≤ clog c n :=
begin
  cases n, { simp },
  rw ← le_pow_iff_clog_le (lt_of_lt_of_le hc hb),
  calc
    n.succ ≤ c ^ clog c n.succ : le_pow_clog hc _
       ... ≤ b ^ clog c n.succ : pow_le_pow_of_le_left (le_of_lt $ zero_lt_one.trans hc) hb _
end

lemma clog_monotone (b : ℕ) : monotone (clog b) :=
λ x y, clog_le_clog_of_le _

lemma clog_antitone_left {n : ℕ} : antitone_on (λ b : ℕ, clog b n) (set.Ioi 1) :=
λ _ hc _ _ hb, clog_le_clog_of_left_ge (set.mem_Iio.1 hc) hb

lemma log_le_clog (b n : ℕ) : log b n ≤ clog b n :=
begin
  obtain hb | hb := le_or_lt b 1,
  { rw log_of_left_le_one hb,
    exact zero_le _},
  cases n,
  { rw log_zero_right,
    exact zero_le _},
  exact (pow_right_strict_mono hb).le_iff_le.1 ((pow_log_le_self hb $ succ_pos _).trans $
    le_pow_clog hb _),
end

end nat
