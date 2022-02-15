/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.gcd
import data.list.rotate
import tactic.abel

/-!
# Congruences modulo a natural number

This file defines the equivalence relation `a ≡ b [MOD n]` on the natural numbers,
and proves basic properties about it such as the Chinese Remainder Theorem
`modeq_and_modeq_iff_modeq_mul`.

## Notations

`a ≡ b [MOD n]` is notation for `nat.modeq n a b`, which is defined to mean `a % n = b % n`.

## Tags

modeq, congruence, mod, MOD, modulo
-/

namespace nat

/-- Modular equality. `n.modeq a b`, or `a ≡ b [MOD n]`, means that `a - b` is a multiple of `n`. -/
@[derive decidable]
def modeq (n a b : ℕ) := a % n = b % n

notation a ` ≡ `:50 b ` [MOD `:50 n `]`:0 := modeq n a b

variables {m n a b c d : ℕ}

namespace modeq

@[refl] protected theorem refl (a : ℕ) : a ≡ a [MOD n] := @rfl _ _

protected theorem rfl : a ≡ a [MOD n] := modeq.refl _

@[symm] protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] := eq.symm

@[trans] protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] := eq.trans

protected theorem comm : a ≡ b [MOD n] ↔ b ≡ a [MOD n] := ⟨modeq.symm, modeq.symm⟩

end modeq

theorem modeq_zero_iff_dvd : a ≡ 0 [MOD n] ↔ n ∣ a :=
by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

lemma _root_.has_dvd.dvd.modeq_zero_nat (h : n ∣ a) : a ≡ 0 [MOD n] := modeq_zero_iff_dvd.2 h
lemma _root_.has_dvd.dvd.zero_modeq_nat (h : n ∣ a) : 0 ≡ a [MOD n] := h.modeq_zero_nat.symm

theorem modeq_iff_dvd : a ≡ b [MOD n] ↔ (n:ℤ) ∣ b - a :=
by rw [modeq, eq_comm, ← int.coe_nat_inj', int.coe_nat_mod, int.coe_nat_mod,
   int.mod_eq_mod_iff_mod_sub_eq_zero, int.dvd_iff_mod_eq_zero]

protected theorem modeq.dvd : a ≡ b [MOD n] → (n:ℤ) ∣ b - a := modeq_iff_dvd.1
theorem modeq_of_dvd : (n:ℤ) ∣ b - a → a ≡ b [MOD n] := modeq_iff_dvd.2

/-- A variant of `modeq_iff_dvd` with `nat` divisibility -/
theorem modeq_iff_dvd' (h : a ≤ b) : a ≡ b [MOD n] ↔ n ∣ b - a :=
by rw [modeq_iff_dvd, ←int.coe_nat_dvd, int.coe_nat_sub h]

theorem mod_modeq (a n) : a % n ≡ a [MOD n] := mod_mod _ _

namespace modeq

protected theorem modeq_of_dvd (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
modeq_of_dvd ((int.coe_nat_dvd.2 d).trans h.dvd)

protected theorem mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD (c * n)] :=
by unfold modeq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]

protected theorem mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
(h.mul_left' _ ).modeq_of_dvd (dvd_mul_left _ _)

protected theorem mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD (n * c)] :=
by rw [mul_comm a, mul_comm b, mul_comm n]; exact h.mul_left' c

protected theorem mul_right (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] :=
by rw [mul_comm a, mul_comm b]; exact h.mul_left c

protected theorem mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
(h₂.mul_left _ ).trans (h₁.mul_right _)

protected theorem pow (m : ℕ) (h : a ≡ b [MOD n]) : a ^ m ≡ b ^ m [MOD n] :=
begin
  induction m with d hd, {refl},
  rw [pow_succ, pow_succ],
  exact h.mul hd,
end

protected theorem add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] :=
begin
  rw [modeq_iff_dvd, int.coe_nat_add, int.coe_nat_add, add_sub_comm],
  exact dvd_add h₁.dvd h₂.dvd,
end

protected theorem add_left (c : ℕ) (h : a ≡ b [MOD n]) : c + a ≡ c + b [MOD n] :=
modeq.rfl.add h

protected theorem add_right (c : ℕ) (h : a ≡ b [MOD n]) : a + c ≡ b + c [MOD n] :=
h.add modeq.rfl

protected theorem add_left_cancel (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
  c ≡ d [MOD n] :=
begin
  simp only [modeq_iff_dvd, int.coe_nat_add] at *,
  rw add_sub_comm at h₂,
  convert _root_.dvd_sub h₂ h₁ using 1,
  rw add_sub_cancel',
end

protected theorem add_left_cancel' (c : ℕ) (h : c + a ≡ c + b [MOD n]) : a ≡ b [MOD n] :=
modeq.rfl.add_left_cancel h

protected theorem add_right_cancel (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) :
  a ≡ b [MOD n] :=
by { rw [add_comm a, add_comm b] at h₂, exact h₁.add_left_cancel h₂ }

protected theorem add_right_cancel' (c : ℕ) (h : a + c ≡ b + c [MOD n]) : a ≡ b [MOD n] :=
modeq.rfl.add_right_cancel h

theorem of_modeq_mul_left (m : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] :=
by { rw [modeq_iff_dvd] at *, exact (dvd_mul_left (n : ℤ) (m : ℤ)).trans h }

theorem of_modeq_mul_right (m : ℕ) : a ≡ b [MOD n * m] → a ≡ b [MOD n] :=
mul_comm m n ▸ of_modeq_mul_left _

end modeq

theorem modeq_one : a ≡ b [MOD 1] := modeq_of_dvd (one_dvd _)

lemma modeq_sub (h : b ≤ a) : a ≡ b [MOD a - b] :=
(modeq_of_dvd $ by rw [int.coe_nat_sub h]).symm

@[simp] lemma modeq_zero_iff {a b : ℕ} : a ≡ b [MOD 0] ↔ a = b :=
by rw [nat.modeq, nat.mod_zero, nat.mod_zero]

@[simp] lemma add_modeq_left {a n : ℕ} : n + a ≡ a [MOD n] :=
by rw [nat.modeq, nat.add_mod_left]
@[simp] lemma add_modeq_right {a n : ℕ} : a + n ≡ a [MOD n] :=
by rw [nat.modeq, nat.add_mod_right]

namespace modeq

lemma le_of_lt_add (h1 : a ≡ b [MOD m]) (h2 : a < b + m) : a ≤ b :=
(le_total a b).elim id (λ h3, nat.le_of_sub_eq_zero
  (eq_zero_of_dvd_of_lt ((modeq_iff_dvd' h3).mp h1.symm) ((tsub_lt_iff_left h3).mpr h2)))

lemma add_le_of_lt (h1 : a ≡ b [MOD m]) (h2 : a < b) : a + m ≤ b :=
le_of_lt_add (add_modeq_right.trans h1) (add_lt_add_right h2 m)

end modeq

local attribute [semireducible] int.nonneg

/-- The natural number less than `lcm n m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder' (h : a ≡ b [MOD gcd n m]) : {k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]} :=
if hn : n = 0 then ⟨a, begin rw [hn, gcd_zero_left] at h, split, refl, exact h end⟩ else
if hm : m = 0 then ⟨b, begin rw [hm, gcd_zero_right] at h, split, exact h.symm, refl end⟩ else
⟨let (c, d) := xgcd n m in int.to_nat (((n * c * b + m * d * a) / gcd n m) % lcm n m), begin
  rw xgcd_val,
  dsimp [chinese_remainder'._match_1],
  rw [modeq_iff_dvd, modeq_iff_dvd,
    int.to_nat_of_nonneg (int.mod_nonneg _ (int.coe_nat_ne_zero.2 (lcm_ne_zero hn hm)))],
  have hnonzero : (gcd n m : ℤ) ≠ 0 := begin
    norm_cast,
    rw [nat.gcd_eq_zero_iff, not_and],
    exact λ _, hm,
  end,
  have hcoedvd : ∀ t, (gcd n m : ℤ) ∣ t * (b - a) := λ t, h.dvd.mul_left _,
  have := gcd_eq_gcd_ab n m,
  split; rw [int.mod_def, ← sub_add]; refine dvd_add _ (dvd_mul_of_dvd_left _ _); try {norm_cast},
  { rw ← sub_eq_iff_eq_add' at this,
    rw [← this, sub_mul, ← add_sub_assoc, add_comm, add_sub_assoc, ← mul_sub,
      int.add_div_of_dvd_left, int.mul_div_cancel_left _ hnonzero,
      int.mul_div_assoc _ h.dvd, ← sub_sub, sub_self, zero_sub, dvd_neg, mul_assoc],
    exact dvd_mul_right _ _,
    norm_cast, exact dvd_mul_right _ _, },
  { exact dvd_lcm_left n m, },
  { rw ← sub_eq_iff_eq_add at this,
    rw [← this, sub_mul, sub_add, ← mul_sub, int.sub_div_of_dvd, int.mul_div_cancel_left _ hnonzero,
      int.mul_div_assoc _ h.dvd, ← sub_add, sub_self, zero_add, mul_assoc],
    exact dvd_mul_right _ _,
    exact hcoedvd _ },
  { exact dvd_lcm_right n m, },
end⟩

/-- The natural number less than `n*m` congruent to `a` mod `n` and `b` mod `m` -/
def chinese_remainder (co : coprime n m) (a b : ℕ) : {k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]} :=
chinese_remainder' (by convert modeq_one)

lemma chinese_remainder'_lt_lcm (h : a ≡ b [MOD gcd n m]) (hn : n ≠ 0) (hm : m ≠ 0) :
  ↑(chinese_remainder' h) < lcm n m :=
begin
  dsimp only [chinese_remainder'],
  rw [dif_neg hn, dif_neg hm, subtype.coe_mk, xgcd_val, ←int.to_nat_coe_nat (lcm n m)],
  have lcm_pos := int.coe_nat_pos.mpr (nat.pos_of_ne_zero (lcm_ne_zero hn hm)),
  exact (int.to_nat_lt_to_nat lcm_pos).mpr (int.mod_lt_of_pos _ lcm_pos),
end

lemma chinese_remainder_lt_mul (co : coprime n m) (a b : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) :
  ↑(chinese_remainder co a b) < n * m :=
lt_of_lt_of_le (chinese_remainder'_lt_lcm _ hn hm) (le_of_eq co.lcm_eq_mul)

lemma modeq_and_modeq_iff_modeq_mul {a b m n : ℕ} (hmn : coprime m n) :
  a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ (a ≡ b [MOD m * n]) :=
⟨λ h, begin
    rw [nat.modeq_iff_dvd, nat.modeq_iff_dvd, ← int.dvd_nat_abs,
      int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd] at h,
    rw [nat.modeq_iff_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd],
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2
  end,
λ h, ⟨h.of_modeq_mul_right _, h.of_modeq_mul_left _⟩⟩

lemma coprime_of_mul_modeq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : coprime a n :=
nat.coprime_of_dvd' (λ k kp ⟨ka, hka⟩ ⟨kb, hkb⟩, int.coe_nat_dvd.1 begin
  rw [hka, hkb, modeq_iff_dvd] at h,
  cases h with z hz,
  rw [sub_eq_iff_eq_add] at hz,
  rw [hz, int.coe_nat_mul, mul_assoc, mul_assoc, int.coe_nat_mul, ← mul_add],
  exact dvd_mul_right _ _,
end)

@[simp] lemma mod_mul_right_mod (a b c : ℕ) : a % (b * c) % b = a % b :=
(mod_modeq _ _).of_modeq_mul_right _

@[simp] lemma mod_mul_left_mod (a b c : ℕ) : a % (b * c) % c = a % c :=
(mod_modeq _ _).of_modeq_mul_left _

lemma div_mod_eq_mod_mul_div (a b c : ℕ) : a / b % c = a % (b * c) / b :=
if hb0 : b = 0 then by simp [hb0]
else by rw [← @add_right_cancel_iff _ _ (c * (a / b / c)), mod_add_div, nat.div_div_eq_div_mul,
  ← nat.mul_right_inj (nat.pos_of_ne_zero hb0),← @add_left_cancel_iff _ _ (a % b), mod_add_div,
  mul_add, ← @add_left_cancel_iff _ _ (a % (b * c) % b), add_left_comm,
  ← add_assoc (a % (b * c) % b), mod_add_div, ← mul_assoc, mod_add_div, mod_mul_right_mod]

lemma add_mod_add_ite (a b c : ℕ) :
  (a + b) % c + (if c ≤ a % c + b % c then c else 0) = a % c + b % c :=
have (a + b) % c = (a % c + b % c) % c,
  from ((mod_modeq _ _).add $ mod_modeq _ _).symm,
if hc0 : c = 0 then by simp [hc0]
else
  begin
    rw this,
    split_ifs,
    { have h2 : (a % c + b % c) / c < 2,
        from nat.div_lt_of_lt_mul (by rw mul_two;
          exact add_lt_add (nat.mod_lt _ (nat.pos_of_ne_zero hc0))
            (nat.mod_lt _ (nat.pos_of_ne_zero hc0))),
      have h0 : 0 <  (a % c + b % c) / c, from nat.div_pos h (nat.pos_of_ne_zero hc0),
      rw [← @add_right_cancel_iff _ _ (c * ((a % c + b % c) / c)), add_comm _ c, add_assoc,
        mod_add_div, le_antisymm (le_of_lt_succ h2) h0, mul_one, add_comm] },
    { rw [nat.mod_eq_of_lt (lt_of_not_ge h), add_zero] }
  end

lemma add_mod_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
  (a + b) % c = a % c + b % c :=
 by rw [← add_mod_add_ite, if_neg (not_le_of_lt hc), add_zero]

lemma add_mod_add_of_le_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) :
  (a + b) % c + c = a % c + b % c :=
by rw [← add_mod_add_ite, if_pos hc]

lemma add_div {a b c : ℕ} (hc0 : 0 < c) : (a + b) / c = a / c + b / c +
  if c ≤ a % c + b % c then 1 else 0 :=
begin
  rw [← nat.mul_right_inj hc0, ← @add_left_cancel_iff _ _ ((a + b) % c + a % c + b % c)],
  suffices : (a + b) % c + c * ((a + b) / c) + a % c + b % c =
    a % c + c * (a / c) + (b % c + c * (b / c)) + c * (if c ≤ a % c + b % c then 1 else 0) +
      (a + b) % c,
  { simpa only [mul_add, add_comm, add_left_comm, add_assoc] },
  rw [mod_add_div, mod_add_div, mod_add_div, mul_ite, add_assoc, add_assoc],
  conv_lhs { rw ← add_mod_add_ite },
  simp, ac_refl
end

lemma add_div_eq_of_add_mod_lt {a b c : ℕ} (hc : a % c + b % c < c) :
  (a + b) / c = a / c + b / c :=
if hc0 : c = 0 then by simp [hc0]
else by rw [add_div (nat.pos_of_ne_zero hc0), if_neg (not_le_of_lt hc), add_zero]

protected lemma add_div_of_dvd_right {a b c : ℕ} (hca : c ∣ a) :
  (a + b) / c = a / c + b / c :=
if h : c = 0 then by simp [h] else add_div_eq_of_add_mod_lt begin
  rw [nat.mod_eq_zero_of_dvd hca, zero_add],
  exact nat.mod_lt _ (pos_iff_ne_zero.mpr h),
end

protected lemma add_div_of_dvd_left {a b c : ℕ} (hca : c ∣ b) :
  (a + b) / c = a / c + b / c :=
by rwa [add_comm, nat.add_div_of_dvd_right, add_comm]

lemma add_div_eq_of_le_mod_add_mod {a b c : ℕ} (hc : c ≤ a % c + b % c) (hc0 : 0 < c) :
  (a + b) / c = a / c + b / c + 1 :=
by rw [add_div hc0, if_pos hc]

lemma add_div_le_add_div (a b c : ℕ) : a / c + b / c ≤ (a + b) / c :=
if hc0 : c = 0 then by simp [hc0]
else by rw [nat.add_div (nat.pos_of_ne_zero hc0)]; exact nat.le_add_right _ _

lemma le_mod_add_mod_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬ c ∣ a) :
  c ≤ a % c + b % c :=
by_contradiction $ λ hc,
  have (a + b) % c = a % c + b % c, from add_mod_of_add_mod_lt (lt_of_not_ge hc),
  by simp [dvd_iff_mod_eq_zero, *] at *

lemma odd_mul_odd {n m : ℕ} : n % 2 = 1 → m % 2 = 1 → (n * m) % 2 = 1 :=
by simpa [nat.modeq] using @modeq.mul 2 n 1 m 1

lemma odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
  (m * n) / 2 = m * (n / 2) + m / 2 :=
have hm0 : 0 < m := nat.pos_of_ne_zero (λ h, by simp * at *),
have hn0 : 0 < n := nat.pos_of_ne_zero (λ h, by simp * at *),
(nat.mul_right_inj (show 0 < 2, from dec_trivial)).1 $
by rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
  two_mul_odd_div_two (nat.odd_mul_odd hm1 hn1), mul_tsub, mul_one,
  ← add_tsub_assoc_of_le (succ_le_of_lt hm0),
  tsub_add_cancel_of_le (le_mul_of_one_le_right (nat.zero_le _) hn0)]

lemma odd_of_mod_four_eq_one {n : ℕ} : n % 4 = 1 → n % 2 = 1 :=
by simpa [modeq, show 2 * 2 = 4, by norm_num] using @modeq.of_modeq_mul_left 2 n 1 2

lemma odd_of_mod_four_eq_three {n : ℕ} : n % 4 = 3 → n % 2 = 1 :=
by simpa [modeq, show 2 * 2 = 4, by norm_num, show 3 % 4 = 3, by norm_num]
  using @modeq.of_modeq_mul_left 2 n 3 2

end nat

namespace list
variable {α : Type*}

lemma nth_rotate : ∀ {l : list α} {n m : ℕ} (hml : m < l.length),
  (l.rotate n).nth m = l.nth ((m + n) % l.length)
| []     n     m hml := (nat.not_lt_zero _ hml).elim
| l      0     m hml := by simp [nat.mod_eq_of_lt hml]
| (a::l) (n+1) m hml :=
have h₃ : m < list.length (l ++ [a]), by simpa using hml,
(lt_or_eq_of_le (nat.le_of_lt_succ $ nat.mod_lt (m + n)
  (lt_of_le_of_lt (nat.zero_le _) hml))).elim
(λ hml',
  have h₁ : (m + (n + 1)) % ((a :: l : list α).length) =
      (m + n) % ((a :: l : list α).length) + 1,
    from calc (m + (n + 1)) % (l.length + 1) =
      ((m + n) % (l.length + 1) + 1) % (l.length + 1) :
        add_assoc m n 1 ▸ nat.modeq.add_right 1 (nat.mod_mod _ _).symm
    ... = (m + n) % (l.length + 1) + 1 : nat.mod_eq_of_lt (nat.succ_lt_succ hml'),
  have h₂ : (m + n) % (l ++ [a]).length < l.length, by simpa [nat.add_one] using hml',
  by rw [list.rotate_cons_succ, nth_rotate h₃, list.nth_append h₂, h₁, list.nth]; simp)
(λ hml',
  have h₁ : (m + (n + 1)) % (l.length + 1) = 0,
    from calc (m + (n + 1)) % (l.length + 1) = (l.length + 1) % (l.length + 1) :
      add_assoc m n 1 ▸ nat.modeq.add_right 1
        (hml'.trans (nat.mod_eq_of_lt (nat.lt_succ_self _)).symm)
    ... = 0 : by simp,
  by rw [list.length, list.rotate_cons_succ, nth_rotate h₃, list.length_append,
    list.length_cons, list.length, zero_add, hml', h₁, list.nth_concat_length]; refl)

lemma rotate_eq_self_iff_eq_repeat [hα : nonempty α] : ∀ {l : list α},
  (∀ n, l.rotate n = l) ↔ ∃ a, l = list.repeat a l.length
| []     := ⟨λ h, nonempty.elim hα (λ a, ⟨a, by simp⟩), by simp⟩
| (a::l) :=
⟨λ h, ⟨a, list.ext_le (by simp) $ λ n hn h₁,
  begin
    rw [← option.some_inj, ← list.nth_le_nth],
    conv {to_lhs, rw ← h ((list.length (a :: l)) - n)},
    rw [nth_rotate hn, add_tsub_cancel_of_le (le_of_lt hn),
      nat.mod_self, nth_le_repeat], refl
  end⟩,
  λ ⟨a, ha⟩ n, ha.symm ▸ list.ext_le (by simp)
    (λ m hm h,
      have hm' : (m + n) % (list.repeat a (list.length (a :: l))).length < list.length (a :: l),
        by rw list.length_repeat; exact nat.mod_lt _ (nat.succ_pos _),
      by rw [nth_le_repeat, ← option.some_inj, ← list.nth_le_nth, nth_rotate h, list.nth_le_nth,
        nth_le_repeat]; simp * at *)⟩

lemma rotate_repeat (a : α) (n : ℕ) (k : ℕ) :
  (list.repeat a n).rotate k = list.repeat a n :=
let h : nonempty α := ⟨a⟩ in by exactI rotate_eq_self_iff_eq_repeat.mpr ⟨a, by rw length_repeat⟩ k

lemma rotate_one_eq_self_iff_eq_repeat [nonempty α] {l : list α} :
  l.rotate 1 = l ↔ ∃ a : α, l = list.repeat a l.length :=
⟨λ h, rotate_eq_self_iff_eq_repeat.mp (λ n, nat.rec l.rotate_zero
  (λ n hn, by rwa [nat.succ_eq_add_one, ←l.rotate_rotate, hn]) n),
    λ h, rotate_eq_self_iff_eq_repeat.mpr h 1⟩

end list
