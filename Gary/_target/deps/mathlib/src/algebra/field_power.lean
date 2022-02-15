/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import algebra.group_with_zero.power
import tactic.linarith
import data.equiv.ring

/-!
# Integer power operation on fields and division rings

This file collects basic facts about the operation of raising an element of a `division_ring` to an
integer power. More specialised results are provided in the case of a linearly ordered field.
-/

universe u

@[simp] lemma ring_hom.map_zpow {K L : Type*} [division_ring K] [division_ring L] (f : K →+* L) :
  ∀ (a : K) (n : ℤ), f (a ^ n) = f a ^ n :=
f.to_monoid_with_zero_hom.map_zpow

@[simp] lemma ring_equiv.map_zpow {K L : Type*} [division_ring K] [division_ring L] (f : K ≃+* L) :
  ∀ (a : K) (n : ℤ), f (a ^ n) = f a ^ n :=
f.to_ring_hom.map_zpow

@[simp] lemma zpow_bit0_neg {K : Type*} [division_ring K] (x : K) (n : ℤ) :
  (-x) ^ (bit0 n) = x ^ bit0 n :=
by rw [zpow_bit0', zpow_bit0', neg_mul_neg]

lemma even.zpow_neg {K : Type*} [division_ring K] {n : ℤ} (h : even n) (a : K) :
  (-a) ^ n = a ^ n :=
begin
  obtain ⟨k, rfl⟩ := h,
  rw [←bit0_eq_two_mul, zpow_bit0_neg],
end

@[simp] lemma zpow_bit1_neg {K : Type*} [division_ring K] (x : K) (n : ℤ) :
  (-x) ^ (bit1 n) = - x ^ bit1 n :=
by rw [zpow_bit1', zpow_bit1', neg_mul_neg, neg_mul_eq_mul_neg]

section ordered_field_power
open int

variables {K : Type u} [linear_ordered_field K] {a : K} {n : ℤ}

lemma zpow_eq_zero_iff (hn : 0 < n) :
  a ^ n = 0 ↔ a = 0 :=
begin
  refine ⟨zpow_eq_zero, _⟩,
  rintros rfl,
  exact zero_zpow _ hn.ne'
end

lemma zpow_nonneg {a : K} (ha : 0 ≤ a) : ∀ (z : ℤ), 0 ≤ a ^ z
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_nonneg ha _ }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_nonneg.2 (pow_nonneg ha _) }

lemma zpow_pos_of_pos {a : K} (ha : 0 < a) : ∀ (z : ℤ), 0 < a ^ z
| (n : ℕ) := by { rw zpow_coe_nat, exact pow_pos ha _ }
| -[1+n]  := by { rw zpow_neg_succ_of_nat, exact inv_pos.2 (pow_pos ha _) }

lemma zpow_le_of_le {x : K} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
begin
  induction a with a a; induction b with b b,
  { simp only [of_nat_eq_coe, zpow_coe_nat],
    apply pow_le_pow hx,
    apply le_of_coe_nat_le_coe_nat h },
  { apply absurd h,
    apply not_le_of_gt,
    exact lt_of_lt_of_le (neg_succ_lt_zero _) (of_nat_nonneg _) },
  { simp only [zpow_neg_succ_of_nat, one_div, of_nat_eq_coe, zpow_coe_nat],
    apply le_trans (inv_le_one _); apply one_le_pow_of_one_le hx },
  { simp only [zpow_neg_succ_of_nat],
    apply (inv_le_inv _ _).2,
    { apply pow_le_pow hx,
      have : -(↑(a+1) : ℤ) ≤ -(↑(b+1) : ℤ), from h,
      have h' := le_of_neg_le_neg this,
      apply le_of_coe_nat_le_coe_nat h' },
    repeat { apply pow_pos (lt_of_lt_of_le zero_lt_one hx) } }
end

lemma pow_le_max_of_min_le {x : K} (hx : 1 ≤ x) {a b c : ℤ} (h : min a b ≤ c) :
      x ^ (-c) ≤ max (x ^ (-a)) (x ^ (-b)) :=
begin
  wlog hle : a ≤ b,
  have hnle : -b ≤ -a, from neg_le_neg hle,
  have hfle : x ^ (-b) ≤ x ^ (-a), from zpow_le_of_le hx hnle,
  have : x ^ (-c) ≤ x ^ (-a),
  { apply zpow_le_of_le hx,
    simpa only [min_eq_left hle, neg_le_neg_iff] using h },
  simpa only [max_eq_left hfle]
end

lemma zpow_le_one_of_nonpos {p : K} (hp : 1 ≤ p) {z : ℤ} (hz : z ≤ 0) : p ^ z ≤ 1 :=
calc p ^ z ≤ p ^ 0 : zpow_le_of_le hp hz
          ... = 1        : by simp

lemma one_le_zpow_of_nonneg {p : K} (hp : 1 ≤ p) {z : ℤ} (hz : 0 ≤ z) : 1 ≤ p ^ z :=
calc p ^ z ≥ p ^ 0 : zpow_le_of_le hp hz
          ... = 1        : by simp

theorem zpow_bit0_nonneg (a : K) (n : ℤ) : 0 ≤ a ^ bit0 n :=
by { rw zpow_bit0₀, exact mul_self_nonneg _ }

theorem zpow_two_nonneg (a : K) : 0 ≤ a ^ 2 :=
pow_bit0_nonneg a 1

theorem zpow_bit0_pos {a : K} (h : a ≠ 0) (n : ℤ) : 0 < a ^ bit0 n :=
(zpow_bit0_nonneg a n).lt_of_ne (zpow_ne_zero _ h).symm

theorem zpow_two_pos_of_ne_zero (a : K) (h : a ≠ 0) : 0 < a ^ 2 :=
pow_bit0_pos h 1

@[simp] theorem zpow_bit1_neg_iff : a ^ bit1 n < 0 ↔ a < 0 :=
⟨λ h, not_le.1 $ λ h', not_le.2 h $ zpow_nonneg h' _,
 λ h, by rw [bit1, zpow_add_one₀ h.ne]; exact mul_neg_of_pos_of_neg (zpow_bit0_pos h.ne _) h⟩

@[simp] theorem zpow_bit1_nonneg_iff : 0 ≤ a ^ bit1 n ↔ 0 ≤ a :=
le_iff_le_iff_lt_iff_lt.2 zpow_bit1_neg_iff

@[simp] theorem zpow_bit1_nonpos_iff : a ^ bit1 n ≤ 0 ↔ a ≤ 0 :=
begin
  rw [le_iff_lt_or_eq, zpow_bit1_neg_iff],
  split,
  { rintro (h | h),
    { exact h.le },
    { exact (zpow_eq_zero h).le } },
  { intro h,
    rcases eq_or_lt_of_le h with rfl|h,
    { exact or.inr (zero_zpow _ (bit1_ne_zero n)) },
    { exact or.inl h } }
end

@[simp] theorem zpow_bit1_pos_iff : 0 < a ^ bit1 n ↔ 0 < a :=
lt_iff_lt_of_le_iff_le zpow_bit1_nonpos_iff

lemma even.zpow_nonneg {n : ℤ} (hn : even n) (a : K) :
  0 ≤ a ^ n :=
begin
  cases le_or_lt 0 a with h h,
  { exact zpow_nonneg h _ },
  { exact (hn.zpow_neg a).subst (zpow_nonneg (neg_nonneg_of_nonpos h.le) _) }
end

theorem even.zpow_pos (hn : even n) (ha : a ≠ 0) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit0_pos ha k

theorem odd.zpow_nonneg (hn : odd n) (ha : 0 ≤ a) : 0 ≤ a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_nonneg_iff.mpr ha

theorem odd.zpow_pos (hn : odd n) (ha : 0 < a) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_pos_iff.mpr ha

theorem odd.zpow_nonpos (hn : odd n) (ha : a ≤ 0) : a ^ n ≤ 0:=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_nonpos_iff.mpr ha

theorem odd.zpow_neg (hn : odd n) (ha : a < 0) : a ^ n < 0:=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_neg_iff.mpr ha

lemma even.zpow_abs {p : ℤ} (hp : even p) (a : K) : |a| ^ p = a ^ p :=
begin
  cases abs_choice a with h h;
  simp only [h, hp.zpow_neg _],
end

@[simp] lemma zpow_bit0_abs (a : K) (p : ℤ) : |a| ^ bit0 p = a ^ bit0 p :=
(even_bit0 _).zpow_abs _

lemma even.abs_zpow {p : ℤ} (hp : even p) (a : K) : |a ^ p| = a ^ p :=
begin
  rw [abs_eq_self],
  exact hp.zpow_nonneg _
end

@[simp] lemma abs_zpow_bit0 (a : K) (p : ℤ) :
  |a ^ bit0 p| = a ^ bit0 p :=
(even_bit0 _).abs_zpow _

end ordered_field_power

lemma one_lt_zpow {K} [linear_ordered_field K] {p : K} (hp : 1 < p) :
  ∀ z : ℤ, 0 < z → 1 < p ^ z
| (n : ℕ) h := (zpow_coe_nat p n).symm.subst (one_lt_pow hp $ int.coe_nat_ne_zero.mp h.ne')
| -[1+ n] h := ((int.neg_succ_not_pos _).mp h).elim

section ordered
variables  {K : Type*} [linear_ordered_field K]

lemma nat.zpow_pos_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : 0 < (p:K)^n :=
by { apply zpow_pos_of_pos, exact_mod_cast h }

lemma nat.zpow_ne_zero_of_pos {p : ℕ} (h : 0 < p) (n:ℤ) : (p:K)^n ≠ 0 :=
ne_of_gt (nat.zpow_pos_of_pos h n)

lemma zpow_strict_mono {x : K} (hx : 1 < x) :
  strict_mono (λ n:ℤ, x ^ n) :=
strict_mono_int_of_lt_succ $ λ n,
have xpos : 0 < x, from zero_lt_one.trans hx,
calc x ^ n < x ^ n * x : lt_mul_of_one_lt_right (zpow_pos_of_pos xpos _) hx
... = x ^ (n + 1) : (zpow_add_one₀ xpos.ne' _).symm

lemma zpow_strict_anti {x : K} (h₀ : 0 < x) (h₁ : x < 1) : strict_anti (λ n : ℤ, x ^ n) :=
strict_anti_int_of_succ_lt $ λ n,
calc x ^ (n + 1) = x ^ n * x : zpow_add_one₀ h₀.ne' _
... < x ^ n * 1 : (mul_lt_mul_left $ zpow_pos_of_pos h₀ _).2 h₁
... = x ^ n : mul_one _

@[simp] lemma zpow_lt_iff_lt {x : K} (hx : 1 < x) {m n : ℤ} :
  x ^ m < x ^ n ↔ m < n :=
(zpow_strict_mono hx).lt_iff_lt

@[simp] lemma zpow_le_iff_le {x : K} (hx : 1 < x) {m n : ℤ} :
  x ^ m ≤ x ^ n ↔ m ≤ n :=
(zpow_strict_mono hx).le_iff_le

@[simp] lemma pos_div_pow_pos {a b : K} (ha : 0 < a) (hb : 0 < b) (k : ℕ) : 0 < a/b^k :=
div_pos ha (pow_pos hb k)

@[simp] lemma div_pow_le {a b : K} (ha : 0 < a) (hb : 1 ≤ b) (k : ℕ) : a/b^k ≤ a :=
(div_le_iff $ pow_pos (lt_of_lt_of_le zero_lt_one hb) k).mpr
(calc a = a * 1 : (mul_one a).symm
   ...  ≤ a*b^k : (mul_le_mul_left ha).mpr $ one_le_pow_of_one_le hb _)

lemma zpow_injective {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) :
  function.injective ((^) x : ℤ → K) :=
begin
  intros m n h,
  rcases h₁.lt_or_lt with H|H,
  { apply (zpow_strict_mono (one_lt_inv h₀ H)).injective,
    show x⁻¹ ^ m = x⁻¹ ^ n,
    rw [← zpow_neg_one, ← zpow_mul₀, ← zpow_mul₀, mul_comm _ m, mul_comm _ n, zpow_mul₀, zpow_mul₀,
      h], },
  { exact (zpow_strict_mono H).injective h, },
end

@[simp] lemma zpow_inj {x : K} (h₀ : 0 < x) (h₁ : x ≠ 1) {m n : ℤ} :
  x ^ m = x ^ n ↔ m = n :=
(zpow_injective h₀ h₁).eq_iff

end ordered

section
variables {K : Type*} [field K]

@[simp, norm_cast] theorem rat.cast_zpow [char_zero K] (q : ℚ) (n : ℤ) :
  ((q ^ n : ℚ) : K) = q ^ n :=
(rat.cast_hom K).map_zpow q n

end
