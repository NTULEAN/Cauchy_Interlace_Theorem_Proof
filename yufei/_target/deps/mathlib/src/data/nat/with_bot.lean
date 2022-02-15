/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.basic
import algebra.order.group
/-!
# `with_bot ℕ`

Lemmas about the type of natural numbers with a bottom element adjoined.
-/
namespace nat

lemma with_bot.add_eq_zero_iff : ∀ {n m : with_bot ℕ}, n + m = 0 ↔ n = 0 ∧ m = 0
| none     m        := iff_of_false dec_trivial (λ h, absurd h.1 dec_trivial)
| n        none     := iff_of_false (by cases n; exact dec_trivial)
  (λ h, absurd h.2 dec_trivial)
| (some n) (some m) := show (n + m : with_bot ℕ) = (0 : ℕ) ↔ (n : with_bot ℕ) = (0 : ℕ) ∧
    (m : with_bot ℕ) = (0 : ℕ),
  by rw [← with_bot.coe_add, with_bot.coe_eq_coe, with_bot.coe_eq_coe,
    with_bot.coe_eq_coe, add_eq_zero_iff' (nat.zero_le _) (nat.zero_le _)]

lemma with_bot.add_eq_one_iff : ∀ {n m : with_bot ℕ}, n + m = 1 ↔ (n = 0 ∧ m = 1) ∨ (n = 1 ∧ m = 0)
| none     none     := dec_trivial
| none     (some m) := dec_trivial
| (some n) none     := iff_of_false dec_trivial (λ h, h.elim (λ h, absurd h.2 dec_trivial)
  (λ h, absurd h.2 dec_trivial))
| (some n) (some 0) := by erw [with_bot.coe_eq_coe, with_bot.coe_eq_coe, with_bot.coe_eq_coe,
    with_bot.coe_eq_coe]; simp
| (some n) (some (m + 1)) := by erw [with_bot.coe_eq_coe, with_bot.coe_eq_coe, with_bot.coe_eq_coe,
    with_bot.coe_eq_coe, with_bot.coe_eq_coe]; simp [nat.add_succ, nat.succ_inj', nat.succ_ne_zero]

@[simp] lemma with_bot.coe_nonneg {n : ℕ} : 0 ≤ (n : with_bot ℕ) :=
by rw [← with_bot.coe_zero, with_bot.coe_le_coe]; exact nat.zero_le _

@[simp] lemma with_bot.lt_zero_iff (n : with_bot ℕ) : n < 0 ↔ n = ⊥ :=
option.cases_on n dec_trivial (λ n, iff_of_false
  (by simp [with_bot.some_eq_coe]) (λ h, option.no_confusion h))

lemma with_bot.one_le_iff_zero_lt {x : with_bot ℕ} : 1 ≤ x ↔ 0 < x :=
begin
  refine ⟨λ h, lt_of_lt_of_le (with_bot.coe_lt_coe.mpr zero_lt_one) h, λ h, _⟩,
  induction x using with_bot.rec_bot_coe,
  { exact (not_lt_bot h).elim },
  { exact with_bot.coe_le_coe.mpr (nat.succ_le_iff.mpr (with_bot.coe_lt_coe.mp h)) }
end

lemma with_bot.lt_one_iff_le_zero {x : with_bot ℕ} : x < 1 ↔ x ≤ 0 :=
not_iff_not.mp (by simpa using with_bot.one_le_iff_zero_lt)

end nat
