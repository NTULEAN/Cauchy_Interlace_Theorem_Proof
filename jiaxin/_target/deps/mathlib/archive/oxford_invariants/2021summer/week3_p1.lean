/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.order
import algebra.big_operators.ring
import data.rat.cast

/-!
# The Oxford Invariants Puzzle Challenges - Summer 2021, Week 3, Problem 1

## Original statement

Let `n ≥ 3`, `a₁, ..., aₙ` be strictly positive integers such that `aᵢ ∣ aᵢ₋₁ + aᵢ₊₁` for
`i = 2, ..., n - 1`. Show that $\sum_{i=1}^{n-1}\dfrac{a_0a_n}{a_ia_{i+1}} ∈ \mathbb N$.

## Comments

Mathlib is based on type theory, so saying that a rational is a natural doesn't make sense. Instead,
we ask that there exists `b : ℕ` whose cast to `α` is the sum we want.

In mathlib, `ℕ` starts at `0`. To make the indexing cleaner, we use `a₀, ..., aₙ₋₁` instead of
`a₁, ..., aₙ`. Similarly, it's nicer to not use substraction of naturals, so we replace
`aᵢ ∣ aᵢ₋₁ + aᵢ₊₁` by `aᵢ₊₁ ∣ aᵢ + aᵢ₊₂`.

We don't actually have to work in `ℚ` or `ℝ`. We can be even more general by stating the result for
any linearly ordered field.

Instead of having `n` naturals, we use a function `a : ℕ → ℕ`.

In the proof itself, we replace `n : ℕ, 1 ≤ n` by `n + 1`.

The statement is actually true for `n = 0, 1` (`n = 1, 2` before the reindexing) as the sum is
simply `0` and `1` respectively. So the version we prove is slightly more general.

Overall, the indexing is a bit of a mess to understand. But, trust Lean, it works.

## Formalised statement

Let `n : ℕ`, `a : ℕ → ℕ`, `∀ i ≤ n, 0 < a i`, `∀ i, i + 2 ≤ n → aᵢ₊₁ ∣ aᵢ + aᵢ₊₂` (read `→` as
"implies"). Then there exists `b : ℕ` such that `b` as an element of any linearly ordered field
equals $\sum_{i=0}^{n-1} (a_0 a_n) / (a_i a_{i+1})$.

## Proof outline

The case `n = 0` is trivial.

For `n + 1`, we prove the result by induction but by adding `aₙ₊₁ ∣ aₙ * b - a₀` to the induction
hypothesis, where `b` is the previous sum, $\sum_{i=0}^{n-1} (a_0 a_n) / (a_i a_{i+1})$, as a
natural.
* Base case:
  * $\sum_{i=0}^0 (a_0 a_{0+1}) / (a_0 a_{0+1})$ is a natural:
    $\sum_{i=0}^0 (a_0 a_{0+1}) / (a_0 a_{0+1}) = (a_0 a_1) / (a_0 a_1) = 1$.
  * Divisibility condition:
    `a₀ * 1 - a₀ = 0` is clearly divisible by `a₁`.
* Induction step:
  * $\sum_{i=0}^n (a_0 a_{n+1}) / (a_i a_{i+1})$ is a natural:
    $$\sum_{i=0}^{n+1} (a_0 a_{n+2}) / (a_i a_{i+1})
      = \sum_{i=0}^n\ (a_0 a_{n+2}) / (a_i a_{i+1}) + (a_0 a_{n+2}) / (a_{n+1} a_{n+2})
      = a_{n+2} / a_{n+1} × \sum_{i=0}^n (a_0 a_{n+1}) / (a_i a_{i+1}) + a_0 / a_{n+1}
      = a_{n+2} / a_{n+1} × b + a_0 / a_{n+1}
      = (a_n + a_{n+2}) / a_{n+1} × b - (a_n b - a_0)(a_{n+1})$$
    which is a natural because `(aₙ + aₙ₊₂)/aₙ₊₁`, `b` and `(aₙ * b - a₀)/aₙ₊₁` are (plus an
    annoying inequality, or the fact that the original sum is positive because its terms are).
  * Divisibility condition:
    `aₙ₊₁ * ((aₙ + aₙ₊₂)/aₙ₊₁ * b - (aₙ * b - a₀)/aₙ₊₁) - a₀ = aₙ₊₁aₙ₊₂b` is divisible by `aₙ₊₂`.
-/

open_locale big_operators

variables {α : Type*} [linear_ordered_field α]

theorem week3_p1 (n : ℕ) (a : ℕ → ℕ) (a_pos : ∀ i ≤ n, 0 < a i)
  (ha : ∀ i, i + 2 ≤ n → a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : α) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  -- Treat separately `n = 0` and `n ≥ 1`
  cases n,
  /- Case `n = 0`
  The sum is trivially equal to `0` -/
  { exact ⟨0, by rw [nat.cast_zero, finset.sum_range_zero]⟩ }, -- `⟨Claim it, Prove it⟩`
  /- Case `n ≥ 1`. We replace `n` by `n + 1` everywhere to make this inequality explicit
  Set up the stronger induction hypothesis -/
  suffices h : ∃ b : ℕ, (b : α) = ∑ i in finset.range (n + 1), (a 0 * a (n + 1))/(a i * a (i + 1))
           ∧ a (n + 1) ∣ a n * b - a 0,
  { obtain ⟨b, hb, -⟩ := h,
    exact ⟨b, hb⟩ },
  simp_rw ←@nat.cast_pos α at a_pos,
  /- Declare the induction
  `ih` will be the induction hypothesis -/
  induction n with n ih,
  /- Base case
  Claim that the sum equals `1`-/
  { refine ⟨1, _, _⟩,
    -- Check that this indeed equals the sum
    { rw [nat.cast_one, finset.sum_range_one, div_self],
      exact (mul_pos (a_pos 0 (nat.zero_le _)) (a_pos 1 (nat.zero_lt_succ _))).ne' },
    -- Check the divisibility condition
    { rw [mul_one, tsub_self],
      exact dvd_zero _ } },
  /- Induction step
  `b` is the value of the previous sum as a natural, `hb` is the proof that it is indeed the value,
  and `han` is the divisibility condition -/
  obtain ⟨b, hb, han⟩ := ih (λ i hi, ha i $ nat.le_succ_of_le hi)
    (λ i hi, a_pos i $ nat.le_succ_of_le hi),
  specialize ha n le_rfl,
  have ha₀ : a 0 ≤ a n * b, -- Needing this is an artifact of `ℕ`-substraction.
  { rw [←@nat.cast_le α, nat.cast_mul, hb, ←div_le_iff' (a_pos _ $ n.le_succ.trans $ nat.le_succ _),
      ←mul_div_mul_right _ _ (a_pos _ $ nat.le_succ _).ne'],
    suffices h : ∀ i, i ∈ finset.range (n + 1) → 0 ≤ (a 0 : α) * a (n + 1) / (a i * a (i + 1)),
    { exact finset.single_le_sum h (finset.self_mem_range_succ n) },
    refine (λ i _, div_nonneg _ _); refine mul_nonneg _ _; exact nat.cast_nonneg _ },
  -- Claim that the sum equals `(aₙ + aₙ₊₂)/aₙ₊₁ * b - (aₙ * b - a₀)/aₙ₊₁`
  refine ⟨(a n + a (n + 2))/ a (n + 1) * b - (a n * b - a 0) / a (n + 1), _, _⟩,
  -- Check that this indeed equals the sum
  { calc
      (((a n + a (n + 2)) / a (n + 1) * b - (a n * b - a 0) / a (n + 1) : ℕ) : α)
        = (a n + a (n + 2)) / a (n + 1) * b - (a n * b - a 0) / a (n + 1) : begin
          norm_cast,
          rw nat.cast_sub (nat.div_le_of_le_mul _),
          rw [←mul_assoc, nat.mul_div_cancel' ha, add_mul],
          exact tsub_le_self.trans (nat.le_add_right _ _),
        end
    ... = a (n + 2) / a (n + 1) * b + (a 0 * a (n + 2)) / (a (n + 1) * a (n + 2))
        : by rw [add_div, add_mul, sub_div, mul_div_right_comm, add_sub_sub_cancel,
            mul_div_mul_right _ _ (a_pos _ le_rfl).ne']
    ... = ∑ (i : ℕ) in finset.range (n + 2), a 0 * a (n + 2) / (a i * a (i + 1))
        : begin
          rw [finset.sum_range_succ, hb, finset.mul_sum],
          congr, ext i,
          rw [←mul_div_assoc, ←mul_div_right_comm, mul_div_assoc, mul_div_cancel _
            (a_pos _ $ nat.le_succ _).ne', mul_comm],
        end },
  -- Check the divisibility condition
  { rw [mul_tsub, ← mul_assoc, nat.mul_div_cancel' ha, add_mul,
      nat.mul_div_cancel' han, add_tsub_tsub_cancel ha₀, add_tsub_cancel_right],
    exact dvd_mul_right _ _ }
end
