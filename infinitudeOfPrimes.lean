import data.nat.prime
import tactic.linarith

theorem infinitude_of_primes : ∀ N : ℕ, ∃ p ≥ N, nat.prime p :=
begin
  intro N,

  let M := nat.factorial N + 1,
  let p := nat.min_fac M,

  have pp : nat.prime p :=
  begin
    refine nat.min_fac_prime _,
    have : nat.factorial N > 0 := nat.factorial_pos N,
    linarith,
  end,

  use p,
  split,
  { by_contradiction,
    have h₁ : p ∣ nat.factorial N + 1 := nat.min_fac_dvd M,
    have h₂ : p ∣ nat.factorial N :=
    begin
      refine nat.dvd_factorial _ _,
      exact nat.prime.pos pp,
      exact le_of_not_ge h
    end,
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁,
    exact nat.prime.not_dvd_one pp h, },
  { exact pp, },
end
