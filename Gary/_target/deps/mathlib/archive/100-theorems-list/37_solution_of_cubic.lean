/-
Copyright (c) 2022 Jeoff Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeoff Lee
-/
import tactic.basic
import ring_theory.roots_of_unity
import ring_theory.polynomial.cyclotomic.basic

/-!
# The Solution of a Cubic

This file proves Theorem 37 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

In this file, we give the solutions to the cubic equation `a * x^3 + b * x^2 + c * x + d = 0` 
over a field `K` that has characteristic neither 2 nor 3, that has a third primitive root of
unity, and in which certain other quantities admit square and cube roots.

This is based on the [Cardano's Formula](https://en.wikipedia.org/wiki/Cubic_equation#Cardano's_formula).

## Main statements

- `cubic_eq_zero_iff` : gives the roots of the cubic equation
where the discriminant `p = 3 * a * c - b^2` is nonzero.
- `cubic_eq_zero_iff_of_p_eq_zero` : gives the roots of the cubic equation 
where the discriminant equals zero.

## References

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL-ex/Cubic_Quartic.html) was written by Amine Chaieb.

## Tags

polynomial, cubic, root
-/

section field

open polynomial

variables {K : Type*} [field K]
variables [invertible (2 : K)] [invertible (3 : K)]
variables (a b c d : K)
variables {ω p q r s t : K}

lemma cube_root_of_unity_sum (hω : is_primitive_root ω 3) : 1 + ω + ω^2 = 0 :=
begin
  convert is_root_cyclotomic (nat.succ_pos _) hω,
  rw [cyclotomic_eq_geom_sum nat.prime_three, eval_geom_sum],
  simp only [geom_sum_succ, geom_sum_zero],
  ring,
end

/-- The roots of a monic cubic whose quadratic term is zero and whose discriminant is nonzero. -/
lemma cubic_basic_eq_zero_iff
  (hω : is_primitive_root ω 3)
  (hp_nonzero : p ≠ 0)
  (hr : r^2 = q^2 + p^3)
  (hs3 : s^3 = q + r)
  (ht : t * s = p)
  (x : K) :
  x^3 + 3 * p * x - 2 * q = 0 ↔
    x = s       - t        ∨
    x = s * ω   - t * ω^2  ∨
    x = s * ω^2 - t * ω    :=
begin
  have h₁ : ∀ x a₁ a₂ a₃ : K, x = a₁ ∨ x = a₂ ∨ x = a₃ ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0,
  { intros, simp only [mul_eq_zero, sub_eq_zero, or.assoc] },
  rw h₁,
  suffices : x ^ 3 + 3 * p * x - 2 * q
    = (x - (s - t)) * (x - (s * ω - t * ω^2)) * (x - (s * ω^2 - t * ω)),
  { rw this, },
  have hc : s^3 - t^3 = 2 * q,
  { have : s ≠ 0 := λ h, by { apply hp_nonzero, rw [h, mul_zero] at ht, exact ht.symm },
    have h_nonzero: q + r ≠ 0 := by { rw ← hs3, exact pow_ne_zero _ this },
    have hp3 : p^3 = r^2 - q^2 := by { rw hr, ring },
    calc    s^3 - t^3
          = s^3 - p^3/s^3 : by { rw [← ht], field_simp, ring }
      ... = (q+r) - (r^2-q^2)/(q+r) : by rw [hs3, hp3]
      ... = (q+r) + (q-r) * ((q+r) / (q+r)) : by ring
      ... = 2 * q : by { rw div_self h_nonzero, ring } },
  symmetry,
  calc (x - (s - t)) * (x - (s * ω - t * ω^2)) * (x - (s * ω^2 - t * ω))
      = x^3 - (s-t) * (1+ω+ω^2) * x^2
        + ((s^2+t^2)*ω*(1+ω+ω^2) - s*t*(-3 + 3*(1+ω+ω^2) + ω*(ω^3-1))) * x
        - (s^3-t^3)*ω^3 + s*t*(s-t)*ω^2*(1+ω+ω^2) : by ring
  ... = x^3 + 3*(t*s)*x - (s^3-t^3)
    : by { rw [hω.pow_eq_one, cube_root_of_unity_sum hω], ring }
  ... = x^3 + 3*p*x - 2*q : by rw [ht, hc]
end

/-- Roots of a monic cubic whose discriminant is nonzero. -/
lemma cubic_monic_eq_zero_iff
  (hω : is_primitive_root ω 3)
  (hp : p = (3 * c - b^2) / 9)
  (hp_nonzero : p ≠ 0)
  (hq : q = (9 * b * c - 2 * b^3 - 27 * d) / 54)
  (hr : r^2 = q^2 + p^3)
  (hs3 : s^3 = q + r)
  (ht : t * s = p)
  (x : K) :
  x^3 + b * x^2 + c * x + d = 0 ↔
    x = s       - t       - b / 3 ∨
    x = s * ω   - t * ω^2 - b / 3 ∨
    x = s * ω^2 - t * ω   - b / 3 :=
begin
  let y := x + b / 3,
  have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _,
  have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _,
  have h9 : (9 : K) = 3^2 := by norm_num,
  have h54 : (54 : K) = 2*3^3 := by norm_num,
  have h₁ : x^3 + b * x^2 + c * x + d = y^3 + 3 * p * y - 2 * q,
  { dsimp only [y],
    rw [hp, hq],
    field_simp [h9, h54], ring, },
  rw [h₁, cubic_basic_eq_zero_iff hω hp_nonzero hr hs3 ht y],
  dsimp only [y],
  simp_rw [eq_sub_iff_add_eq],
end

/-- **The Solution of Cubic**.
  The roots of a cubic polynomial whose discriminant is nonzero. -/
theorem cubic_eq_zero_iff (ha : a ≠ 0)
  (hω : is_primitive_root ω 3)
  (hp : p = (3 * a * c - b^2) / (9 * a^2))
  (hp_nonzero : p ≠ 0)
  (hq : q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3))
  (hr : r^2 = q^2 + p^3)
  (hs3 : s^3 = q + r)
  (ht : t * s = p)
  (x : K) :
  a * x^3 + b * x^2 + c * x + d = 0 ↔
    x = s       - t       - b / (3 * a) ∨
    x = s * ω   - t * ω^2 - b / (3 * a) ∨
    x = s * ω^2 - t * ω   - b / (3 * a) :=
begin
  have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _,
  have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _,
  have h9 : (9 : K) = 3^2 := by norm_num,
  have h54 : (54 : K) = 2*3^3 := by norm_num,
  have h₁ : a * x^3 + b * x^2 + c * x + d = a * (x^3 + b/a * x^2 + c/a * x + d/a),
  { field_simp, ring },
  have h₂ : ∀ x, a * x = 0 ↔ x = 0, { intros x, simp [ha], },
  have hp' : p = (3 * (c/a) - (b/a) ^ 2) / 9, { field_simp [hp, h9], ring_nf },
  have hq' : q = (9 * (b/a) * (c/a) - 2 * (b/a) ^ 3 - 27 * (d/a)) / 54,
  { field_simp [hq, h54], ring_nf },
  rw [h₁, h₂, cubic_monic_eq_zero_iff (b/a) (c/a) (d/a) hω hp' hp_nonzero hq' hr hs3 ht x],
  have h₄ := calc b / a / 3 = b / (a * 3) : by { field_simp [ha] }
                        ... = b / (3 * a) : by rw mul_comm,
  rw [h₄],
end

/-- the solution of the cubic equation when p equals zero. -/
lemma cubic_eq_zero_iff_of_p_eq_zero (ha : a ≠ 0)
  (hω : is_primitive_root ω 3)
  (hpz : 3 * a * c - b^2 = 0)
  (hq : q = (9 * a * b * c - 2 * b^3 - 27 * a^2 * d) / (54 * a^3))
  (hs3 : s^3 = 2 * q)
  (x : K) :
  a * x^3 + b * x^2 + c * x + d = 0 ↔
    x = s       - b / (3 * a) ∨
    x = s * ω   - b / (3 * a) ∨
    x = s * ω^2 - b / (3 * a) :=
begin
  have h₁ : ∀ x a₁ a₂ a₃ : K, x = a₁ ∨ x = a₂ ∨ x = a₃ ↔ (x - a₁) * (x - a₂) * (x - a₃) = 0,
  { intros, simp only [mul_eq_zero, sub_eq_zero, or.assoc] },
  have hi2 : (2 : K) ≠ 0 := nonzero_of_invertible _,
  have hi3 : (3 : K) ≠ 0 := nonzero_of_invertible _,
  have h54 : (54 : K) = 2*3^3 := by norm_num,
  have hb2 : b^2 = 3 * a * c, { rw sub_eq_zero at hpz, rw hpz },
  have hb3 : b^3 = 3 * a * b * c, { rw [pow_succ, hb2], ring },
  have h₂ :=
    calc  a * x^3 + b * x^2 + c * x + d
        = a * (x + b/(3*a))^3 + (c - b^2/(3*a)) * x + (d - b^3*a/(3*a)^3)
          : by { field_simp, ring }
    ... = a * (x + b/(3*a))^3 + (d - (9*a*b*c-2*b^3)*a/(3*a)^3)
          : by { simp only [hb2, hb3], field_simp, ring }
    ... = a * ((x + b/(3*a))^3 - s^3)
          : by { rw [hs3, hq], field_simp [h54], ring, },
  have h₃ : ∀ x, a * x = 0 ↔ x = 0, { intro x, simp [ha] },
  have h₄ : ∀ x : K, x^3 - s^3 = (x - s) * (x - s * ω) * (x - s * ω^2),
  { intro x,
    calc  x^3 - s^3
        = (x - s) * (x^2 + x*s + s^2) : by ring
    ... = (x - s) * (x^2 - (ω+ω^2)*x*s + (1+ω+ω^2)*x*s + s^2) : by ring
    ... = (x - s) * (x^2 - (ω+ω^2)*x*s + ω^3*s^2)
        : by { rw [hω.pow_eq_one, cube_root_of_unity_sum hω], simp, }
    ... = (x - s) * (x - s * ω) * (x - s * ω^2) : by ring },
  rw [h₁, h₂, h₃, h₄ (x + b/(3*a))],
  ring_nf,
end

end field
