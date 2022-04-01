import data.matrix.basic
import analysis.calculus.fderiv
import analysis.calculus.deriv
import linear_algebra.matrix.adjugate
import analysis.normed_space.finite_dimension
import topology.algebra.module.basic
open matrix
open_locale matrix
variable n: ℕ 

variables {𝕜: Type} [nondiscrete_normed_field 𝕜] -- def 𝕜 := ℝ if you wish to simp things
local attribute [instance] real.nondiscrete_normed_field matrix.normed_group matrix.normed_space -- introduce an arbitrary canonical instance of normed_group and normed_space.
local notation `mat`:1000 := matrix (fin n) (fin n) 𝕜
local notation `trc`:1000 := trace (fin n) 𝕜 𝕜

-- theorem jacobi {A': 𝕜 →L[𝕜] mat} (A: 𝕜 -> mat) (t: 𝕜) (h: has_fderiv_at A A' t): 
--   has_fderiv_at (det ∘ A ) (trace (fin n) 𝕜 𝕜 ((adjugate (A t)) ⬝ (A' t))) t := 

def detdiff (A: mat): ∃ det': mat →L[𝕜] 𝕜, has_fderiv_at det det' A := begin -- determinant is differentiable
  sorry
end
#check (1 : 𝕜 →L[𝕜] 𝕜).smul_right

lemma linearity (f: 𝕜 →L[𝕜] 𝕜): (1: 𝕜 →L[𝕜] 𝕜).smul_right (f 1) = f := begin
  have h: ∀x: 𝕜, (1: 𝕜 →L[𝕜] 𝕜).smul_right (f 1) x = f x := by {
    intro x,
    sorry,
  },
  simp,
end

-- #check [has_coe_to_fun continuous_linear_map]
theorem jacobi {A': 𝕜 →L[𝕜] mat} (A: 𝕜 -> mat) (t: 𝕜) (h: has_fderiv_at A A' t): 
  has_deriv_at (det ∘ A) (trc (adjugate (A t) ⬝ (A' t))) t := begin
    -- L1: (det ∘ A)'(t) = (det)'(A t) ∘ A'(t)
    cases detdiff n (A t) with det' h',
    have L1: has_fderiv_at (det ∘ A) (det'.comp A') t := has_fderiv_at.comp t h' h,

    have suffice: (det'.comp A') 1 = (trace (fin n) 𝕜 𝕜 (adjugate (A t) ⬝ (A' t))) := sorry,

    rw ← suffice,
    unfold has_deriv_at,
    unfold has_fderiv_at at L1,
    unfold has_deriv_at_filter,
    have obvious: (1 : 𝕜 →L[𝕜] 𝕜).smul_right (det'.comp A' 1) = (det'.comp A') := linearity (det'.comp A'),
    rw obvious, exact L1,
end