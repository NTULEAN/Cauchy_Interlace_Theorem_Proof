import analysis.calculus.deriv
import linear_algebra.matrix.adjugate

open_locale matrix
open matrix
local attribute [instance]  matrix.normed_group matrix.normed_space -- introduce an arbitrary canonical instance of normed_group and normed_space.

variables {𝕜: Type*} [nondiscrete_normed_field 𝕜]
local notation `mat` n := matrix (fin n) (fin n) 𝕜
variable n: ℕ
variable A : 𝕜 → (mat n)

theorem jacobi (A₀ : mat n) (x : 𝕜) (h : has_deriv_at A A₀ x) :
  has_deriv_at (det ∘ A) (trace (fin n) 𝕜 𝕜 (adjugate (A x) ⬝ A₀)) x :=
begin
  sorry
end