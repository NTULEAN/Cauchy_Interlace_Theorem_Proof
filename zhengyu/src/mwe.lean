import data.fintype.basic
import data.real.basic
import data.matrix.basic
import linear_algebra.matrix
import analysis.calculus.fderiv
import analysis.calculus.deriv

open_locale matrix 
open fintype finset matrix complex 
local attribute [instance] real.nondiscrete_normed_field matrix.normed_group matrix.normed_space -- introduce an arbitrary canonical instance of normed_group and normed_space.

variable n: ℕ 
def mat := matrix (fin n) (fin n) ℝ -- mat n is square matrix of size n 
variable A : ℝ -> (mat n) -- A is any map from R to square matrix of size n

theorem jacobi [normed_group (mat n)] [normed_space ℝ (mat n)]: 
  ∀(x: ℝ) , differentiable_at ℝ A x -> deriv (det ∘ A) x = matrix.trace (fin n) ℝ ℝ (adjugate(A x) ⬝ (deriv A x)) :=
begin
  intro x,
  set f'comp := deriv (det ∘ A) with hmh,
  set f'det: mat n →L[ℝ] ℝ := fderiv ℝ det (A x) with f1h,
  set f'A:  ℝ →L[ℝ] (mat n) := fderiv ℝ A x with f2h,
 have hg : has_fderiv_at det (f'det: (matrix (fin n) (fin n) ℝ) →L[ℝ] ℝ) (A x),
 sorry

end