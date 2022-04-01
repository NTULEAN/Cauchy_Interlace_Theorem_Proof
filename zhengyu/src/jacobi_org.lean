import data.fintype.basic
import data.real.basic
import data.matrix.basic
import linear_algebra.matrix
import analysis.calculus.fderiv
import analysis.calculus.deriv

open_locale matrix big_operators complex_conjugate
open fintype finset matrix complex 
open_locale topological_space classical nnreal filter asymptotics ennreal
local attribute [instance] real.nondiscrete_normed_field matrix.normed_group matrix.normed_space -- introduce an arbitrary canonical instance of normed_group and normed_space.

noncomputable theory


variable n: ℕ 
def mat := matrix (fin n) (fin n) ℝ -- mat n is square matrix of size n 
variable A : ℝ -> (mat n) -- A is any map from R to square matrix of size n
def 𝕜 := ℝ -- it's not scaling factor σ (see notation); it's the common semiring of the two modules you are operating. 

-- some examples for understanding:
  -- dA / dt, under regular derivative.
  noncomputable def DA [normed_group (mat n)] [normed_space ℝ (mat n)] (x: ℝ): (mat n) := deriv A x

  -- Frechet dA / dt, under arbitrary canonical norm on vector space of matrices.
  noncomputable def DA_fderiv [normed_group (mat n)] [normed_space ℝ (mat n)] (x: ℝ): (mat n) := fderiv ℝ A x (1: ℝ)

  -- Frechet dA / dt == dA / dt as in usual derivative.
  lemma triv [normed_group (mat n)] [normed_space ℝ (mat n)] : DA = DA_fderiv := begin
    sorry
    -- strangely, unable to fold def
  end
  -- we can further prove the deriv corresponds to elementwise derivative from two applications of has_deriv_at_pi
  lemma triv2 [normed_group (mat n)] [normed_space ℝ (mat n)] : ∀x, deriv A x = fderiv ℝ A x (1: ℝ) := begin
    unfold deriv, intro x, refl,
  end

  -- d det A(t) / dt, under arbitrary canonical norm on vector space of matrices.
  noncomputable def DDetA (x: ℝ) := fderiv ℝ (det ∘ A) x

-- Jacobi's Formula: For any differentiable map A, ...
theorem jacobi [normed_group (mat n)] [normed_space ℝ (mat n)]: 
  ∀(x: ℝ) , differentiable_at ℝ A x -> deriv (det ∘ A) x = trace (fin n) ℝ ℝ (adjugate(A x) ⬝ (deriv A x)) :=
begin
  intro x,

  set f'comp := deriv (det ∘ A) with hmh,
  set f'det: mat n →L[ℝ] ℝ := fderiv ℝ det (A x) with f1h,
  set f'A:  ℝ →L[ℝ] (mat n) := fderiv ℝ A x with f2h,

  -- L1
  have L1: f'comp = f'det ∘ f'A := begin
    have hg : has_fderiv_at det (f'det: (matrix (fin n) (fin n) ℝ) →L[ℝ] ℝ) (A x),
    
  end



end
