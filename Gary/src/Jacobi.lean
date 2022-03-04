import data.complex.basic
import data.complex.module
import data.fintype.basic
import data.real.basic
import data.matrix.basic
import linear_algebra.matrix

open_locale matrix big_operators
open_locale complex_conjugate
open fintype finset matrix complex

universes u
variables {α : Type u}
variables {m n : Type*} [fintype m] [fintype n]

namespace matrix

variables (M : matrix n n ℂ)

def trce (M : matrix n n ℂ) := ∑ (i : n), M i i

end matrix

-- def make_mat (M : matrix n n ℂ) : matrix n n ℂ := λ i: n, (λ j : n, (M i j))

lemma trace_form (A : matrix n n ℂ) (B : matrix n n ℂ) : ∑ (i : n), ∑ (j : n), (A i j)*(B i j) = ( (A.transpose).mul B).trce :=
begin
  simp only [matrix.trce, matrix.mul],
  -- ∑ (i j : n), A i j * B i j = ∑ (x : n), Aᵀ x ⬝ᵥ λ (j : n), B j x
  simp [matrix.transpose, dot_product],
  exact sum_comm,
  -- ∑ (i j : n), A i j * B i j = ∑ (x : n), Aᵀ x ⬝ᵥ λ (j : n), B j x
end


