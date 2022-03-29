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
-- variables {α : Type u}
-- variables {m n : Type*} [fintype m] [fintype n] [decidable_eq m] [decidable_eq n] [has_one n]
variable (n : ℕ) 
-- namespace matrix

variables (M : matrix (fin n) (fin n) ℂ)

-- end matrix

-- def make_mat (M : matrix n n ℂ) : matrix n n ℂ := λ i: n, (λ j : n, (M i j))

-- lemma trace_form (A : matrix n n ℂ) (B : matrix n n ℂ) : ∑ (i : n), ∑ (j : n), (A i j)*(B i j) = ( (A.transpose).mul B).trce :=
-- begin
--   simp only [matrix.trce, matrix.mul],
--   -- ∑ (i j : n), A i j * B i j = ∑ (x : n), Aᵀ x ⬝ᵥ λ (j : n), B j x
--   simp [matrix.transpose, dot_product],
--   exact sum_comm,
--   -- ∑ (i j : n), A i j * B i j = ∑ (x : n), Aᵀ x ⬝ᵥ λ (j : n), B j x
-- end

lemma trace_form (A : matrix (fin n) (fin n) ℂ) (B : matrix (fin n) (fin n) ℂ) : ∑ (i : (fin n)), ∑ (j : (fin n)), (A i j)*(B i j) = matrix.trace (fin n) ℂ ℂ ( (A.transpose).mul B) :=
begin
  simp only [matrix.trace, matrix.mul],
  -- ∑ (i j : n), A i j * B i j = ∑ (x : n), Aᵀ x ⬝ᵥ λ (j : n), B j x
  simp [matrix.transpose, dot_product],
  exact sum_comm,
  -- ∑ (i j : n), A i j * B i j = ∑ (x : n), Aᵀ x ⬝ᵥ λ (j : n), B j x
end

lemma Laplace (A : matrix (fin n.succ) (fin n.succ) ℂ) : ∀ i : (fin n.succ), det A = ∑ (j : (fin n.succ)), (A i j)*(-1)^(i+j : ℕ)*det (A.minor i.succ_above j.succ_above) :=
begin
  intro i,
  have hyp := det_succ_row A i,
  rw hyp,
  simp [add_comm, mul_comm],
end  






