/-
Copyright (c) 2021 Gabriel Moise. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Gabriel Moise.
-/

import data.complex.basic
import data.complex.module
import data.fintype.basic
import data.real.basic
import linear_algebra.matrix

/-!
# Symmetric Matrices
This module defines symmetric matrices, together with key properties about their eigenvalues & eigenvectors.
It uses a more restrictive definition of eigenvalues & eigenvectors, together with helping lemmas for vector-matrix
operations and tools for complex numbers/vectors.
TODO : make the eigen-definitions consistent with the ones already defined in linear_algebra.eigenspace
## Main definitions
* `vec_conj x` - the complex conjugate of a complex vector `x`
* `vec_re x` - the vector containing the real parts of elements from x
* `vec_im x` - the vector containing the imaginary parts of elements from x
* `has_eigenpair M μ x` - matrix `M` has non-zero eigenvector `x` with corresponding eigenvalue `μ`
* `has_eigenvector M x` - matrix `M` has non-zero eigenvector `x`
* `has_eigenvalue M μ`  - matrix `M` has eigenvalue `μ`
* `symm_matrix M` - `M` is a symmetric matrix
## Main statements
1. If x is an eigenvector of matrix M, then a • x is an eigenvector of M, for any non-zero a : ℂ.
2. If there are two eigenvectors of M that have the same correspoding eigenvalue, then any linear combination of them
is also an eigenvector of M with the same eigenvalue μ.
3. All eigenvalues of a symmetric real matrix M are real.
4. For every real eigenvalue of a symmetric matrix M, there exists a corresponding real-valued eigenvector.
5. If v and w are eigenvectors of a symmetric matrix M with different eigenvalues, then v and w are orthogonal.
## References
<https://www.doc.ic.ac.uk/~ae/papers/lecture05.pdf>
<https://sharmaeklavya2.github.io/theoremdep/nodes/linear-algebra/eigenvectors/real-matrix-with-real-eigenvalue-has-real-eigenvectors.html>
-/

open_locale matrix big_operators
open_locale complex_conjugate
open fintype finset matrix complex

universes u
variables {α : Type u}
variables {m n : Type*} [fintype m] [fintype n]

lemma vec_eq_unfold (x y : n → α) : (λ i : n, x i) = (λ i : n, y i) ↔ ∀ i : n, x i = y i :=
begin
  split,
  { intros hyp i, exact congr_fun hyp i },
  { intro hyp, ext, apply hyp }
end

-- ## Coercions
instance : has_coe (n → ℝ) (n → ℂ) := ⟨λ x, (λ i, ⟨x i, 0⟩)⟩
instance : has_coe (matrix m n ℝ) (matrix m n ℂ) := ⟨λ M, (λ i j, ⟨M i j, 0⟩)⟩

-- ## Lemmas on ℂ

lemma conj_of_zero_im {μ : ℂ} (H_im : μ.im = 0) : conj μ = μ :=
by { ext; simp only [conj_re, conj_im, H_im, neg_zero] }

lemma sum_complex_re {x : n → ℂ} : (∑ i : n, x i).re = ∑ i : n, (x i).re := by exact complex.re_lm.map_sum

lemma sum_complex_im {x : n → ℂ} : (∑ i : n, x i).im = ∑ i : n, (x i).im := by exact complex.im_lm.map_sum

-- The real and complex parts of a complex vector
def vec_re (x : n → ℂ) : n → ℝ := λ i : n, (x i).re
def vec_im (x : n → ℂ) : n → ℝ := λ i : n, (x i).im

-- Defining the complex conjugate of a complex vector
section vec_conj

def vec_conj (x : n → ℂ) : n → ℂ := λ i : n, conj (x i)

-- (μ • x)* = μ* • x*
lemma vec_conj_smul (μ : ℂ) (x : n → ℂ) :
  vec_conj (μ • x) = (conj μ) • (vec_conj x) :=
by { ext ; simp only [vec_conj, algebra.id.smul_eq_mul, pi.smul_apply, ring_hom.map_mul] }

-- ↑A i j = ↑(A i j)
lemma coe_matrix_coe_elem (i : m) (j : n) (A : matrix m n ℝ) : (A : matrix m n ℂ) i j = ↑(A i j) := by exact rfl

-- (A ⬝ x)* = A ⬝ x*
lemma vec_conj_mul_vec [decidable_eq n] [nonempty n] (A : matrix m n ℝ) (x : n → ℂ) :
  vec_conj ((A : matrix m n ℂ).mul_vec x) = (A : matrix m n ℂ).mul_vec (vec_conj x) :=
begin
  ext,
  simp only [vec_conj, mul_vec, dot_product, conj_re, coe_matrix_coe_elem, sum_complex_re, mul_re, of_real_im, zero_mul],
  simp only [vec_conj, mul_vec, dot_product, conj_im, coe_matrix_coe_elem, sum_complex_im, mul_im, add_zero, of_real_im,
    zero_mul, sum_neg_distrib, mul_neg_eq_neg_mul_symm]
end

lemma vec_norm_sq_zero {x : n → ℂ} (H_dot : dot_product (vec_conj x) x = 0) : x = 0 :=
begin
  unfold dot_product at H_dot,
  simp only [vec_conj, mul_comm, mul_conj, complex.ext_iff, sum_complex_re, zero_re, of_real_re] at H_dot,
  cases H_dot with H_re H_im,
  have key : ∑ i in (univ : finset n), norm_sq (x i) = 0 ↔ ∀ i ∈ (univ : finset n), norm_sq(x i) = 0,
  { apply sum_eq_zero_iff_of_nonneg, intros i h_univ, exact norm_sq_nonneg (x i) },
  simp only [forall_prop_of_true, mem_univ, monoid_with_zero_hom.map_eq_zero] at key,
  rw key at H_re,
  ext i;
  { specialize H_re i, simp only [H_re, pi.zero_apply] }
end

lemma coe_vec_re (x : n → ℂ) {i : n} : (vec_re x : n → ℂ) i = ((x i).re : ℂ) :=
by simpa only [vec_re]

lemma vec_add_conj_eq_two_re (x : n → ℂ) : x + vec_conj x = (2 : ℂ) • (vec_re x : n → ℂ) :=
begin
  ext,
  { simp [vec_conj, coe_vec_re x], linarith },
  { simp [vec_conj, coe_vec_re x] }
end

lemma vec_conj_add_zero {x : n → ℂ} (H : x + vec_conj x = 0) : vec_re x = 0 :=
begin
  rw [vec_add_conj_eq_two_re, smul_eq_zero] at H,
  cases H with H_20 H_x,
  { exfalso, simp at H_20, assumption }, -- 2 = 0
  { rw function.funext_iff at H_x,
    ext i,
    specialize H_x i,
    rw coe_vec_re at H_x,
    simp only [of_real_eq_zero, pi.zero_apply] at H_x,
    simp only [vec_re, H_x, pi.zero_apply] }
end

end vec_conj

namespace matrix

variables (M : matrix n n ℝ)

def Coe (M : matrix m n ℝ) := (M : matrix m n ℂ)

/--
## Matrix definitions
Let `M` be a square real matrix. An `eigenvector` of `M` is a complex vector `x` with `M ⬝ x = μ • x`
for some `μ ∈ ℂ`, which is called the `eigenvalue` of `M` corresponding to the `eigenvector x`.
-/
def has_eigenpair (μ : ℂ) (x : n → ℂ) : Prop :=
  x ≠ 0 ∧ (mul_vec M.Coe x = μ • x)

def has_eigenvector (x : n → ℂ) : Prop :=
  ∃ μ : ℂ, M.has_eigenpair μ x

def has_eigenvalue (μ : ℂ) : Prop :=
  ∃ x : n → ℂ, M.has_eigenpair μ x

def symm_matrix : Prop := M = Mᵀ

-- ## Matrix : Helping lemmas

-- (↑M)ᵀ = ↑Mᵀ
lemma coe_transpose_matrix : (M.Coe)ᵀ = (Mᵀ).Coe := by { unfold Coe, ext, tidy }

-- ↑M i j = ↑(M i j)
lemma coe_matrix_coe_elem (i j : n) : (M.Coe) i j = ↑(M i j) := by exact rfl

-- (M x)* = M x*
lemma vec_conj_mul_vec_re (x : n → ℂ) :
  vec_conj (mul_vec M.Coe x) = mul_vec (M.Coe) (vec_conj x) :=
begin
  ext ;
  simp only [vec_conj, mul_vec, dot_product, coe_matrix_coe_elem],
  { simp only [sum_complex_re, of_real_im, zero_mul, conj_re, mul_re] },
  { simp only [sum_complex_im, add_zero, of_real_im, zero_mul,
               sum_neg_distrib, conj_im, mul_neg_eq_neg_mul_symm, mul_im] },
end

lemma symm_matrix_coe (H_symm : symm_matrix M) : (M.Coe) = (M.Coe)ᵀ :=
begin
  unfold symm_matrix at H_symm,
  rw [coe_transpose_matrix, ← H_symm]
end

-- vᵀ (M w) = (vᵀ M)ᵀ w
lemma dot_product_mul_vec_vec_mul (v w : n → ℂ) :
  dot_product v (mul_vec M.Coe w) = dot_product (vec_mul v M.Coe) w :=
begin
  have key : vec_mul v M.Coe = λ j, dot_product v (λ i, M.Coe i j),
  { ext ; unfold vec_mul },
  rw [key, dot_product_assoc v w M.Coe],
  ext ; simp only [dot_product, mul_vec],
end

-- 1. If x is an eigenvector of M, then a • x is an eigenvector of M, for any non-zero a : ℂ.
theorem has_eigenvector_smul (a : ℂ) (x : n → ℂ) (H_na : a ≠ 0) (H_eigenvector : has_eigenvector M x) :
  has_eigenvector M (a • x) :=
begin
  rcases H_eigenvector with ⟨μ, ⟨H_nx, H_mul⟩⟩,
  use μ, -- corresponding eigenvalue μ
  split,
  { intro hyp, rw smul_eq_zero at hyp, tauto }, -- a • x ≠ 0
  calc (M.Coe).mul_vec (a • x)
      = a • M.Coe.mul_vec x : -- M ⬝ (a • x) = a • (M ⬝ x)
  by { rw mul_vec_smul_assoc }
  ... = a • (μ • x) :                 -- ... = a • (μ • x)
  by { rw H_mul }
  ... = μ • (a • x) :                 -- ... = μ • (a • x)
  by { simp only [smul_smul, mul_comm] }
end

-- 2. If there are two eigenvectors that have the same correspoding eigenvalue μ,
-- then any non-zero linear combination of them is also an eigenvector with the same eigenvalue μ.
theorem has_eigenpair_linear (a b : ℂ) (v w : n → ℂ) (μ : ℂ) (H_ne : a • v + b • w ≠ 0)
(H₁ : has_eigenpair M μ v) (H₂ : has_eigenpair M μ w) : has_eigenpair M μ (a • v + b • w) :=
begin
  rcases H₁ with ⟨H₁₁, H₁₂⟩,
  rcases H₂ with ⟨H₂₁, H₂₂⟩,
  use H_ne, -- a • v + b • w ≠ 0
  calc M.Coe.mul_vec (a • v + b • w) -- M ⬝ (a • v + b • w) = M ⬝ (a • v) + M ⬝ (b • w)
      = M.Coe.mul_vec(a • v) + M.Coe.mul_vec(b • w) :
  by { ext ; simp only [mul_vec, pi.add_apply, dot_product_add] }
  ... = a • M.Coe.mul_vec v + b • M.Coe.mul_vec w :  -- ... = a • (M ⬝ v) + b • (M ⬝ w)
  by { ext ; simp only [mul_vec, algebra.id.smul_eq_mul,
                        dot_product_smul, pi.add_apply, pi.smul_apply] }
  ... = a • (μ • v) + b • (μ • w) :                  -- ... = a • (μ • v) + b • (μ • w)
  by { rw [H₁₂, H₂₂] }
  ... = μ • (a • v + b • w) :                        -- ... = μ • (a • v + b • w)
  by { simp only [smul_smul, mul_comm, smul_add] }
end

-- 3. All eigenvalues of a symmetric real matrix M are real.
theorem symm_matrix_real_eigenvalues (H_symm : symm_matrix M) :
  ∀ (μ : ℂ), has_eigenvalue M μ → μ.im = 0 :=
begin
  -- (1) M ⬝ x = μ • x
  rintro μ ⟨x, ⟨H_x, H_eq₁⟩⟩,
  -- (2) M ⬝ x* = μ* • x*
  have H_eq₂ : mul_vec M.Coe (vec_conj x) = (conj μ) • (vec_conj x),
  { rw [← vec_conj_smul μ x, ← M.vec_conj_mul_vec_re x, H_eq₁] },
  -- (3) μ ((x*)ᵀ x) = μ* ((x*)ᵀ x)
  have H_eq₃ : μ * (dot_product (vec_conj x) x) = conj μ * dot_product (vec_conj x) x,

  calc μ * (dot_product (vec_conj x) x)
      = dot_product (vec_conj x) (μ • x) :    -- μ ((x*)ᵀ x) = (x*)ᵀ (μ x)
  by { 
    -- sorry
  rw dot_product_comm _ _,
  -- μ * x ⬝ᵥ vec_conj x = vec_conj x ⬝ᵥ μ • x
  refine eq.symm _,
  rw dot_product_comm _ _,
  -- vec_conj x ⬝ᵥ μ • x = μ * vec_conj x ⬝ᵥ x
  rw smul_dot_product μ x (vec_conj x),
  simp [dot_product, vec_conj, ← mul_assoc, mul_comm],
  }
  ... = dot_product (vec_conj x) (M.Coe.mul_vec x) :  -- ... = (x*)ᵀ (M x)
  by { rw ← H_eq₁ }
  ... = dot_product (M.Coe.vec_mul (vec_conj x)) x :  -- ... = ((x*)ᵀ M) x
  by { exact (dot_product_assoc (vec_conj x) x M.Coe).symm }
  ... = dot_product (M.Coeᵀ.mul_vec (vec_conj x)) x : -- ... = (Mᵀ x*)ᵀ x
  by { rw ← mul_vec_transpose M.Coe (vec_conj x) }
  ... = dot_product (M.Coe.mul_vec (vec_conj x)) x :  -- ... = (M x*)ᵀ x
  by { 
    -- sorry
    have H : M.Coe = M.Coeᵀ, 
    { 
    unfold Coe,
    exact congr_arg coe H_symm,
    }, 
    rw ← H 
    }
  ... = dot_product (conj μ • vec_conj x) x :         -- ... = (μ* x*)ᵀ x
  by { rw H_eq₂ }
  ... = conj μ * dot_product (vec_conj x) x :         -- ... = μ* ((x*)ᵀ x)
  by { 
    rw smul_dot_product (conj μ) (vec_conj x) x,
    simp,
    },

  -- (4) (μ - μ*) ((x*)ᵀ x) = 0
  have H_eq₄ : (μ - conj μ) * dot_product (vec_conj x) x = 0,
  { rw sub_mul, simp only [H_eq₃, sub_self] },
  -- μ - μ* = 0 ∨ (x*)ᵀ x = 0
  rw mul_eq_zero at H_eq₄,
  cases H_eq₄ with H_μ H_prod,
  { rw [sub_eq_zero, eq_comm, eq_conj_iff_real] at H_μ,
    cases H_μ with r H_r,
    rw [H_r, of_real_im] }, -- μ - μ* = 0
  { exfalso,
    exact H_x (vec_norm_sq_zero H_prod) }, -- (x*)ᵀ x = 0
end

-- 4. For every real eigenvalue of a symmetric matrix M, there exists a corresponding real-valued eigenvector.
theorem symm_matrix_real_eigenvectors (H_symm : symm_matrix M) (μ : ℂ) (H_eigenvalue : has_eigenvalue M μ) :
  ∃ x : n → ℂ, has_eigenpair M μ x ∧ vec_im x = 0 :=
begin
  -- We know that μ ∈ ℝ from before.
  have H_μ : μ.im = 0,
  { apply M.symm_matrix_real_eigenvalues H_symm μ H_eigenvalue },
  rcases H_eigenvalue with ⟨x, ⟨H_nx, H_mul⟩⟩,
  by_cases H_re : vec_re x = 0,
  -- 1) I • x will be used
  { use (I • x),
    split,
    -- 1.1) I • x is an eigenvector
    { split,
      -- 1.1.1) I • x ≠ 0
      { intro hyp, rw smul_eq_zero at hyp,
        have H_nI : I ≠ 0, { exact I_ne_zero },
        tauto },
      -- 1.1.2) M (I • x) = μ • (I • x)
      { simp only [mul_vec_smul_assoc, H_mul, smul_smul, mul_comm] } },
    -- 1.2) I • x ∈ ℝⁿ
    { ext i,
      simp only [vec_re, vec_eq_unfold] at H_re,
      simp only [vec_im, algebra.id.smul_eq_mul, I_re, one_mul,
                 I_im, zero_mul, mul_im, zero_add, pi.smul_apply],
      exact H_re i } },
  -- 2) x + x* will be used
  { use (x + vec_conj x),
    split,
    -- 2.1) x + x* is an eigenvector
    { split,
      -- 2.1.1) x + x* ≠ 0
      { intro hyp, exact H_re (vec_conj_add_zero hyp) },
      -- 2.1.2) M (x + x*) = μ • (x + x*)
      { calc M.Coe.mul_vec (x + vec_conj x)
            = M.Coe.mul_vec x + M.Coe.mul_vec (vec_conj x) :
        by { apply mul_vec_add } -- M (x + x*) = M x + M x*
        ... = M.Coe.mul_vec x + vec_conj (M.Coe.mul_vec x) :
        by { rw ← M.vec_conj_mul_vec_re x }     -- ... = M x + (M x)*
        ... = μ • x + vec_conj (μ • x) :
        by { rw H_mul }                         -- ... = μ • x + (μ • x)*
        ... = μ • x + (conj μ) • (vec_conj x) :
        by { rw vec_conj_smul }                 -- ... = μ • x + μ* • x*
        ... = μ • x + μ • (vec_conj x) :
        by { rw conj_of_zero_im H_μ }           -- ... = μ • x + μ • x*
        ... = μ • (x + vec_conj x) :
        by { simp only [smul_add] } } },        -- ... = μ • (x + x*)
    -- 2.2) x + x* ∈ ℝⁿ
    { ext, simp [vec_add_conj_eq_two_re, vec_im, coe_vec_re] } }
end

-- 5. If v and w are eigenvectors of a symmetric matrix M with different eigenvalues, then v and w are orthogonal.
theorem dot_product_neq_eigenvalue_zero (H_symm : symm_matrix M) (v w : n → ℂ) (μ μ' : ℂ)
(H_ne : μ ≠ μ') (H₁ : has_eigenpair M μ v) (H₂ : has_eigenpair M μ' w) : dot_product v w = 0 :=
begin
  have key : (μ - μ') * dot_product v w = 0,
  calc (μ - μ') * dot_product v w
      = μ * dot_product v w - μ' * dot_product v w :
  by { apply mul_sub_right_distrib }-- (μ - μ')vᵀ w = μ(vᵀ w) - μ'(vᵀ w)
  ... = dot_product (μ • v) w - dot_product v (μ' • w) :
  by { 
  --   -- sorry
  --       -- sorry
  -- rw dot_product_comm _ _,
  -- -- μ * x ⬝ᵥ vec_conj x = vec_conj x ⬝ᵥ μ • x
  -- refine eq.symm _,
  -- rw dot_product_comm _ _,
  -- -- vec_conj x ⬝ᵥ μ • x = μ * vec_conj x ⬝ᵥ x
  -- rw smul_dot_product μ x (vec_conj x),
  -- simp [dot_product, vec_conj, ← mul_assoc, mul_comm],
    simp only [dot_product_smul, smul_dot_product],
    simp,
  }                   -- ... = (μ • v)ᵀw - vᵀ(μ' • w)
  ... = dot_product (M.Coe.mul_vec v) w - dot_product v (M.Coe.mul_vec w) :
  by { rw [H₁.2, H₂.2] }                     -- ... = (M v)ᵀw - vᵀ(M w)
  ... = dot_product (M.Coe.mul_vec v) w - dot_product (vec_mul v M.Coe) w :
  by { rw M.dot_product_mul_vec_vec_mul v w }-- ... = (M v)ᵀw - (vᵀ M)ᵀw
  ... = dot_product (M.Coe.mul_vec v) w - dot_product (vec_mul v M.Coeᵀ) w:
  by { rw ← symm_matrix_coe M H_symm }  -- ... = (M v)ᵀw - (vᵀ Mᵀ)ᵀw
  ... = dot_product (M.Coe.mul_vec v) w - dot_product (mul_vec M.Coe v) w :
  by { rw ← vec_mul_transpose M.Coe v }       -- ... = (M v)ᵀw - (M v)ᵀw
  ... = 0 :
  by { simp only [sub_self] },               -- ... = 0
  rw mul_eq_zero at key,
  cases key with H_μ H_dot,
  { exfalso, rw sub_eq_zero at H_μ, exact H_ne H_μ }, -- μ - μ' = 0
  { exact H_dot } -- vᵀ w = 0
end

-- TODOs :
-- 1. positive semidefinite matrices
-- 2. eigenvalues = roots of characteristic polynomial (char_poly)
-- 3. eigendecomposition of a diagonalizable matrix

end matrix