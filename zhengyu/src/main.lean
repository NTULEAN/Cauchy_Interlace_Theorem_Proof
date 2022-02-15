import data.complex.basic
import data.matrix.basic
import data.matrix.notation
import data.fin.basic
import data.list.basic
import linear_algebra.matrix.determinant
import data.multiset.basic
import data.polynomial.basic
import data.polynomial.ring_division -- for polynomial.root
-- import linear_algebra.eigenspace 

def finMat (u: ℕ) (v: ℕ) := matrix (fin u) (fin v) ℂ
def finPolyMat (u: ℕ) (v: ℕ) := matrix (fin u) (fin v) (polynomial ℂ)
def Hermitian (n: ℕ) (A: finMat n n) := ∀ i j: fin n, A i j = complex.conj (A j i)

mutual def Interlace, Interlace' {num_t: Type} [linear_order num_t] -- no need [linear_order num_t]
with Interlace: list num_t -> list num_t -> Prop
| (x :: xs) (y :: ys) := (x <= y) ∧ Interlace' xs (y :: ys)
| (x :: xs) nil := true
| _ _ := false
with Interlace': list num_t -> list num_t -> Prop
| (x :: xs) (y :: ys) := (y <= x) ∧ Interlace (x :: xs) ys
| _ _ := false

def principalSubMat {sz: ℕ} (A: finMat (sz + 1) (sz + 1)) (k: fin (sz + 1)) := λ u v: fin sz, 
  if fin.cast_succ u < k then 
    if fin.cast_succ v < k then A u v else A u (v + 1) 
  else
    if (fin.cast_succ v < k) then A (u + 1) v else A (u + 1) (v + 1)

def Id (n: ℕ): finMat n n := λ u v: fin n, if u = v then 1 else 0

noncomputable def solution (A: polynomial ℂ): multiset ℂ := polynomial.roots A
def toReal (A: multiset ℂ): multiset ℝ := multiset.map (λx: ℂ, x.re) A
noncomputable def rSolution (A: polynomial ℂ) := toReal (solution A)

noncomputable def eigenPolynomial {n: ℕ} (A: finMat n n): polynomial ℂ := 
  matrix.det (A.map (λx, polynomial.monomial 0 x) - (Id n).map (λx, polynomial.monomial 1 x)) 

-- i wish to indicate though it is of type complex, the complex part is always zero so I can still apply <
-- < still holds for complex, it's just it's not totality
-- Kevin advises to just rip im off ...
-- because (5, 0): ℂ is fundamentally different thing from 5: ℝ , or 5: ℕ. 

lemma cauchy_interlace_theorem_lemma_1: 
  forall (n: ℕ)
  (A: finMat (n + 1) (n + 1)) (isHerA: Hermitian (n + 1) A) 
  (k: fin (n + 1)), 
    let B := principalSubMat A k, 
        polyA := eigenPolynomial A,
        polyB := eigenPolynomial B in
  forall (a b ∈ rSolution polyA), a ≠ b -> exists (c ∈ rSolution polyB), (a < c) ∧ (c < b) := begin
    intros, 
  end

-- theorem cauchy_interlace_theorem: 
--   forall (n: ℕ)
--   (A: finMat (n + 1) (n + 1)) (isHerA: Hermitian (n + 1) A) 
--   (k: fin (n + 1)), 
--     let B := principalSubMat A k, 
--         polyA := eigenPolynomial A,
--         polyB := eigenPolynomial B,
--         solA  := rSolution polyA,
--         solB  := rSolution polyB  in
--   Interlace solA solB := begin
--     intros, 
--     sorry
--   end

