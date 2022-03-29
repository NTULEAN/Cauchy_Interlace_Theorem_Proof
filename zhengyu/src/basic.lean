import data.complex.basic
import data.matrix.basic
import data.matrix.notation
import data.matrix.pequiv
import data.fin.basic
import data.list.basic
import linear_algebra.matrix.determinant
import data.multiset.basic
import data.polynomial.basic
import data.polynomial.ring_division -- for polynomial.root

open matrix
open_locale matrix
-- here I prefer to just use fin u, v as that makes describe u * v easier
-- you can def num_t {T: Type*} := fintype T. if you wish abstraction, and use x.elems.card as dimension size.

def mat (u: ℕ) (v: ℕ) := matrix (fin u) (fin v) ℂ
def finPolyMat (u: ℕ) (v: ℕ) := matrix (fin u) (fin v) (polynomial ℂ)
def Hermitian (n: ℕ) (A: mat n n) := A = Aᴴ 
noncomputable def solution (A: polynomial ℂ): multiset ℂ := polynomial.roots A
def toReal (A: multiset ℂ): multiset ℝ := multiset.map (λx: ℂ, x.re) A
noncomputable def rSolution (A: polynomial ℂ) := toReal (solution A)


-- 1. def / structure is just a macro stuff; inductive introduce atomic stuff from nothing
-- 2. Lean seems to discourage naming expressions; as they are determinable by previous args.
-- 3. [imo] difference is that def cannot create new constructors.