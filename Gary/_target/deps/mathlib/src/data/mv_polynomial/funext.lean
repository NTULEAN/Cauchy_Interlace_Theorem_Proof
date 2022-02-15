/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.polynomial.ring_division
import data.mv_polynomial.rename
import ring_theory.polynomial.basic

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `mv_polynomial.funext`: two polynomials `φ ψ : mv_polynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/

namespace mv_polynomial

variables {R : Type*} [comm_ring R] [is_domain R] [infinite R]

private lemma funext_fin {n : ℕ} {p : mv_polynomial (fin n) R}
  (h : ∀ x : fin n → R, eval x p = 0) : p = 0 :=
begin
  unfreezingI { induction n with n ih generalizing R },
  { let e := (mv_polynomial.is_empty_ring_equiv R (fin 0)),
    apply e.injective,
    rw ring_equiv.map_zero,
    convert h fin_zero_elim,
    suffices : (eval₂_hom (ring_hom.id _) (is_empty.elim' fin.is_empty)) p =
      (eval fin_zero_elim : mv_polynomial (fin 0) R →+* R) p,
    { rw [← this],
      simp only [coe_eval₂_hom, is_empty_ring_equiv_apply,
        ring_equiv.trans_apply, aeval_eq_eval₂_hom],
      congr },
    exact eval₂_hom_congr rfl (subsingleton.elim _ _) rfl },
  { let e := (fin_succ_equiv R n).to_ring_equiv,
    apply e.injective,
    simp only [ring_equiv.map_zero],
    apply polynomial.funext,
    intro q,
    rw [polynomial.eval_zero],
    apply ih, swap, { apply_instance },
    intro x,
    dsimp [e],
    rw [fin_succ_equiv_apply],
    calc _ = eval _ p : _
       ... = 0 : h _,
    { intro i, exact fin.cases (eval x q) x i },
    apply induction_on p,
    { intro r,
      simp only [eval_C, polynomial.eval_C, ring_hom.coe_comp, eval₂_hom_C], },
    { intros, simp only [*, ring_hom.map_add, polynomial.eval_add] },
    { intros φ i hφ, simp only [*, eval_X, polynomial.eval_mul, ring_hom.map_mul, eval₂_hom_X'],
      congr' 1,
      by_cases hi : i = 0,
      { subst hi, simp only [polynomial.eval_X, fin.cases_zero] },
      { rw [← fin.succ_pred i hi], simp only [eval_X, polynomial.eval_C, fin.cases_succ] } },
    { apply_instance, }, },
end

/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
lemma funext {σ : Type*} {p q : mv_polynomial σ R}
  (h : ∀ x : σ → R, eval x p = eval x q) : p = q :=
begin
  suffices : ∀ p, (∀ (x : σ → R), eval x p = 0) → p = 0,
  { rw [← sub_eq_zero, this (p - q)], simp only [h, ring_hom.map_sub, forall_const, sub_self] },
  clear h p q,
  intros p h,
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p,
  suffices : p = 0, { rw [this, alg_hom.map_zero] },
  apply funext_fin,
  intro x,
  classical,
  convert h (function.extend f x 0),
  simp only [eval, eval₂_hom_rename, function.extend_comp hf]
end

lemma funext_iff {σ : Type*} {p q : mv_polynomial σ R} :
  p = q ↔ (∀ x : σ → R, eval x p = eval x q) :=
⟨by rintro rfl; simp only [forall_const, eq_self_iff_true], funext⟩

end mv_polynomial
