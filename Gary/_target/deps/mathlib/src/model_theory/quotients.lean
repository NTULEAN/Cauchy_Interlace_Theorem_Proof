/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import data.fintype.basic
import model_theory.terms_and_formulas

/-!
# Quotients of First-Order Structures
This file defines prestructures and quotients of first-order structures.

## Main Definitions
* If `s` is a setoid (equivalence relation) on `M`, a `first_order.language.prestructure s` is the
data for a first-order structure on `M` that will still be a structure when modded out by `s`.
* The structure `first_order.language.quotient_structure s` is the resulting structure on
`quotient s`.

-/

namespace first_order
namespace language

variables (L : language) {M : Type*}
open_locale first_order
open Structure

/-- A prestructure is a first-order structure with a `setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class prestructure (s : setoid M) :=
(to_structure : L.Structure M)
(fun_equiv : ∀{n} {f : L.functions n} (x y : fin n → M),
  x ≈ y → fun_map f x ≈ fun_map f y)
(rel_equiv : ∀{n} {r : L.relations n} (x y : fin n → M) (h : x ≈ y),
  (rel_map r x = rel_map r y))

variables {L} {s : setoid M} [ps : L.prestructure s]

instance quotient_structure :
  L.Structure (quotient s) :=
{ fun_map := λ n f x, quotient.map (@fun_map L M ps.to_structure n f) prestructure.fun_equiv
    (quotient.fin_choice x),
  rel_map := λ n r x, quotient.lift (@rel_map L M ps.to_structure n r) prestructure.rel_equiv
    (quotient.fin_choice x) }

variables [s]
include s

lemma fun_map_quotient_mk {n : ℕ} (f : L.functions n) (x : fin n → M) :
  fun_map f (λ i, ⟦x i⟧) = ⟦@fun_map _ _ ps.to_structure _ f x⟧ :=
begin
  change quotient.map (@fun_map L M ps.to_structure n f) prestructure.fun_equiv
    (quotient.fin_choice _) = _,
  rw [quotient.fin_choice_eq, quotient.map_mk],
end

lemma rel_map_quotient_mk {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (λ i, ⟦x i⟧) = @rel_map _ _ ps.to_structure _ r x :=
begin
  change quotient.lift (@rel_map L M ps.to_structure n r) prestructure.rel_equiv
    (quotient.fin_choice _) = _,
  rw [quotient.fin_choice_eq, quotient.lift_mk],
end

lemma realize_term_quotient_mk {β : Type*} (x : β → M) (t : L.term β) :
  realize_term (λ i, ⟦x i⟧) t = ⟦@realize_term _ _ ps.to_structure _ x t⟧ :=
begin
  induction t with a1 a2 a3 a4 ih a6 a7 a8 a9 a0,
  { refl },
  simp only [ih, fun_map_quotient_mk, realize_term],
end

end language
end first_order
