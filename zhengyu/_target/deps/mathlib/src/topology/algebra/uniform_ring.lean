/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import topology.algebra.group_completion
import topology.algebra.ring

/-!
# Completion of topological rings:

This files endows the completion of a topological ring with a ring structure.
More precisely the instance `uniform_space.completion.ring` builds a ring structure
on the completion of a ring endowed with a compatible uniform structure in the sense of
`uniform_add_group`. There is also a commutative version when the original ring is commutative.

The last part of the file builds a ring structure on the biggest separated quotient of a ring.

## Main declarations:

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous ring morphisms.

* `uniform_space.completion.extension_hom`: extends a continuous ring morphism from `R`
  to a complete separated group `S` to `completion R`.
* `uniform_space.completion.map_ring_hom` : promotes a continuous ring morphism
  from `R` to `S` into a continuous ring morphism from `completion R` to `completion S`.
-/
open classical set filter topological_space add_comm_group
open_locale classical
noncomputable theory
universes u

namespace uniform_space.completion
open dense_inducing uniform_space function
variables (α : Type*) [ring α] [uniform_space α]

instance : has_one (completion α) := ⟨(1:α)⟩

instance : has_mul (completion α) :=
⟨curry $ (dense_inducing_coe.prod dense_inducing_coe).extend (coe ∘ uncurry (*))⟩

@[norm_cast] lemma coe_one : ((1 : α) : completion α) = 1 := rfl

variables {α} [topological_ring α]

@[norm_cast]
lemma coe_mul (a b : α) : ((a * b : α) : completion α) = a * b :=
((dense_inducing_coe.prod dense_inducing_coe).extend_eq
  ((continuous_coe α).comp (@continuous_mul α _ _ _)) (a, b)).symm

variables [uniform_add_group α]

lemma continuous_mul : continuous (λ p : completion α × completion α, p.1 * p.2) :=
begin
  let m := (add_monoid_hom.mul : α →+ α →+ α).compr₂ to_compl,
  have : continuous (λ p : α × α, m p.1 p.2),
  from (continuous_coe α).comp continuous_mul,
  have di : dense_inducing (to_compl : α → completion α),
  from dense_inducing_coe,
  convert di.extend_Z_bilin di this,
  ext ⟨x, y⟩,
  refl
end

lemma continuous.mul {β : Type*} [topological_space β] {f g : β → completion α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, f b * g b) :=
continuous_mul.comp (hf.prod_mk hg : _)

instance : ring (completion α) :=
{ one_mul       := assume a, completion.induction_on a
    (is_closed_eq (continuous.mul continuous_const continuous_id) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, one_mul]),
  mul_one       := assume a, completion.induction_on a
    (is_closed_eq (continuous.mul continuous_id continuous_const) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, mul_one]),
  mul_assoc     := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous.mul (continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
        (continuous_snd.comp continuous_snd))
      (continuous.mul continuous_fst
        (continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]),
  left_distrib  := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous.mul continuous_fst (continuous.add
        (continuous_fst.comp continuous_snd)
        (continuous_snd.comp continuous_snd)))
      (continuous.add
        (continuous.mul continuous_fst (continuous_fst.comp continuous_snd))
        (continuous.mul continuous_fst (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, mul_add]),
  right_distrib := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous.mul (continuous.add continuous_fst
        (continuous_fst.comp continuous_snd)) (continuous_snd.comp continuous_snd))
      (continuous.add
        (continuous.mul continuous_fst (continuous_snd.comp continuous_snd))
        (continuous.mul (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, add_mul]),
  ..completion.add_comm_group, ..completion.has_mul α, ..completion.has_one α }

/-- The map from a uniform ring to its completion, as a ring homomorphism. -/
def coe_ring_hom : α →+* completion α :=
⟨coe, coe_one α, assume a b, coe_mul a b, coe_zero, assume a b, coe_add a b⟩

lemma continuous_coe_ring_hom : continuous (coe_ring_hom : α → completion α) :=
continuous_coe α

variables {β : Type u} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
          (f : α →+* β) (hf : continuous f)

/-- The completion extension as a ring morphism. -/
def extension_hom [complete_space β] [separated_space β] :
  completion α →+* β :=
have hf' : continuous (f : α →+ β), from hf, -- helping the elaborator
have hf : uniform_continuous f, from uniform_continuous_add_monoid_hom_of_continuous hf',
{ to_fun := completion.extension f,
  map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero],
  map_add' := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_extension.comp continuous_add)
      ((continuous_extension.comp continuous_fst).add
                      (continuous_extension.comp continuous_snd)))
    (assume a b,
      by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf,
             f.map_add]),
  map_one' := by rw [← coe_one, extension_coe hf, f.map_one],
  map_mul' := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_extension.comp continuous_mul)
      ((continuous_extension.comp continuous_fst).mul (continuous_extension.comp continuous_snd)))
    (assume a b,
      by rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, f.map_mul]) }

instance top_ring_compl : topological_ring (completion α) :=
{ continuous_add := continuous_add,
  continuous_mul := continuous_mul }

/-- The completion map as a ring morphism. -/
def map_ring_hom (hf : continuous f) : completion α →+* completion β :=
extension_hom (coe_ring_hom.comp f) (continuous_coe_ring_hom.comp  hf)

variables (R : Type*) [comm_ring R] [uniform_space R] [uniform_add_group R] [topological_ring R]

instance : comm_ring (completion R) :=
{ mul_comm := assume a b, completion.induction_on₂ a b
      (is_closed_eq (continuous_fst.mul continuous_snd)
                    (continuous_snd.mul continuous_fst))
      (assume a b, by rw [← coe_mul, ← coe_mul, mul_comm]),
 ..completion.ring }

end uniform_space.completion


namespace uniform_space
variables {α : Type*}
lemma ring_sep_rel (α) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  separation_setoid α = submodule.quotient_rel (ideal.closure ⊥) :=
setoid.ext $ assume x y, add_group_separation_rel x y

lemma ring_sep_quot
  (α : Type u) [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) = (α ⧸ (⊥ : ideal α).closure) :=
by rw [@ring_sep_rel α r]; refl

/-- Given a topological ring `α` equipped with a uniform structure that makes subtraction uniformly
continuous, get an equivalence between the separated quotient of `α` and the quotient ring
corresponding to the closure of zero. -/
def sep_quot_equiv_ring_quot (α)
  [r : comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  quotient (separation_setoid α) ≃ (α ⧸ (⊥ : ideal α).closure) :=
quotient.congr_right $ assume x y, add_group_separation_rel x y

/- TODO: use a form of transport a.k.a. lift definition a.k.a. transfer -/
instance comm_ring [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  comm_ring (quotient (separation_setoid α)) :=
by rw ring_sep_quot α; apply_instance

instance topological_ring
  [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] :
  topological_ring (quotient (separation_setoid α)) :=
begin
  convert topological_ring_quotient (⊥ : ideal α).closure; try {apply ring_sep_rel},
  simp [uniform_space.comm_ring]
end

end uniform_space
