/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.monoid
import group_theory.group_action.prod
import group_theory.group_action.basic
import topology.homeomorph
import topology.algebra.const_mul_action

/-!
# Continuous monoid action

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M α` if `M` acts on
`α` and the map `(c, x) ↦ c • x` is continuous on `M × α`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M α` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × α`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `α` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `α`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `α`
  is a homeomorphism of `α`.
* `units.has_continuous_smul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/

open_locale topological_space pointwise
open filter

/-- Class `has_continuous_smul M α` says that the scalar multiplication `(•) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class has_continuous_smul (M α : Type*) [has_scalar M α]
  [topological_space M] [topological_space α] : Prop :=
(continuous_smul : continuous (λp : M × α, p.1 • p.2))

export has_continuous_smul (continuous_smul)

/-- Class `has_continuous_vadd M α` says that the additive action `(+ᵥ) : M → α → α`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class has_continuous_vadd (M α : Type*) [has_vadd M α]
  [topological_space M] [topological_space α] : Prop :=
(continuous_vadd : continuous (λp : M × α, p.1 +ᵥ p.2))

export has_continuous_vadd (continuous_vadd)

attribute [to_additive] has_continuous_smul

variables {M α β : Type*}
variables [topological_space M] [topological_space α]

section has_scalar
variables [has_scalar M α] [has_continuous_smul M α]

@[priority 100, to_additive] instance has_continuous_smul.has_continuous_const_smul :
  has_continuous_const_smul M α :=
{ continuous_const_smul := λ _, continuous_smul.comp (continuous_const.prod_mk continuous_id) }

@[to_additive]
lemma filter.tendsto.smul {f : β → M} {g : β → α} {l : filter β} {c : M} {a : α}
  (hf : tendsto f l (𝓝 c)) (hg : tendsto g l (𝓝 a)) :
  tendsto (λ x, f x • g x) l (𝓝 $ c • a) :=
(continuous_smul.tendsto _).comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma filter.tendsto.smul_const {f : β → M} {l : filter β} {c : M}
  (hf : tendsto f l (𝓝 c)) (a : α) :
  tendsto (λ x, (f x) • a) l (𝓝 (c • a)) :=
hf.smul tendsto_const_nhds

variables [topological_space β] {f : β → M} {g : β → α} {b : β} {s : set β}

@[to_additive]
lemma continuous_within_at.smul (hf : continuous_within_at f s b)
  (hg : continuous_within_at g s b) :
  continuous_within_at (λ x, f x • g x) s b :=
hf.smul hg

@[to_additive]
lemma continuous_at.smul (hf : continuous_at f b) (hg : continuous_at g b) :
  continuous_at (λ x, f x • g x) b :=
hf.smul hg

@[to_additive]
lemma continuous_on.smul (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ x, f x • g x) s :=
λ x hx, (hf x hx).smul (hg x hx)

@[continuity, to_additive]
lemma continuous.smul (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x • g x) :=
continuous_smul.comp (hf.prod_mk hg)

/-- If a scalar is central, then its right action is continuous when its left action is. -/
instance has_continuous_smul.op [has_scalar Mᵐᵒᵖ α] [is_central_scalar M α] :
  has_continuous_smul Mᵐᵒᵖ α :=
⟨ suffices continuous (λ p : M × α, mul_opposite.op p.fst • p.snd),
  from this.comp (mul_opposite.continuous_unop.prod_map continuous_id),
  by simpa only [op_smul_eq_smul] using (continuous_smul : continuous (λ p : M × α, _)) ⟩

end has_scalar

section monoid
variables [monoid M] [mul_action M α] [has_continuous_smul M α]

@[to_additive] instance units.has_continuous_smul : has_continuous_smul Mˣ α :=
{ continuous_smul :=
    show continuous ((λ p : M × α, p.fst • p.snd) ∘ (λ p : Mˣ × α, (p.1, p.2))),
    from continuous_smul.comp ((units.continuous_coe.comp continuous_fst).prod_mk continuous_snd) }

end monoid

@[to_additive]
instance has_continuous_mul.has_continuous_smul {M : Type*} [monoid M]
  [topological_space M] [has_continuous_mul M] :
  has_continuous_smul M M :=
⟨continuous_mul⟩

@[to_additive]
instance [topological_space β] [has_scalar M α] [has_scalar M β] [has_continuous_smul M α]
  [has_continuous_smul M β] :
  has_continuous_smul M (α × β) :=
⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
  (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type*} {γ : ι → Type*}
  [∀ i, topological_space (γ i)] [Π i, has_scalar M (γ i)] [∀ i, has_continuous_smul M (γ i)] :
  has_continuous_smul M (Π i, γ i) :=
⟨continuous_pi $ λ i,
  (continuous_fst.smul continuous_snd).comp $
    continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

section lattice_ops

variables {ι : Type*} [has_scalar M β]
  {ts : set (topological_space β)} (h : Π t ∈ ts, @has_continuous_smul M β _ _ t)
  {ts' : ι → topological_space β} (h' : Π i, @has_continuous_smul M β _ _ (ts' i))
  {t₁ t₂ : topological_space β} [h₁ : @has_continuous_smul M β _ _ t₁]
  [h₂ : @has_continuous_smul M β _ _ t₂]

include h

@[to_additive] lemma has_continuous_smul_Inf :
  @has_continuous_smul M β _ _ (Inf ts) :=
{ continuous_smul :=
  begin
    rw ← @Inf_singleton _ _ ‹topological_space M›,
    exact continuous_Inf_rng (λ t ht, continuous_Inf_dom₂ (eq.refl _) ht
      (@has_continuous_smul.continuous_smul _ _ _ _ t (h t ht)))
  end }

omit h

include h'

@[to_additive] lemma has_continuous_smul_infi :
  @has_continuous_smul M β _ _ (⨅ i, ts' i) :=
by {rw ← Inf_range, exact has_continuous_smul_Inf (set.forall_range_iff.mpr h')}

omit h'

include h₁ h₂

@[to_additive] lemma has_continuous_smul_inf :
  @has_continuous_smul M β _ _ (t₁ ⊓ t₂) :=
by {rw inf_eq_infi, refine has_continuous_smul_infi (λ b, _), cases b; assumption}

omit h₁ h₂

end lattice_ops
