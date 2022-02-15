/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.measure.measure_space

/-!
# Typeclasses for measurability of operations

In this file we define classes `has_measurable_mul` etc and prove dot-style lemmas
(`measurable.mul`, `ae_measurable.mul` etc). For binary operations we define two typeclasses:

- `has_measurable_mul` says that both left and right multiplication are measurable;
- `has_measurable_mul₂` says that `λ p : α × α, p.1 * p.2` is measurable,

and similarly for other binary operations. The reason for introducing these classes is that in case
of topological space `α` equipped with the Borel `σ`-algebra, instances for `has_measurable_mul₂`
etc require `α` to have a second countable topology.

We define separate classes for `has_measurable_div`/`has_measurable_sub`
because on some types (e.g., `ℕ`, `ℝ≥0∞`) division and/or subtraction are not defined as `a * b⁻¹` /
`a + (-b)`.

For instances relating, e.g., `has_continuous_mul` to `has_measurable_mul` see file
`measure_theory.borel_space`.

## Implementation notes

For the heuristics of `@[to_additive]` it is important that the type with a multiplication
(or another multiplicative operations) is the first (implicit) argument of all declarations.

## Tags

measurable function, arithmetic operator

## Todo

* Uniformize the treatment of `pow` and `smul`.
* Use `@[to_additive]` to send `has_measurable_pow` to `has_measurable_smul₂`.
* This might require changing the definition (swapping the arguments in the function that is
  in the conclusion of `measurable_smul`.)
-/

universes u v

open_locale big_operators pointwise
open measure_theory

/-!
### Binary operations: `(+)`, `(*)`, `(-)`, `(/)`
-/

/-- We say that a type `has_measurable_add` if `((+) c)` and `(+ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (+)` see `has_measurable_add₂`. -/
class has_measurable_add (M : Type*) [measurable_space M] [has_add M] : Prop :=
(measurable_const_add : ∀ c : M, measurable ((+) c))
(measurable_add_const : ∀ c : M, measurable (+ c))

/-- We say that a type `has_measurable_add` if `uncurry (+)` is a measurable functions.
For a typeclass assuming measurability of `((+) c)` and `(+ c)` see `has_measurable_add`. -/
class has_measurable_add₂ (M : Type*) [measurable_space M] [has_add M] : Prop :=
(measurable_add : measurable (λ p : M × M, p.1 + p.2))

export has_measurable_add₂ (measurable_add)
  has_measurable_add (measurable_const_add measurable_add_const)

/-- We say that a type `has_measurable_mul` if `((*) c)` and `(* c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (*)` see `has_measurable_mul₂`. -/
@[to_additive]
class has_measurable_mul (M : Type*) [measurable_space M] [has_mul M] : Prop :=
(measurable_const_mul : ∀ c : M, measurable ((*) c))
(measurable_mul_const : ∀ c : M, measurable (* c))

/-- We say that a type `has_measurable_mul` if `uncurry (*)` is a measurable functions.
For a typeclass assuming measurability of `((*) c)` and `(* c)` see `has_measurable_mul`. -/
@[to_additive has_measurable_add₂]
class has_measurable_mul₂ (M : Type*) [measurable_space M] [has_mul M] : Prop :=
(measurable_mul : measurable (λ p : M × M, p.1 * p.2))

export has_measurable_mul₂ (measurable_mul)
  has_measurable_mul (measurable_const_mul measurable_mul_const)

section mul

variables {M α : Type*} [measurable_space M] [has_mul M] {m : measurable_space α}
  {f g : α → M} {μ : measure α}

include m

@[measurability, to_additive]
lemma measurable.const_mul [has_measurable_mul M] (hf : measurable f) (c : M) :
  measurable (λ x, c * f x) :=
(measurable_const_mul c).comp hf

@[measurability, to_additive]
lemma ae_measurable.const_mul [has_measurable_mul M] (hf : ae_measurable f μ) (c : M) :
  ae_measurable (λ x, c * f x) μ :=
(has_measurable_mul.measurable_const_mul c).comp_ae_measurable hf

@[measurability, to_additive]
lemma measurable.mul_const [has_measurable_mul M] (hf : measurable f) (c : M) :
  measurable (λ x, f x * c) :=
(measurable_mul_const c).comp hf

@[measurability, to_additive]
lemma ae_measurable.mul_const [has_measurable_mul M] (hf : ae_measurable f μ) (c : M) :
  ae_measurable (λ x, f x * c) μ :=
(measurable_mul_const c).comp_ae_measurable hf

@[measurability, to_additive]
lemma measurable.mul' [has_measurable_mul₂ M] (hf : measurable f) (hg : measurable g) :
  measurable (f * g) :=
measurable_mul.comp (hf.prod_mk hg)

@[measurability, to_additive]
lemma measurable.mul [has_measurable_mul₂ M] (hf : measurable f) (hg : measurable g) :
  measurable (λ a, f a * g a) :=
measurable_mul.comp (hf.prod_mk hg)

@[measurability, to_additive]
lemma ae_measurable.mul' [has_measurable_mul₂ M] (hf : ae_measurable f μ)
  (hg : ae_measurable g μ) :
  ae_measurable (f * g) μ :=
measurable_mul.comp_ae_measurable (hf.prod_mk hg)

@[measurability, to_additive]
lemma ae_measurable.mul [has_measurable_mul₂ M] (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ a, f a * g a) μ :=
measurable_mul.comp_ae_measurable (hf.prod_mk hg)

omit m

@[to_additive]
instance pi.has_measurable_mul {ι : Type*} {α : ι → Type*} [∀ i, has_mul (α i)]
  [∀ i, measurable_space (α i)] [∀ i, has_measurable_mul (α i)] :
  has_measurable_mul (Π i, α i) :=
⟨λ g, measurable_pi_iff.mpr $ λ i, (measurable_const_mul (g i)).comp $ measurable_pi_apply i,
 λ g, measurable_pi_iff.mpr $ λ i, (measurable_mul_const (g i)).comp $ measurable_pi_apply i⟩

@[priority 100, to_additive]
instance has_measurable_mul₂.to_has_measurable_mul [has_measurable_mul₂ M] :
  has_measurable_mul M :=
⟨λ c, measurable_const.mul measurable_id, λ c, measurable_id.mul measurable_const⟩

attribute [measurability] measurable.add' measurable.add ae_measurable.add ae_measurable.add'
  measurable.const_add ae_measurable.const_add measurable.add_const ae_measurable.add_const


end mul

/-- This class assumes that the map `β × γ → β` given by `(x, y) ↦ x ^ y` is measurable. -/
class has_measurable_pow (β γ : Type*) [measurable_space β] [measurable_space γ] [has_pow β γ] :=
(measurable_pow : measurable (λ p : β × γ, p.1 ^ p.2))

export has_measurable_pow (measurable_pow)

instance has_measurable_mul.has_measurable_pow (M : Type*) [monoid M] [measurable_space M]
  [has_measurable_mul₂ M] : has_measurable_pow M ℕ :=
⟨begin
  haveI : measurable_singleton_class ℕ := ⟨λ _, trivial⟩,
  refine measurable_from_prod_encodable (λ n, _),
  induction n with n ih,
  { simp [pow_zero, measurable_one] },
  { simp only [pow_succ], exact measurable_id.mul ih }
end⟩

section pow

variables {β γ α : Type*} [measurable_space β] [measurable_space γ] [has_pow β γ]
  [has_measurable_pow β γ] {m : measurable_space α} {μ : measure α} {f : α → β} {g : α → γ}

include m

@[measurability]
lemma measurable.pow (hf : measurable f) (hg : measurable g) :
  measurable (λ x, f x ^ g x) :=
measurable_pow.comp (hf.prod_mk hg)

@[measurability]
lemma ae_measurable.pow (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x, f x ^ g x) μ :=
measurable_pow.comp_ae_measurable (hf.prod_mk hg)

@[measurability]
lemma measurable.pow_const (hf : measurable f) (c : γ) :
  measurable (λ x, f x ^ c) :=
hf.pow measurable_const

@[measurability]
lemma ae_measurable.pow_const (hf : ae_measurable f μ) (c : γ) :
  ae_measurable (λ x, f x ^ c) μ :=
hf.pow ae_measurable_const

@[measurability]
lemma measurable.const_pow (hg : measurable g) (c : β) :
  measurable (λ x, c ^ g x) :=
measurable_const.pow hg

@[measurability]
lemma ae_measurable.const_pow (hg : ae_measurable g μ) (c : β) :
  ae_measurable (λ x, c ^ g x) μ :=
ae_measurable_const.pow hg

omit m

end pow

/-- We say that a type `has_measurable_sub` if `(λ x, c - x)` and `(λ x, x - c)` are measurable
functions. For a typeclass assuming measurability of `uncurry (-)` see `has_measurable_sub₂`. -/
class has_measurable_sub (G : Type*) [measurable_space G] [has_sub G] : Prop :=
(measurable_const_sub : ∀ c : G, measurable (λ x, c - x))
(measurable_sub_const : ∀ c : G, measurable (λ x, x - c))

/-- We say that a type `has_measurable_sub` if `uncurry (-)` is a measurable functions.
For a typeclass assuming measurability of `((-) c)` and `(- c)` see `has_measurable_sub`. -/
class has_measurable_sub₂ (G : Type*) [measurable_space G] [has_sub G] : Prop :=
(measurable_sub : measurable (λ p : G × G, p.1 - p.2))

export has_measurable_sub₂ (measurable_sub)

/-- We say that a type `has_measurable_div` if `((/) c)` and `(/ c)` are measurable functions.
For a typeclass assuming measurability of `uncurry (/)` see `has_measurable_div₂`. -/
@[to_additive] class has_measurable_div (G₀: Type*) [measurable_space G₀] [has_div G₀] : Prop :=
(measurable_const_div : ∀ c : G₀, measurable ((/) c))
(measurable_div_const : ∀ c : G₀, measurable (/ c))

/-- We say that a type `has_measurable_div` if `uncurry (/)` is a measurable functions.
For a typeclass assuming measurability of `((/) c)` and `(/ c)` see `has_measurable_div`. -/
@[to_additive has_measurable_sub₂]
class has_measurable_div₂ (G₀: Type*) [measurable_space G₀] [has_div G₀] : Prop :=
(measurable_div : measurable (λ p : G₀× G₀, p.1 / p.2))

export has_measurable_div₂ (measurable_div)

section div

variables {G α : Type*} [measurable_space G] [has_div G] {m : measurable_space α} {f g : α → G}
  {μ : measure α}

include m

@[measurability, to_additive]
lemma measurable.const_div [has_measurable_div G] (hf : measurable f) (c : G) :
  measurable (λ x, c / f x) :=
(has_measurable_div.measurable_const_div c).comp hf

@[measurability, to_additive]
lemma ae_measurable.const_div [has_measurable_div G] (hf : ae_measurable f μ) (c : G) :
  ae_measurable (λ x, c / f x) μ :=
(has_measurable_div.measurable_const_div c).comp_ae_measurable hf

@[measurability, to_additive]
lemma measurable.div_const [has_measurable_div G] (hf : measurable f) (c : G) :
  measurable (λ x, f x / c) :=
(has_measurable_div.measurable_div_const c).comp hf

@[measurability, to_additive]
lemma ae_measurable.div_const [has_measurable_div G] (hf : ae_measurable f μ) (c : G) :
  ae_measurable (λ x, f x / c) μ :=
(has_measurable_div.measurable_div_const c).comp_ae_measurable hf

@[measurability, to_additive]
lemma measurable.div' [has_measurable_div₂ G] (hf : measurable f) (hg : measurable g) :
  measurable (f / g) :=
measurable_div.comp (hf.prod_mk hg)

@[measurability, to_additive]
lemma measurable.div [has_measurable_div₂ G] (hf : measurable f) (hg : measurable g) :
  measurable (λ a, f a / g a) :=
measurable_div.comp (hf.prod_mk hg)

@[measurability, to_additive]
lemma ae_measurable.div' [has_measurable_div₂ G] (hf : ae_measurable f μ)
  (hg : ae_measurable g μ) :
  ae_measurable (f / g) μ :=
measurable_div.comp_ae_measurable (hf.prod_mk hg)

@[measurability, to_additive]
lemma ae_measurable.div [has_measurable_div₂ G] (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ a, f a / g a) μ :=
measurable_div.comp_ae_measurable (hf.prod_mk hg)

attribute [measurability] measurable.sub measurable.sub' ae_measurable.sub ae_measurable.sub'
  measurable.const_sub ae_measurable.const_sub measurable.sub_const ae_measurable.sub_const

omit m

@[priority 100, to_additive]
instance has_measurable_div₂.to_has_measurable_div [has_measurable_div₂ G] :
  has_measurable_div G :=
⟨λ c, measurable_const.div measurable_id, λ c, measurable_id.div measurable_const⟩

@[measurability]
lemma measurable_set_eq_fun {m : measurable_space α} {E} [measurable_space E] [add_group E]
  [measurable_singleton_class E] [has_measurable_sub₂ E] {f g : α → E}
  (hf : measurable f) (hg : measurable g) :
  measurable_set {x | f x = g x} :=
begin
  suffices h_set_eq : {x : α | f x = g x} = {x | (f-g) x = (0 : E)},
  { rw h_set_eq,
    exact (hf.sub hg) measurable_set_eq, },
  ext,
  simp_rw [set.mem_set_of_eq, pi.sub_apply, sub_eq_zero],
end

lemma ae_eq_trim_of_measurable {α E} {m m0 : measurable_space α} {μ : measure α}
  [measurable_space E] [add_group E] [measurable_singleton_class E] [has_measurable_sub₂ E]
  (hm : m ≤ m0) {f g : α → E} (hf : @measurable _ _ m _ f) (hg : @measurable _ _ m _ g)
  (hfg : f =ᵐ[μ] g) :
  f =ᶠ[@measure.ae α m (μ.trim hm)] g :=
begin
  rwa [filter.eventually_eq, ae_iff, trim_measurable_set_eq hm _],
  exact (@measurable_set.compl α _ m (@measurable_set_eq_fun α m E _ _ _ _ _ _ hf hg)),
end

end div

/-- We say that a type `has_measurable_neg` if `x ↦ -x` is a measurable function. -/
class has_measurable_neg (G : Type*) [has_neg G] [measurable_space G] : Prop :=
(measurable_neg : measurable (has_neg.neg : G → G))

/-- We say that a type `has_measurable_inv` if `x ↦ x⁻¹` is a measurable function. -/
@[to_additive]
class has_measurable_inv (G : Type*) [has_inv G] [measurable_space G] : Prop :=
(measurable_inv : measurable (has_inv.inv : G → G))

export has_measurable_inv (measurable_inv) has_measurable_neg (measurable_neg)

@[priority 100, to_additive]
instance has_measurable_div_of_mul_inv (G : Type*) [measurable_space G]
  [div_inv_monoid G] [has_measurable_mul G] [has_measurable_inv G] :
  has_measurable_div G :=
{ measurable_const_div := λ c,
    by { convert (measurable_inv.const_mul c), ext1, apply div_eq_mul_inv },
  measurable_div_const := λ c,
    by { convert (measurable_id.mul_const c⁻¹), ext1, apply div_eq_mul_inv } }

section inv

variables {G α : Type*} [has_inv G] [measurable_space G] [has_measurable_inv G]
  {m : measurable_space α} {f : α → G} {μ : measure α}

include m

@[measurability, to_additive]
lemma measurable.inv (hf : measurable f) : measurable (λ x, (f x)⁻¹) := measurable_inv.comp hf

@[measurability, to_additive]
lemma ae_measurable.inv (hf : ae_measurable f μ) : ae_measurable (λ x, (f x)⁻¹) μ :=
measurable_inv.comp_ae_measurable hf

attribute [measurability] measurable.neg ae_measurable.neg

@[simp, to_additive] lemma measurable_inv_iff {G : Type*} [group G] [measurable_space G]
  [has_measurable_inv G] {f : α → G} : measurable (λ x, (f x)⁻¹) ↔ measurable f :=
⟨λ h, by simpa only [inv_inv] using h.inv, λ h, h.inv⟩

@[simp, to_additive] lemma ae_measurable_inv_iff {G : Type*} [group G] [measurable_space G]
  [has_measurable_inv G] {f : α → G} :
  ae_measurable (λ x, (f x)⁻¹) μ ↔ ae_measurable f μ :=
⟨λ h, by simpa only [inv_inv] using h.inv, λ h, h.inv⟩

@[simp] lemma measurable_inv_iff₀ {G₀ : Type*} [group_with_zero G₀]
  [measurable_space G₀] [has_measurable_inv G₀] {f : α → G₀} :
  measurable (λ x, (f x)⁻¹) ↔ measurable f :=
⟨λ h, by simpa only [inv_inv₀] using h.inv, λ h, h.inv⟩

@[simp] lemma ae_measurable_inv_iff₀ {G₀ : Type*} [group_with_zero G₀]
  [measurable_space G₀] [has_measurable_inv G₀] {f : α → G₀} :
  ae_measurable (λ x, (f x)⁻¹) μ ↔ ae_measurable f μ :=
⟨λ h, by simpa only [inv_inv₀] using h.inv, λ h, h.inv⟩

omit m

@[to_additive] lemma measurable_set.inv {s : set G} (hs : measurable_set s) : measurable_set s⁻¹ :=
measurable_inv hs

end inv

/- There is something extremely strange here: copy-pasting the proof of this lemma in the proof
of `has_measurable_zpow` fails, while `pp.all` does not show any difference in the goal.
Keep it as a separate lemmas as a workaround. -/
private lemma has_measurable_zpow_aux (G : Type u) [div_inv_monoid G] [measurable_space G]
  [has_measurable_mul₂ G] [has_measurable_inv G] (k : ℕ) :
  measurable (λ (x : G), x ^(-[1+ k])) :=
begin
  simp_rw [zpow_neg_succ_of_nat],
  exact (measurable_id.pow_const (k + 1)).inv
end

instance has_measurable_zpow (G : Type u) [div_inv_monoid G] [measurable_space G]
  [has_measurable_mul₂ G] [has_measurable_inv G] :
  has_measurable_pow G ℤ :=
begin
  letI : measurable_singleton_class ℤ := ⟨λ _, trivial⟩,
  constructor,
  refine measurable_from_prod_encodable (λ n, _),
  dsimp,
  apply int.cases_on n,
  { simpa using measurable_id.pow_const },
  { exact has_measurable_zpow_aux G }
end

@[priority 100, to_additive]
instance has_measurable_div₂_of_mul_inv (G : Type*) [measurable_space G]
  [div_inv_monoid G] [has_measurable_mul₂ G] [has_measurable_inv G] :
  has_measurable_div₂ G :=
⟨by { simp only [div_eq_mul_inv], exact measurable_fst.mul measurable_snd.inv }⟩

/-- We say that the action of `M` on `α` `has_measurable_vadd` if for each `c` the map `x ↦ c +ᵥ x`
is a measurable function and for each `x` the map `c ↦ c +ᵥ x` is a measurable function. -/
class has_measurable_vadd (M α : Type*) [has_vadd M α] [measurable_space M] [measurable_space α] :
  Prop :=
(measurable_const_vadd : ∀ c : M, measurable ((+ᵥ) c : α → α))
(measurable_vadd_const : ∀ x : α, measurable (λ c : M, c +ᵥ x))

/-- We say that the action of `M` on `α` `has_measurable_smul` if for each `c` the map `x ↦ c • x`
is a measurable function and for each `x` the map `c ↦ c • x` is a measurable function. -/
@[to_additive]
class has_measurable_smul (M α : Type*) [has_scalar M α] [measurable_space M] [measurable_space α] :
  Prop :=
(measurable_const_smul : ∀ c : M, measurable ((•) c : α → α))
(measurable_smul_const : ∀ x : α, measurable (λ c : M, c • x))

/-- We say that the action of `M` on `α` `has_measurable_vadd₂` if the map
`(c, x) ↦ c +ᵥ x` is a measurable function. -/
class has_measurable_vadd₂ (M α : Type*) [has_vadd M α] [measurable_space M]
  [measurable_space α] : Prop :=
(measurable_vadd : measurable (function.uncurry (+ᵥ) : M × α → α))

/-- We say that the action of `M` on `α` `has_measurable_smul₂` if the map
`(c, x) ↦ c • x` is a measurable function. -/
@[to_additive has_measurable_vadd₂]
class has_measurable_smul₂ (M α : Type*) [has_scalar M α] [measurable_space M]
  [measurable_space α] : Prop :=
(measurable_smul : measurable (function.uncurry (•) : M × α → α))

export has_measurable_smul (measurable_const_smul measurable_smul_const)
  has_measurable_smul₂ (measurable_smul)
export has_measurable_vadd (measurable_const_vadd measurable_vadd_const)
  has_measurable_vadd₂ (measurable_vadd)

@[to_additive]
instance has_measurable_smul_of_mul (M : Type*) [has_mul M] [measurable_space M]
  [has_measurable_mul M] :
  has_measurable_smul M M :=
⟨measurable_id.const_mul, measurable_id.mul_const⟩

@[to_additive]
instance has_measurable_smul₂_of_mul (M : Type*) [has_mul M] [measurable_space M]
  [has_measurable_mul₂ M] :
  has_measurable_smul₂ M M :=
⟨measurable_mul⟩

@[to_additive] instance submonoid.has_measurable_smul {M α} [measurable_space M]
  [measurable_space α] [monoid M] [mul_action M α] [has_measurable_smul M α] (s : submonoid M) :
  has_measurable_smul s α :=
⟨λ c, by simpa only using measurable_const_smul (c : M),
  λ x, (measurable_smul_const x : measurable (λ c : M, c • x)).comp measurable_subtype_coe⟩

@[to_additive] instance subgroup.has_measurable_smul {G α} [measurable_space G]
  [measurable_space α] [group G] [mul_action G α] [has_measurable_smul G α] (s : subgroup G) :
  has_measurable_smul s α :=
s.to_submonoid.has_measurable_smul

section smul

variables {M β α : Type*} [measurable_space M] [measurable_space β] [has_scalar M β]
  {m : measurable_space α} {f : α → M} {g : α → β}

include m

@[measurability, to_additive]
lemma measurable.smul [has_measurable_smul₂ M β] (hf : measurable f) (hg : measurable g) :
  measurable (λ x, f x • g x) :=
measurable_smul.comp (hf.prod_mk hg)

@[measurability, to_additive]
lemma ae_measurable.smul [has_measurable_smul₂ M β]
  {μ : measure α} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x, f x • g x) μ :=
has_measurable_smul₂.measurable_smul.comp_ae_measurable (hf.prod_mk hg)

omit m

@[priority 100, to_additive]
instance has_measurable_smul₂.to_has_measurable_smul [has_measurable_smul₂ M β] :
  has_measurable_smul M β :=
⟨λ c, measurable_const.smul measurable_id, λ y, measurable_id.smul measurable_const⟩

include m

variables [has_measurable_smul M β] {μ : measure α}

@[measurability, to_additive]
lemma measurable.smul_const (hf : measurable f) (y : β) :
  measurable (λ x, f x • y) :=
(has_measurable_smul.measurable_smul_const y).comp hf

@[measurability, to_additive]
lemma ae_measurable.smul_const (hf : ae_measurable f μ) (y : β) :
  ae_measurable (λ x, f x • y) μ :=
(has_measurable_smul.measurable_smul_const y).comp_ae_measurable hf

@[measurability, to_additive]
lemma measurable.const_smul' (hg : measurable g) (c : M) :
  measurable (λ x, c • g x) :=
(has_measurable_smul.measurable_const_smul c).comp hg

@[measurability, to_additive]
lemma measurable.const_smul (hg : measurable g) (c : M) :
  measurable (c • g) :=
hg.const_smul' c

@[measurability, to_additive]
lemma ae_measurable.const_smul' (hg : ae_measurable g μ) (c : M) :
  ae_measurable (λ x, c • g x) μ :=
(has_measurable_smul.measurable_const_smul c).comp_ae_measurable hg

@[measurability, to_additive]
lemma ae_measurable.const_smul (hf : ae_measurable g μ) (c : M) :
  ae_measurable (c • g) μ :=
hf.const_smul' c

omit m

end smul

section mul_action

variables {M β α : Type*} [measurable_space M] [measurable_space β] [monoid M] [mul_action M β]
  [has_measurable_smul M β] [measurable_space α] {f : α → β} {μ : measure α}

variables {G : Type*} [group G] [measurable_space G] [mul_action G β]
  [has_measurable_smul G β]

@[to_additive]
lemma measurable_const_smul_iff (c : G) :
  measurable (λ x, c • f x) ↔ measurable f :=
⟨λ h, by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, λ h, h.const_smul c⟩

@[to_additive]
lemma ae_measurable_const_smul_iff (c : G) :
  ae_measurable (λ x, c • f x) μ ↔ ae_measurable f μ :=
⟨λ h, by simpa only [inv_smul_smul] using h.const_smul' c⁻¹, λ h, h.const_smul c⟩

@[to_additive]
instance : measurable_space Mˣ := measurable_space.comap (coe : Mˣ → M) ‹_›

@[to_additive]
instance units.has_measurable_smul : has_measurable_smul Mˣ β :=
{ measurable_const_smul := λ c, (measurable_const_smul (c : M) : _),
  measurable_smul_const := λ x,
    (measurable_smul_const x : measurable (λ c : M, c • x)).comp measurable_space.le_map_comap, }

@[to_additive]
lemma is_unit.measurable_const_smul_iff {c : M} (hc : is_unit c) :
  measurable (λ x, c • f x) ↔ measurable f :=
let ⟨u, hu⟩ := hc in hu ▸ measurable_const_smul_iff u

@[to_additive]
lemma is_unit.ae_measurable_const_smul_iff {c : M} (hc : is_unit c) :
  ae_measurable (λ x, c • f x) μ ↔ ae_measurable f μ :=
let ⟨u, hu⟩ := hc in hu ▸ ae_measurable_const_smul_iff u

variables {G₀ : Type*} [group_with_zero G₀] [measurable_space G₀] [mul_action G₀ β]
  [has_measurable_smul G₀ β]

lemma measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
  measurable (λ x, c • f x) ↔ measurable f :=
(is_unit.mk0 c hc).measurable_const_smul_iff

lemma ae_measurable_const_smul_iff₀ {c : G₀} (hc : c ≠ 0) :
  ae_measurable (λ x, c • f x) μ ↔ ae_measurable f μ :=
(is_unit.mk0 c hc).ae_measurable_const_smul_iff

end mul_action

/-!
### Opposite monoid
-/

section opposite
open mul_opposite

@[to_additive]
instance {α : Type*} [h : measurable_space α] : measurable_space αᵐᵒᵖ := measurable_space.map op h

@[to_additive]
lemma measurable_mul_op {α : Type*} [measurable_space α] : measurable (op : α → αᵐᵒᵖ) := λ s, id

@[to_additive]
lemma measurable_mul_unop {α : Type*} [measurable_space α] : measurable (unop : αᵐᵒᵖ → α) := λ s, id

@[to_additive]
instance {M : Type*} [has_mul M] [measurable_space M] [has_measurable_mul M] :
  has_measurable_mul Mᵐᵒᵖ :=
⟨λ c, measurable_mul_op.comp (measurable_mul_unop.mul_const _),
  λ c, measurable_mul_op.comp (measurable_mul_unop.const_mul _)⟩

@[to_additive]
instance {M : Type*} [has_mul M] [measurable_space M] [has_measurable_mul₂ M] :
  has_measurable_mul₂ Mᵐᵒᵖ :=
⟨measurable_mul_op.comp ((measurable_mul_unop.comp measurable_snd).mul
  (measurable_mul_unop.comp measurable_fst))⟩

@[to_additive]
instance has_measurable_smul_opposite_of_mul {M : Type*} [has_mul M] [measurable_space M]
  [has_measurable_mul M] : has_measurable_smul Mᵐᵒᵖ M :=
⟨λ c, measurable_mul_const (unop c), λ x, measurable_mul_unop.const_mul x⟩

@[to_additive]
instance has_measurable_smul₂_opposite_of_mul {M : Type*} [has_mul M] [measurable_space M]
  [has_measurable_mul₂ M] : has_measurable_smul₂ Mᵐᵒᵖ M :=
⟨measurable_snd.mul (measurable_mul_unop.comp measurable_fst)⟩

end opposite

/-!
### Big operators: `∏` and `∑`
-/

section monoid
variables {M α : Type*} [monoid M] [measurable_space M] [has_measurable_mul₂ M]
  {m : measurable_space α} {μ : measure α}

include m

@[measurability, to_additive]
lemma list.measurable_prod' (l : list (α → M)) (hl : ∀ f ∈ l, measurable f) :
  measurable l.prod :=
begin
  induction l with f l ihl, { exact measurable_one },
  rw [list.forall_mem_cons] at hl,
  rw [list.prod_cons],
  exact hl.1.mul (ihl hl.2)
end

@[measurability, to_additive]
lemma list.ae_measurable_prod' (l : list (α → M))
  (hl : ∀ f ∈ l, ae_measurable f μ) : ae_measurable l.prod μ :=
begin
  induction l with f l ihl, { exact ae_measurable_one },
  rw [list.forall_mem_cons] at hl,
  rw [list.prod_cons],
  exact hl.1.mul (ihl hl.2)
end

@[measurability, to_additive]
lemma list.measurable_prod (l : list (α → M)) (hl : ∀ f ∈ l, measurable f) :
  measurable (λ x, (l.map (λ f : α → M, f x)).prod) :=
by simpa only [← pi.list_prod_apply] using l.measurable_prod' hl

@[measurability, to_additive]
lemma list.ae_measurable_prod (l : list (α → M)) (hl : ∀ f ∈ l, ae_measurable f μ) :
  ae_measurable (λ x, (l.map (λ f : α → M, f x)).prod) μ :=
by simpa only [← pi.list_prod_apply] using l.ae_measurable_prod' hl

omit m

end monoid

section comm_monoid
variables {M ι α : Type*} [comm_monoid M] [measurable_space M] [has_measurable_mul₂ M]
  {m : measurable_space α} {μ : measure α} {f : ι → α → M}

include m

@[measurability, to_additive]
lemma multiset.measurable_prod' (l : multiset (α → M)) (hl : ∀ f ∈ l, measurable f) :
  measurable l.prod :=
by { rcases l with ⟨l⟩, simpa using l.measurable_prod' (by simpa using hl) }

@[measurability, to_additive]
lemma multiset.ae_measurable_prod' (l : multiset (α → M))
  (hl : ∀ f ∈ l, ae_measurable f μ) : ae_measurable l.prod μ :=
by { rcases l with ⟨l⟩, simpa using l.ae_measurable_prod' (by simpa using hl) }

@[measurability, to_additive]
lemma multiset.measurable_prod (s : multiset (α → M)) (hs : ∀ f ∈ s, measurable f) :
  measurable (λ x, (s.map (λ f : α → M, f x)).prod) :=
by simpa only [← pi.multiset_prod_apply] using s.measurable_prod' hs

@[measurability, to_additive]
lemma multiset.ae_measurable_prod (s : multiset (α → M))
  (hs : ∀ f ∈ s, ae_measurable f μ) : ae_measurable (λ x, (s.map (λ f : α → M, f x)).prod) μ :=
by simpa only [← pi.multiset_prod_apply] using s.ae_measurable_prod' hs

@[measurability, to_additive]
lemma finset.measurable_prod' (s : finset ι) (hf : ∀i ∈ s, measurable (f i)) :
  measurable (∏ i in s, f i) :=
finset.prod_induction _ _ (λ _ _, measurable.mul) (@measurable_one M _ _ _ _) hf

@[measurability, to_additive]
lemma finset.measurable_prod (s : finset ι) (hf : ∀i ∈ s, measurable (f i)) :
  measurable (λ a, ∏ i in s, f i a) :=
by simpa only [← finset.prod_apply] using s.measurable_prod' hf

@[measurability, to_additive]
lemma finset.ae_measurable_prod' (s : finset ι) (hf : ∀i ∈ s, ae_measurable (f i) μ) :
  ae_measurable (∏ i in s, f i) μ :=
multiset.ae_measurable_prod' _ $
  λ g hg, let ⟨i, hi, hg⟩ := multiset.mem_map.1 hg in (hg ▸ hf _ hi)

@[measurability, to_additive]
lemma finset.ae_measurable_prod (s : finset ι) (hf : ∀i ∈ s, ae_measurable (f i) μ) :
  ae_measurable (λ a, ∏ i in s, f i a) μ :=
by simpa only [← finset.prod_apply] using s.ae_measurable_prod' hf

omit m

end comm_monoid
