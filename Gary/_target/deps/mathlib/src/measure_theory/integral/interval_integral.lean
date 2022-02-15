/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Patrick Massot, Sébastien Gouëzel
-/
import analysis.normed_space.dual
import data.set.intervals.disjoint
import measure_theory.measure.haar_lebesgue
import analysis.calculus.extend_deriv
import measure_theory.integral.set_integral
import measure_theory.integral.vitali_caratheodory

/-!
# Integral over an interval

In this file we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ` if `a ≤ b` and
`-∫ x in Ioc b a, f x ∂μ` if `b ≤ a`. We prove a few simple properties and several versions of the
[fundamental theorem of calculus](https://en.wikipedia.org/wiki/Fundamental_theorem_of_calculus).

Recall that its first version states that the function `(u, v) ↦ ∫ x in u..v, f x` has derivative
`(δu, δv) ↦ δv • f b - δu • f a` at `(a, b)` provided that `f` is continuous at `a` and `b`,
and its second version states that, if `f` has an integrable derivative on `[a, b]`, then
`∫ x in a..b, f' x = f b - f a`.

## Main statements

### FTC-1 for Lebesgue measure

We prove several versions of FTC-1, all in the `interval_integral` namespace. Many of them follow
the naming scheme `integral_has(_strict?)_(f?)deriv(_within?)_at(_of_tendsto_ae?)(_right|_left?)`.
They formulate FTC in terms of `has(_strict?)_(f?)deriv(_within?)_at`.
Let us explain the meaning of each part of the name:

* `_strict` means that the theorem is about strict differentiability;
* `f` means that the theorem is about differentiability in both endpoints; incompatible with
  `_right|_left`;
* `_within` means that the theorem is about one-sided derivatives, see below for details;
* `_of_tendsto_ae` means that instead of continuity the theorem assumes that `f` has a finite limit
  almost surely as `x` tends to `a` and/or `b`;
* `_right` or `_left` mean that the theorem is about differentiability in the right (resp., left)
  endpoint.

We also reformulate these theorems in terms of `(f?)deriv(_within?)`. These theorems are named
`(f?)deriv(_within?)_integral(_of_tendsto_ae?)(_right|_left?)` with the same meaning of parts of the
name.

### One-sided derivatives

Theorem `integral_has_fderiv_within_at_of_tendsto_ae` states that `(u, v) ↦ ∫ x in u..v, f x` has a
derivative `(δu, δv) ↦ δv • cb - δu • ca` within the set `s × t` at `(a, b)` provided that `f` tends
to `ca` (resp., `cb`) almost surely at `la` (resp., `lb`), where possible values of `s`, `t`, and
corresponding filters `la`, `lb` are given in the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |

We use a typeclass `FTC_filter` to make Lean automatically find `la`/`lb` based on `s`/`t`. This way
we can formulate one theorem instead of `16` (or `8` if we leave only non-trivial ones not covered
by `integral_has_deriv_within_at_of_tendsto_ae_(left|right)` and
`integral_has_fderiv_at_of_tendsto_ae`). Similarly,
`integral_has_deriv_within_at_of_tendsto_ae_right` works for both one-sided derivatives using the
same typeclass to find an appropriate filter.

### FTC for a locally finite measure

Before proving FTC for the Lebesgue measure, we prove a few statements that can be seen as FTC for
any measure. The most general of them,
`measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae`, states the following. Let `(la, la')`
be an `FTC_filter` pair of filters around `a` (i.e., `FTC_filter a la la'`) and let `(lb, lb')` be
an `FTC_filter` pair of filters around `b`. If `f` has finite limits `ca` and `cb` almost surely at
`la'` and `lb'`, respectively, then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)` as `ua` and `va` tend to `la` while
`ub` and `vb` tend to `lb`.

### FTC-2 and corollaries

We use FTC-1 to prove several versions of FTC-2 for the Lebesgue measure, using a similar naming
scheme as for the versions of FTC-1. They include:
* `interval_integral.integral_eq_sub_of_has_deriv_right_of_le` - most general version, for functions
  with a right derivative
* `interval_integral.integral_eq_sub_of_has_deriv_at'` - version for functions with a derivative on
  an open set
* `interval_integral.integral_deriv_eq_sub'` - version that is easiest to use when computing the
  integral of a specific function

We then derive additional integration techniques from FTC-2:
* `interval_integral.integral_mul_deriv_eq_deriv_mul` - integration by parts
* `interval_integral.integral_comp_mul_deriv''` - integration by substitution

Many applications of these theorems can be found in the file `analysis.special_functions.integrals`.

Note that the assumptions of FTC-2 are formulated in the form that `f'` is integrable. To use it in
a context with the stronger assumption that `f'` is continuous, one can use
`continuous_on.interval_integrable` or `continuous_on.integrable_on_Icc` or
`continuous_on.integrable_on_interval`.

## Implementation notes

### Avoiding `if`, `min`, and `max`

In order to avoid `if`s in the definition, we define `interval_integrable f μ a b` as
`integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ`. For any `a`, `b` one of these
intervals is empty and the other coincides with `set.interval_oc a b = set.Ioc (min a b) (max a b)`.

Similarly, we define `∫ x in a..b, f x ∂μ` to be `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`.
Again, for any `a`, `b` one of these integrals is zero, and the other gives the expected result.

This way some properties can be translated from integrals over sets without dealing with
the cases `a ≤ b` and `b ≤ a` separately.

### Choice of the interval

We use integral over `set.interval_oc a b = set.Ioc (min a b) (max a b)` instead of one of the other
three possible intervals with the same endpoints for two reasons:

* this way `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ` holds whenever
  `f` is integrable on each interval; in particular, it works even if the measure `μ` has an atom
  at `b`; this rules out `set.Ioo` and `set.Icc` intervals;
* with this definition for a probability measure `μ`, the integral `∫ x in a..b, 1 ∂μ` equals
  the difference $F_μ(b)-F_μ(a)$, where $F_μ(a)=μ(-∞, a]$ is the
  [cumulative distribution function](https://en.wikipedia.org/wiki/Cumulative_distribution_function)
  of `μ`.

### `FTC_filter` class

As explained above, many theorems in this file rely on the typeclass
`FTC_filter (a : α) (l l' : filter α)` to avoid code duplication. This typeclass combines four
assumptions:

- `pure a ≤ l`;
- `l' ≤ 𝓝 a`;
- `l'` has a basis of measurable sets;
- if `u n` and `v n` tend to `l`, then for any `s ∈ l'`, `Ioc (u n) (v n)` is eventually included
  in `s`.

This typeclass has the following “real” instances: `(a, pure a, ⊥)`, `(a, 𝓝[≥] a, 𝓝[>] a)`,
`(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`.
Furthermore, we have the following instances that are equal to the previously mentioned instances:
`(a, 𝓝[{a}] a, ⊥)` and `(a, 𝓝[univ] a, 𝓝[univ] a)`.
While the difference between `Ici a` and `Ioi a` doesn't matter for theorems about Lebesgue measure,
it becomes important in the versions of FTC about any locally finite measure if this measure has an
atom at one of the endpoints.

### Combining one-sided and two-sided derivatives

There are some `FTC_filter` instances where the fact that it is one-sided or
two-sided depends on the point, namely `(x, 𝓝[Icc a b] x, 𝓝[Icc a b] x)`
(resp. `(x, 𝓝[[a, b]] x, 𝓝[[a, b]] x)`, where `[a, b] = set.interval a b`),
with `x ∈ Icc a b` (resp. `x ∈ [a, b]`).
This results in a two-sided derivatives for `x ∈ Ioo a b` and one-sided derivatives for
`x ∈ {a, b}`. Other instances could be added when needed (in that case, one also needs to add
instances for `filter.is_measurably_generated` and `filter.tendsto_Ixx_class`).

## Tags

integral, fundamental theorem of calculus, FTC-1, FTC-2, change of variables in integrals
-/

noncomputable theory
open topological_space (second_countable_topology)
open measure_theory set classical filter function

open_locale classical topological_space filter ennreal big_operators interval

variables {α β 𝕜 E F : Type*} [linear_order α] [measurable_space α]
  [measurable_space E] [normed_group E]

/-!
### Almost everywhere on an interval
-/

section
variables {μ : measure α} {a b : α} {P : α → Prop}

lemma ae_interval_oc_iff :
  (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ (∀ᵐ x ∂μ, x ∈ Ioc b a → P x) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

lemma ae_measurable_interval_oc_iff {μ : measure α} {β : Type*} [measurable_space β] {f : α → β} :
  (ae_measurable f $ μ.restrict $ Ι a b) ↔
  (ae_measurable f $ μ.restrict $ Ioc a b) ∧ (ae_measurable f $ μ.restrict $ Ioc b a) :=
by { dsimp [interval_oc], cases le_total a b with hab hab ; simp [hab] }

variables [topological_space α] [opens_measurable_space α] [order_closed_topology α]

lemma ae_interval_oc_iff' : (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔
  (∀ᵐ x ∂ (μ.restrict $ Ioc a b), P x) ∧ (∀ᵐ x ∂ (μ.restrict $ Ioc b a), P x) :=
begin
  simp_rw ae_interval_oc_iff,
  rw [ae_restrict_eq, eventually_inf_principal, ae_restrict_eq, eventually_inf_principal] ;
  exact measurable_set_Ioc
end

end

/-!
### Integrability at an interval
-/

/-- A function `f` is called *interval integrable* with respect to a measure `μ` on an unordered
interval `a..b` if it is integrable on both intervals `(a, b]` and `(b, a]`. One of these
intervals is always empty, so this property is equivalent to `f` being integrable on
`(min a b, max a b]`. -/
def interval_integrable (f : α → E) (μ : measure α) (a b : α) :=
integrable_on f (Ioc a b) μ ∧ integrable_on f (Ioc b a) μ

/-- A function is interval integrable with respect to a given measure `μ` on `interval a b` if and
  only if it is integrable on `interval_oc a b` with respect to `μ`. This is an equivalent
  defintion of `interval_integrable`. -/
lemma interval_integrable_iff {f : α → E} {a b : α} {μ : measure α} :
  interval_integrable f μ a b ↔ integrable_on f (Ι a b) μ :=
by cases le_total a b; simp [h, interval_integrable, interval_oc]

/-- If a function is interval integrable with respect to a given measure `μ` on `interval a b` then
  it is integrable on `interval_oc a b` with respect to `μ`. -/
lemma interval_integrable.def {f : α → E} {a b : α} {μ : measure α}
  (h : interval_integrable f μ a b) :
  integrable_on f (Ι a b) μ :=
interval_integrable_iff.mp h

lemma interval_integrable_iff_integrable_Ioc_of_le
  {f : α → E} {a b : α} (hab : a ≤ b) {μ : measure α} :
  interval_integrable f μ a b ↔ integrable_on f (Ioc a b) μ :=
by rw [interval_integrable_iff, interval_oc_of_le hab]

/-- If a function is integrable with respect to a given measure `μ` then it is interval integrable
  with respect to `μ` on `interval a b`. -/
lemma measure_theory.integrable.interval_integrable {f : α → E} {a b : α} {μ : measure α}
  (hf : integrable f μ) :
  interval_integrable f μ a b :=
⟨hf.integrable_on, hf.integrable_on⟩

lemma measure_theory.integrable_on.interval_integrable {f : α → E} {a b : α} {μ : measure α}
  (hf : integrable_on f (interval a b) μ) :
  interval_integrable f μ a b :=
⟨measure_theory.integrable_on.mono_set hf (Ioc_subset_Icc_self.trans Icc_subset_interval),
 measure_theory.integrable_on.mono_set hf (Ioc_subset_Icc_self.trans Icc_subset_interval')⟩

lemma interval_integrable_const_iff {a b : α} {μ : measure α} {c : E} :
  interval_integrable (λ _, c) μ a b ↔ c = 0 ∨ μ (Ι a b) < ∞ :=
by simp only [interval_integrable_iff, integrable_on_const]

@[simp] lemma interval_integrable_const [topological_space α] [compact_Icc_space α]
  {μ : measure α} [is_locally_finite_measure μ] {a b : α} {c : E} :
  interval_integrable (λ _, c) μ a b :=
interval_integrable_const_iff.2 $ or.inr measure_Ioc_lt_top

namespace interval_integrable

section

variables {f : α → E} {a b c d : α} {μ ν : measure α}

@[symm] lemma symm (h : interval_integrable f μ a b) : interval_integrable f μ b a :=
h.symm

@[refl] lemma refl : interval_integrable f μ a a :=
by split; simp

@[trans] lemma trans (hab : interval_integrable f μ a b) (hbc : interval_integrable f μ b c) :
  interval_integrable f μ a c :=
⟨(hab.1.union hbc.1).mono_set Ioc_subset_Ioc_union_Ioc,
  (hbc.2.union hab.2).mono_set Ioc_subset_Ioc_union_Ioc⟩

lemma trans_iterate {a : ℕ → α} {n : ℕ} (hint : ∀ k < n, interval_integrable f μ (a k) (a $ k+1)) :
  interval_integrable f μ (a 0) (a n) :=
begin
  induction n with n hn,
  { simp },
  { exact (hn (λ k hk, hint k (hk.trans n.lt_succ_self))).trans (hint n n.lt_succ_self) }
end

lemma neg [borel_space E] (h : interval_integrable f μ a b) : interval_integrable (-f) μ a b :=
⟨h.1.neg, h.2.neg⟩

lemma norm [opens_measurable_space E] (h : interval_integrable f μ a b) :
  interval_integrable (λ x, ∥f x∥) μ a b  :=
⟨h.1.norm, h.2.norm⟩

lemma abs {f : α → ℝ} (h : interval_integrable f μ a b) :
  interval_integrable (λ x, |f x|) μ a b  :=
h.norm

lemma mono
  (hf : interval_integrable f ν a b) (h1 : interval c d ⊆ interval a b) (h2 : μ ≤ ν) :
  interval_integrable f μ c d :=
let ⟨h1₁, h1₂⟩ := interval_subset_interval_iff_le.mp h1 in
interval_integrable_iff.mpr $ hf.def.mono (Ioc_subset_Ioc h1₁ h1₂) h2

lemma mono_set
  (hf : interval_integrable f μ a b) (h : interval c d ⊆ interval a b) :
  interval_integrable f μ c d :=
hf.mono h rfl.le

lemma mono_measure
  (hf : interval_integrable f ν a b) (h : μ ≤ ν) :
  interval_integrable f μ a b :=
hf.mono rfl.subset h

lemma mono_set_ae
  (hf : interval_integrable f μ a b) (h : Ι c d ≤ᵐ[μ] Ι a b) :
  interval_integrable f μ c d :=
interval_integrable_iff.mpr $ hf.def.mono_set_ae h

lemma mono_fun {F : Type*} [normed_group F] [measurable_space F] {g : α → F}
  (hf : interval_integrable f μ a b) (hgm : ae_measurable g (μ.restrict (Ι a b)))
  (hle : (λ x, ∥g x∥) ≤ᵐ[μ.restrict (Ι a b)] (λ x, ∥f x∥)) : interval_integrable g μ a b :=
interval_integrable_iff.2 $ hf.def.integrable.mono hgm hle

lemma mono_fun' {g : α → ℝ} (hg : interval_integrable g μ a b)
  (hfm : ae_measurable f (μ.restrict (Ι a b)))
  (hle : (λ x, ∥f x∥) ≤ᵐ[μ.restrict (Ι a b)] g) : interval_integrable f μ a b :=
interval_integrable_iff.2 $ hg.def.integrable.mono' hfm hle

protected lemma ae_measurable (h : interval_integrable f μ a b) :
  ae_measurable f (μ.restrict (Ioc a b)):=
h.1.ae_measurable

protected lemma ae_measurable' (h : interval_integrable f μ a b) :
  ae_measurable f (μ.restrict (Ioc b a)):=
h.2.ae_measurable

end

variables [borel_space E] {f g : α → E} {a b : α} {μ : measure α}

lemma smul [normed_field 𝕜] [normed_space 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  {f : α → E} {a b : α} {μ : measure α} (h : interval_integrable f μ a b) (r : 𝕜) :
  interval_integrable (r • f) μ a b :=
⟨h.1.smul r, h.2.smul r⟩

@[simp] lemma add [second_countable_topology E] (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b) : interval_integrable (λ x, f x + g x) μ a b :=
⟨hf.1.add hg.1, hf.2.add hg.2⟩

@[simp] lemma sub [second_countable_topology E] (hf : interval_integrable f μ a b)
  (hg : interval_integrable g μ a b) : interval_integrable (λ x, f x - g x) μ a b :=
⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

lemma mul_continuous_on {α : Type*} [conditionally_complete_linear_order α] [measurable_space α]
  [topological_space α] [order_topology α] [opens_measurable_space α]
  {μ : measure α} {a b : α} {f g : α → ℝ}
  (hf : interval_integrable f μ a b) (hg : continuous_on g (interval a b)) :
  interval_integrable (λ x, f x * g x) μ a b :=
begin
  rw interval_integrable_iff at hf ⊢,
  exact hf.mul_continuous_on_of_subset hg measurable_set_Ioc is_compact_interval Ioc_subset_Icc_self
end

lemma continuous_on_mul {α : Type*} [conditionally_complete_linear_order α] [measurable_space α]
  [topological_space α] [order_topology α] [opens_measurable_space α]
  {μ : measure α} {a b : α} {f g : α → ℝ}
  (hf : interval_integrable f μ a b) (hg : continuous_on g (interval a b)) :
  interval_integrable (λ x, g x * f x) μ a b :=
by simpa [mul_comm] using hf.mul_continuous_on hg

end interval_integrable

section

variables {μ : measure ℝ} [is_locally_finite_measure μ]

lemma continuous_on.interval_integrable [borel_space E] {u : ℝ → E} {a b : ℝ}
  (hu : continuous_on u (interval a b)) : interval_integrable u μ a b :=
(continuous_on.integrable_on_Icc hu).interval_integrable

lemma continuous_on.interval_integrable_of_Icc [borel_space E] {u : ℝ → E} {a b : ℝ} (h : a ≤ b)
  (hu : continuous_on u (Icc a b)) : interval_integrable u μ a b :=
continuous_on.interval_integrable ((interval_of_le h).symm ▸ hu)

/-- A continuous function on `ℝ` is `interval_integrable` with respect to any locally finite measure
`ν` on ℝ. -/
lemma continuous.interval_integrable [borel_space E] {u : ℝ → E} (hu : continuous u) (a b : ℝ) :
  interval_integrable u μ a b :=
hu.continuous_on.interval_integrable

end

section

variables {ι : Type*} [topological_space ι] [conditionally_complete_linear_order ι]
  [order_topology ι] [measurable_space ι] [borel_space ι] {μ : measure ι}
  [is_locally_finite_measure μ] [conditionally_complete_linear_order E] [order_topology E]
  [second_countable_topology E] [borel_space E]

lemma monotone_on.interval_integrable {u : ι → E} {a b : ι} (hu : monotone_on u (interval a b)) :
  interval_integrable u μ a b :=
begin
  rw interval_integrable_iff,
  exact (monotone_on.integrable_on_compact is_compact_interval hu).mono_set Ioc_subset_Icc_self,
end

lemma antitone_on.interval_integrable {u : ι → E} {a b : ι} (hu : antitone_on u (interval a b)) :
  interval_integrable u μ a b :=
@monotone_on.interval_integrable (order_dual E) _ ‹_› ι _ _ _ _ _ _ _ _ _ ‹_› ‹_› u a b hu

lemma monotone.interval_integrable {u : ι → E} {a b : ι} (hu : monotone u) :
  interval_integrable u μ a b :=
(hu.monotone_on _).interval_integrable

lemma antitone.interval_integrable {u : ι → E} {a b : ι} (hu :antitone u) :
  interval_integrable u μ a b :=
(hu.antitone_on _).interval_integrable

end

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : α → E` has a finite limit at `l' ⊓ μ.ae`. Then `f` is interval integrable on
`u..v` provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter α` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
lemma filter.tendsto.eventually_interval_integrable_ae {f : α → E} {μ : measure α}
  {l l' : filter α}  (hfm : measurable_at_filter f l' μ)
  [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  {u v : β → α} {lt : filter β} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  ∀ᶠ t in lt, interval_integrable f μ (u t) (v t) :=
have _ := (hf.integrable_at_filter_ae hfm hμ).eventually,
((hu.Ioc hv).eventually this).and $ (hv.Ioc hu).eventually this

/-- Let `l'` be a measurably generated filter; let `l` be a of filter such that each `s ∈ l'`
eventually includes `Ioc u v` as both `u` and `v` tend to `l`. Let `μ` be a measure finite at `l'`.

Suppose that `f : α → E` has a finite limit at `l`. Then `f` is interval integrable on `u..v`
provided that both `u` and `v` tend to `l`.

Typeclass instances allow Lean to find `l'` based on `l` but not vice versa, so
`apply tendsto.eventually_interval_integrable_ae` will generate goals `filter α` and
`tendsto_Ixx_class Ioc ?m_1 l'`. -/
lemma filter.tendsto.eventually_interval_integrable {f : α → E} {μ : measure α}
  {l l' : filter α} (hfm : measurable_at_filter f l' μ)
  [tendsto_Ixx_class Ioc l l'] [is_measurably_generated l']
  (hμ : μ.finite_at_filter l') {c : E} (hf : tendsto f l' (𝓝 c))
  {u v : β → α} {lt : filter β} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  ∀ᶠ t in lt, interval_integrable f μ (u t) (v t) :=
(hf.mono_left inf_le_left).eventually_interval_integrable_ae hfm hμ hu hv

/-!
### Interval integral: definition and basic properties

In this section we define `∫ x in a..b, f x ∂μ` as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`
and prove some basic properties.
-/

variables [second_countable_topology E] [complete_space E] [normed_space ℝ E]
  [borel_space E]

/-- The interval integral `∫ x in a..b, f x ∂μ` is defined
as `∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ`. If `a ≤ b`, then it equals
`∫ x in Ioc a b, f x ∂μ`, otherwise it equals `-∫ x in Ioc b a, f x ∂μ`. -/
def interval_integral (f : α → E) (a b : α) (μ : measure α) :=
∫ x in Ioc a b, f x ∂μ - ∫ x in Ioc b a, f x ∂μ

notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, f) ` ∂` μ:70 := interval_integral r a b μ
notation `∫` binders ` in ` a `..` b `, ` r:(scoped:60 f, interval_integral f a b volume) := r

namespace interval_integral

section basic

variables {a b : α} {f g : α → E} {μ : measure α}

@[simp] lemma integral_zero : ∫ x in a..b, (0 : E) ∂μ = 0 :=
by simp [interval_integral]

lemma integral_of_le (h : a ≤ b) : ∫ x in a..b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ :=
by simp [interval_integral, h]

@[simp] lemma integral_same : ∫ x in a..a, f x ∂μ = 0 :=
sub_self _

lemma integral_symm (a b) : ∫ x in b..a, f x ∂μ = -∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, neg_sub]

lemma integral_of_ge (h : b ≤ a) : ∫ x in a..b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ :=
by simp only [integral_symm b, integral_of_le h]

lemma interval_integral_eq_integral_interval_oc (f : α → E) (a b : α) (μ : measure α) :
  ∫ x in a..b, f x ∂μ = (if a ≤ b then 1 else -1 : ℝ) • ∫ x in Ι a b, f x ∂μ :=
begin
  split_ifs with h,
  { simp only [integral_of_le h, interval_oc_of_le h, one_smul] },
  { simp only [integral_of_ge (not_le.1 h).le, interval_oc_of_lt (not_le.1 h), neg_one_smul] }
end

lemma integral_cases (f : α → E) (a b) :
  ∫ x in a..b, f x ∂μ ∈ ({∫ x in Ι a b, f x ∂μ, -∫ x in Ι a b, f x ∂μ} : set E) :=
by { rw interval_integral_eq_integral_interval_oc, split_ifs; simp }

lemma integral_undef (h : ¬ interval_integrable f μ a b) :
  ∫ x in a..b, f x ∂μ = 0 :=
by cases le_total a b with hab hab;
  simp only [integral_of_le, integral_of_ge, hab, neg_eq_zero];
    refine integral_undef (not_imp_not.mpr integrable.integrable_on' _);
      simpa [hab] using not_and_distrib.mp h

lemma integral_non_ae_measurable
  (hf : ¬ ae_measurable f (μ.restrict (Ι a b))) :
  ∫ x in a..b, f x ∂μ = 0 :=
by rw [interval_integral_eq_integral_interval_oc, integral_non_ae_measurable hf, smul_zero]


lemma integral_non_ae_measurable_of_le (h : a ≤ b)
  (hf : ¬ ae_measurable f (μ.restrict (Ioc a b))) :
  ∫ x in a..b, f x ∂μ = 0 :=
integral_non_ae_measurable $ by rwa [interval_oc_of_le h]

lemma norm_integral_min_max (f : α → E) :
  ∥∫ x in min a b..max a b, f x ∂μ∥ = ∥∫ x in a..b, f x ∂μ∥ :=
by cases le_total a b; simp [*, integral_symm a b]

lemma norm_integral_eq_norm_integral_Ioc (f : α → E) :
  ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ι a b, f x ∂μ∥ :=
by rw [← norm_integral_min_max, integral_of_le min_le_max, interval_oc]

lemma abs_integral_eq_abs_integral_interval_oc (f : α → ℝ) :
  |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| :=
norm_integral_eq_norm_integral_Ioc f

lemma norm_integral_le_integral_norm_Ioc :
  ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in Ι a b, ∥f x∥ ∂μ :=
calc ∥∫ x in a..b, f x ∂μ∥ = ∥∫ x in Ι a b, f x ∂μ∥ :
  norm_integral_eq_norm_integral_Ioc f
... ≤ ∫ x in Ι a b, ∥f x∥ ∂μ :
  norm_integral_le_integral_norm f

lemma norm_integral_le_abs_integral_norm : ∥∫ x in a..b, f x ∂μ∥ ≤ |∫ x in a..b, ∥f x∥ ∂μ| :=
begin
  simp only [← real.norm_eq_abs, norm_integral_eq_norm_integral_Ioc],
  exact le_trans (norm_integral_le_integral_norm _) (le_abs_self _)
end

lemma norm_integral_le_integral_norm (h : a ≤ b) :
  ∥∫ x in a..b, f x ∂μ∥ ≤ ∫ x in a..b, ∥f x∥ ∂μ :=
norm_integral_le_integral_norm_Ioc.trans_eq $ by rw [interval_oc_of_le h, integral_of_le h]

lemma norm_integral_le_of_norm_le_const_ae {a b C : ℝ} {f : ℝ → E}
  (h : ∀ᵐ x, x ∈ Ι a b → ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * |b - a| :=
begin
  rw [norm_integral_eq_norm_integral_Ioc],
  convert norm_set_integral_le_of_norm_le_const_ae'' _ measurable_set_Ioc h,
  { rw [real.volume_Ioc, max_sub_min_eq_abs, ennreal.to_real_of_real (abs_nonneg _)] },
  { simp only [real.volume_Ioc, ennreal.of_real_lt_top] },
end

lemma norm_integral_le_of_norm_le_const {a b C : ℝ} {f : ℝ → E}
  (h : ∀ x ∈ Ι a b, ∥f x∥ ≤ C) :
  ∥∫ x in a..b, f x∥ ≤ C * |b - a| :=
norm_integral_le_of_norm_le_const_ae $ eventually_of_forall h

@[simp] lemma integral_add (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  ∫ x in a..b, f x + g x ∂μ = ∫ x in a..b, f x ∂μ + ∫ x in a..b, g x ∂μ :=
by simp only [interval_integral_eq_integral_interval_oc, integral_add hf.def hg.def, smul_add]

lemma integral_finset_sum {ι} {s : finset ι} {f : ι → α → E}
  (h : ∀ i ∈ s, interval_integrable (f i) μ a b) :
  ∫ x in a..b, ∑ i in s, f i x ∂μ = ∑ i in s, ∫ x in a..b, f i x ∂μ :=
by simp only [interval_integral_eq_integral_interval_oc,
  integral_finset_sum s (λ i hi, (h i hi).def), finset.smul_sum]

@[simp] lemma integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ :=
by { simp only [interval_integral, integral_neg], abel }

@[simp] lemma integral_sub (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b) :
  ∫ x in a..b, f x - g x ∂μ = ∫ x in a..b, f x ∂μ - ∫ x in a..b, g x ∂μ :=
by simpa only [sub_eq_add_neg] using (integral_add hf hg.neg).trans (congr_arg _ integral_neg)

@[simp] lemma integral_smul {𝕜 : Type*} [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E]
  [smul_comm_class ℝ 𝕜 E] [measurable_space 𝕜] [opens_measurable_space 𝕜]
  (r : 𝕜) (f : α → E) : ∫ x in a..b, r • f x ∂μ = r • ∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, integral_smul, smul_sub]

@[simp] lemma integral_smul_const {𝕜 : Type*} [is_R_or_C 𝕜] [normed_space 𝕜 E]
  (f : α → 𝕜) (c : E) :
  ∫ x in a..b, f x • c ∂μ = (∫ x in a..b, f x ∂μ) • c :=
by simp only [interval_integral_eq_integral_interval_oc, integral_smul_const, smul_assoc]

@[simp] lemma integral_const_mul {𝕜 : Type*} [is_R_or_C 𝕜]
  (r : 𝕜) (f : α → 𝕜) : ∫ x in a..b, r * f x ∂μ = r * ∫ x in a..b, f x ∂μ :=
integral_smul r f

@[simp] lemma integral_mul_const {𝕜 : Type*} [is_R_or_C 𝕜]
  (r : 𝕜) (f : α → 𝕜) : ∫ x in a..b, f x * r ∂μ = ∫ x in a..b, f x ∂μ * r :=
by simpa only [mul_comm r] using integral_const_mul r f

@[simp] lemma integral_div {𝕜 : Type*} [is_R_or_C 𝕜]
  (r : 𝕜) (f : α → 𝕜) : ∫ x in a..b, f x / r ∂μ = ∫ x in a..b, f x ∂μ / r :=
by simpa only [div_eq_mul_inv] using integral_mul_const r⁻¹ f

lemma integral_const' (c : E) :
  ∫ x in a..b, c ∂μ = ((μ $ Ioc a b).to_real - (μ $ Ioc b a).to_real) • c :=
by simp only [interval_integral, set_integral_const, sub_smul]

@[simp] lemma integral_const {a b : ℝ} (c : E) : ∫ x in a..b, c = (b - a) • c :=
by simp only [integral_const', real.volume_Ioc, ennreal.to_real_of_real', ← neg_sub b,
  max_zero_sub_eq_self]

lemma integral_smul_measure (c : ℝ≥0∞) :
  ∫ x in a..b, f x ∂(c • μ) = c.to_real • ∫ x in a..b, f x ∂μ :=
by simp only [interval_integral, measure.restrict_smul, integral_smul_measure, smul_sub]

variables [normed_group F] [second_countable_topology F] [complete_space F] [normed_space ℝ F]
  [measurable_space F] [borel_space F]

lemma _root_.continuous_linear_map.interval_integral_comp_comm
  (L : E →L[ℝ] F) (hf : interval_integrable f μ a b) :
  ∫ x in a..b, L (f x) ∂μ = L (∫ x in a..b, f x ∂μ) :=
begin
  rw [interval_integral, interval_integral, L.integral_comp_comm, L.integral_comp_comm, L.map_sub],
  exacts [hf.2, hf.1]
end

end basic

section comp

variables {a b c d : ℝ} (f : ℝ → E)

@[simp] lemma integral_comp_mul_right (hc : c ≠ 0) :
  ∫ x in a..b, f (x * c) = c⁻¹ • ∫ x in a*c..b*c, f x :=
begin
  have A : measurable_embedding (λ x, x * c) :=
    (homeomorph.mul_right₀ c hc).closed_embedding.measurable_embedding,
  conv_rhs { rw [← real.smul_map_volume_mul_right hc] },
  simp_rw [integral_smul_measure, interval_integral, A.set_integral_map,
          ennreal.to_real_of_real (abs_nonneg c)],
  cases hc.lt_or_lt,
  { simp [h, mul_div_cancel, hc, abs_of_neg, measure.restrict_congr_set Ico_ae_eq_Ioc] },
  { simp [h, mul_div_cancel, hc, abs_of_pos] }
end

@[simp] lemma smul_integral_comp_mul_right (c) :
  c • ∫ x in a..b, f (x * c) = ∫ x in a*c..b*c, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_mul_left (hc : c ≠ 0) :
  ∫ x in a..b, f (c * x) = c⁻¹ • ∫ x in c*a..c*b, f x :=
by simpa only [mul_comm c] using integral_comp_mul_right f hc

@[simp] lemma smul_integral_comp_mul_left (c) :
  c • ∫ x in a..b, f (c * x) = ∫ x in c*a..c*b, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_div (hc : c ≠ 0) :
  ∫ x in a..b, f (x / c) = c • ∫ x in a/c..b/c, f x :=
by simpa only [inv_inv₀] using integral_comp_mul_right f (inv_ne_zero hc)

@[simp] lemma inv_smul_integral_comp_div (c) :
  c⁻¹ • ∫ x in a..b, f (x / c) = ∫ x in a/c..b/c, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_add_right (d) :
  ∫ x in a..b, f (x + d) = ∫ x in a+d..b+d, f x :=
have A : measurable_embedding (λ x, x + d) :=
  (homeomorph.add_right d).closed_embedding.measurable_embedding,
calc  ∫ x in a..b, f (x + d)
    = ∫ x in a+d..b+d, f x ∂(measure.map (λ x, x + d) volume)
                           : by simp [interval_integral, A.set_integral_map]
... = ∫ x in a+d..b+d, f x : by rw [map_add_right_eq_self]

@[simp] lemma integral_comp_add_left (d) :
  ∫ x in a..b, f (d + x) = ∫ x in d+a..d+b, f x :=
by simpa only [add_comm] using integral_comp_add_right f d

@[simp] lemma integral_comp_mul_add (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (c * x + d) = c⁻¹ • ∫ x in c*a+d..c*b+d, f x :=
by rw [← integral_comp_add_right, ← integral_comp_mul_left _ hc]

@[simp] lemma smul_integral_comp_mul_add (c d) :
  c • ∫ x in a..b, f (c * x + d) = ∫ x in c*a+d..c*b+d, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_add_mul (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (d + c * x) = c⁻¹ • ∫ x in d+c*a..d+c*b, f x :=
by rw [← integral_comp_add_left, ← integral_comp_mul_left _ hc]

@[simp] lemma smul_integral_comp_add_mul (c d) :
  c • ∫ x in a..b, f (d + c * x) = ∫ x in d+c*a..d+c*b, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_div_add (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (x / c + d) = c • ∫ x in a/c+d..b/c+d, f x :=
by simpa only [div_eq_inv_mul, inv_inv₀] using integral_comp_mul_add f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_div_add (c d) :
  c⁻¹ • ∫ x in a..b, f (x / c + d) = ∫ x in a/c+d..b/c+d, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_add_div (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (d + x / c) = c • ∫ x in d+a/c..d+b/c, f x :=
by simpa only [div_eq_inv_mul, inv_inv₀] using integral_comp_add_mul f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_add_div (c d) :
  c⁻¹ • ∫ x in a..b, f (d + x / c) = ∫ x in d+a/c..d+b/c, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_mul_sub (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (c * x - d) = c⁻¹ • ∫ x in c*a-d..c*b-d, f x :=
by simpa only [sub_eq_add_neg] using integral_comp_mul_add f hc (-d)

@[simp] lemma smul_integral_comp_mul_sub (c d) :
  c • ∫ x in a..b, f (c * x - d) = ∫ x in c*a-d..c*b-d, f x  :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_sub_mul (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (d - c * x) = c⁻¹ • ∫ x in d-c*b..d-c*a, f x :=
begin
  simp only [sub_eq_add_neg, neg_mul_eq_neg_mul],
  rw [integral_comp_add_mul f (neg_ne_zero.mpr hc) d, integral_symm],
  simp only [inv_neg, smul_neg, neg_neg, neg_smul],
end

@[simp] lemma smul_integral_comp_sub_mul (c d) :
  c • ∫ x in a..b, f (d - c * x) = ∫ x in d-c*b..d-c*a, f x  :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_div_sub (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (x / c - d) = c • ∫ x in a/c-d..b/c-d, f x :=
by simpa only [div_eq_inv_mul, inv_inv₀] using integral_comp_mul_sub f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_div_sub (c d) :
  c⁻¹ • ∫ x in a..b, f (x / c - d) = ∫ x in a/c-d..b/c-d, f x  :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_sub_div (hc : c ≠ 0) (d) :
  ∫ x in a..b, f (d - x / c) = c • ∫ x in d-b/c..d-a/c, f x :=
by simpa only [div_eq_inv_mul, inv_inv₀] using integral_comp_sub_mul f (inv_ne_zero hc) d

@[simp] lemma inv_smul_integral_comp_sub_div (c d) :
  c⁻¹ • ∫ x in a..b, f (d - x / c) = ∫ x in d-b/c..d-a/c, f x :=
by by_cases hc : c = 0; simp [hc]

@[simp] lemma integral_comp_sub_right (d) :
  ∫ x in a..b, f (x - d) = ∫ x in a-d..b-d, f x :=
by simpa only [sub_eq_add_neg] using integral_comp_add_right f (-d)

@[simp] lemma integral_comp_sub_left (d) :
  ∫ x in a..b, f (d - x) = ∫ x in d-b..d-a, f x :=
by simpa only [one_mul, one_smul, inv_one] using integral_comp_sub_mul f one_ne_zero d

@[simp] lemma integral_comp_neg : ∫ x in a..b, f (-x) = ∫ x in -b..-a, f x :=
by simpa only [zero_sub] using integral_comp_sub_left f 0

end comp

/-!
### Integral is an additive function of the interval

In this section we prove that `∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ`
as well as a few other identities trivially equivalent to this one. We also prove that
`∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ` provided that `support f ⊆ Ioc a b`.
-/

section order_closed_topology

variables [topological_space α] [order_closed_topology α] [opens_measurable_space α]
  {a b c d : α} {f g : α → E} {μ : measure α}

lemma integrable_on_Icc_iff_integrable_on_Ioc'
  {E : Type*} [measurable_space E] [normed_group E]
  {f : α → E} {a b : α} (ha : μ {a} ≠ ⊤) :
  integrable_on f (Icc a b) μ ↔ integrable_on f (Ioc a b) μ :=
begin
  cases le_or_lt a b with hab hab,
  { have : Icc a b = Icc a a ∪ Ioc a b := (Icc_union_Ioc_eq_Icc le_rfl hab).symm,
    rw [this, integrable_on_union],
    simp [lt_top_iff_ne_top.2 ha] },
  { simp [hab, hab.le] },
end

lemma integrable_on_Icc_iff_integrable_on_Ioc
  {E : Type*} [measurable_space E] [normed_group E] [has_no_atoms μ] {f : α → E} {a b : α} :
  integrable_on f (Icc a b) μ ↔ integrable_on f (Ioc a b) μ :=
integrable_on_Icc_iff_integrable_on_Ioc' (by simp)

lemma interval_integrable_iff_integrable_Icc_of_le
  {E : Type*} [measurable_space E] [normed_group E]
  {f : α → E} {a b : α} (hab : a ≤ b) {μ : measure α} [has_no_atoms μ] :
  interval_integrable f μ a b ↔ integrable_on f (Icc a b) μ :=
by rw [interval_integrable_iff_integrable_Ioc_of_le hab, integrable_on_Icc_iff_integrable_on_Ioc]

/-- If two functions are equal in the relevant interval, their interval integrals are also equal. -/
lemma integral_congr {a b : α} (h : eq_on f g (interval a b)) :
  ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ :=
by cases le_total a b with hab hab; simpa [hab, integral_of_le, integral_of_ge]
  using set_integral_congr measurable_set_Ioc (h.mono Ioc_subset_Icc_self)

lemma integral_add_adjacent_intervals_cancel (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ + ∫ x in c..a, f x ∂μ = 0 :=
begin
  have hac := hab.trans hbc,
  simp only [interval_integral, ← add_sub_comm, sub_eq_zero],
  iterate 4 { rw ← integral_union },
  { suffices : Ioc a b ∪ Ioc b c ∪ Ioc c a = Ioc b a ∪ Ioc c b ∪ Ioc a c, by rw this,
    rw [Ioc_union_Ioc_union_Ioc_cycle, union_right_comm, Ioc_union_Ioc_union_Ioc_cycle,
      min_left_comm, max_left_comm] },
  all_goals { simp [*, measurable_set.union, measurable_set_Ioc, Ioc_disjoint_Ioc_same,
    Ioc_disjoint_Ioc_same.symm, hab.1, hab.2, hbc.1, hbc.2, hac.1, hac.2] }
end

lemma integral_add_adjacent_intervals (hab : interval_integrable f μ a b)
  (hbc : interval_integrable f μ b c) :
  ∫ x in a..b, f x ∂μ + ∫ x in b..c, f x ∂μ = ∫ x in a..c, f x ∂μ :=
by rw [← add_neg_eq_zero, ← integral_symm, integral_add_adjacent_intervals_cancel hab hbc]

lemma sum_integral_adjacent_intervals {a : ℕ → α} {n : ℕ}
  (hint : ∀ k < n, interval_integrable f μ (a k) (a $ k+1)) :
  ∑ (k : ℕ) in finset.range n, ∫ x in (a k)..(a $ k+1), f x ∂μ = ∫ x in (a 0)..(a n), f x ∂μ :=
begin
  induction n with n hn,
  { simp },
  { rw [finset.sum_range_succ, hn (λ k hk, hint k (hk.trans n.lt_succ_self))],
    exact integral_add_adjacent_intervals
      (interval_integrable.trans_iterate $ λ k hk, hint k (hk.trans n.lt_succ_self))
      (hint n n.lt_succ_self) }
end

lemma integral_interval_sub_left (hab : interval_integrable f μ a b)
  (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in a..c, f x ∂μ = ∫ x in c..b, f x ∂μ :=
sub_eq_of_eq_add' $ eq.symm $ integral_add_adjacent_intervals hac (hac.symm.trans hab)

lemma integral_interval_add_interval_comm (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ + ∫ x in c..d, f x ∂μ = ∫ x in a..d, f x ∂μ + ∫ x in c..b, f x ∂μ :=
by rw [← integral_add_adjacent_intervals hac hcd, add_assoc, add_left_comm,
  integral_add_adjacent_intervals hac (hac.symm.trans hab), add_comm]

lemma integral_interval_sub_interval_comm (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in c..d, f x ∂μ = ∫ x in a..c, f x ∂μ - ∫ x in b..d, f x ∂μ :=
by simp only [sub_eq_add_neg, ← integral_symm,
  integral_interval_add_interval_comm hab hcd.symm (hac.trans hcd)]

lemma integral_interval_sub_interval_comm' (hab : interval_integrable f μ a b)
  (hcd : interval_integrable f μ c d) (hac : interval_integrable f μ a c) :
  ∫ x in a..b, f x ∂μ - ∫ x in c..d, f x ∂μ = ∫ x in d..b, f x ∂μ - ∫ x in c..a, f x ∂μ :=
by { rw [integral_interval_sub_interval_comm hab hcd hac, integral_symm b d, integral_symm a c,
  sub_neg_eq_add, sub_eq_neg_add], }

lemma integral_Iic_sub_Iic (ha : integrable_on f (Iic a) μ) (hb : integrable_on f (Iic b) μ) :
  ∫ x in Iic b, f x ∂μ - ∫ x in Iic a, f x ∂μ = ∫ x in a..b, f x ∂μ :=
begin
  wlog hab : a ≤ b using [a b] tactic.skip,
  { rw [sub_eq_iff_eq_add', integral_of_le hab, ← integral_union (Iic_disjoint_Ioc le_rfl),
      Iic_union_Ioc_eq_Iic hab],
    exacts [measurable_set_Ioc, ha, hb.mono_set (λ _, and.right)] },
  { intros ha hb,
    rw [integral_symm, ← this hb ha, neg_sub] }
end

/-- If `μ` is a finite measure then `∫ x in a..b, c ∂μ = (μ (Iic b) - μ (Iic a)) • c`. -/
lemma integral_const_of_cdf [is_finite_measure μ] (c : E) :
  ∫ x in a..b, c ∂μ = ((μ (Iic b)).to_real - (μ (Iic a)).to_real) • c :=
begin
  simp only [sub_smul, ← set_integral_const],
  refine (integral_Iic_sub_Iic _ _).symm;
    simp only [integrable_on_const, measure_lt_top, or_true]
end

lemma integral_eq_integral_of_support_subset {f : α → E} {a b} (h : support f ⊆ Ioc a b) :
  ∫ x in a..b, f x ∂μ = ∫ x, f x ∂μ :=
begin
  cases le_total a b with hab hab,
  { rw [integral_of_le hab, ← integral_indicator measurable_set_Ioc, indicator_eq_self.2 h];
    apply_instance },
  { rw [Ioc_eq_empty hab.not_lt, subset_empty_iff, support_eq_empty_iff] at h,
    simp [h] }
end

lemma integral_congr_ae' {f g : α → E} (h : ∀ᵐ x ∂μ, x ∈ Ioc a b → f x = g x)
  (h' : ∀ᵐ x ∂μ, x ∈ Ioc b a → f x = g x) :
  ∫ (x : α) in a..b, f x ∂μ = ∫ (x : α) in a..b, g x ∂μ :=
by simp only [interval_integral, set_integral_congr_ae (measurable_set_Ioc) h,
              set_integral_congr_ae (measurable_set_Ioc) h']

lemma integral_congr_ae {f g : α → E} (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = g x) :
  ∫ (x : α) in a..b, f x ∂μ = ∫ (x : α) in a..b, g x ∂μ :=
integral_congr_ae' (ae_interval_oc_iff.mp h).1 (ae_interval_oc_iff.mp h).2

lemma integral_zero_ae {f : α → E} (h : ∀ᵐ x ∂μ, x ∈ Ι a b → f x = 0) :
  ∫ (x : α) in a..b, f x ∂μ = 0 :=
calc ∫ x in a..b, f x ∂μ = ∫ x in a..b, 0 ∂μ : integral_congr_ae h
                     ... = 0                 : integral_zero

lemma integral_indicator {a₁ a₂ a₃ : α} (h : a₂ ∈ Icc a₁ a₃) {f : α → E} :
  ∫ x in a₁..a₃, indicator {x | x ≤ a₂} f x ∂ μ = ∫ x in a₁..a₂, f x ∂ μ :=
begin
  have : {x | x ≤ a₂} ∩ Ioc a₁ a₃ = Ioc a₁ a₂, from Iic_inter_Ioc_of_le h.2,
  rw [integral_of_le h.1, integral_of_le (h.1.trans h.2),
      integral_indicator, measure.restrict_restrict, this],
  exact measurable_set_Iic,
  all_goals { apply measurable_set_Iic },
end

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
lemma tendsto_integral_filter_of_dominated_convergence {ι} {l : filter ι}
  [l.is_countably_generated] {F : ι → α → E} (bound : α → ℝ)
  (hF_meas : ∀ᶠ n in l, ae_measurable (F n) (μ.restrict (Ι a b)))
  (h_bound : ∀ᶠ n in l, ∀ᵐ x ∂μ, x ∈ Ι a b → ∥F n x∥ ≤ bound x)
  (bound_integrable : interval_integrable bound μ a b)
  (h_lim : ∀ᵐ x ∂μ, x ∈ Ι a b → tendsto (λ n, F n x) l (𝓝 (f x))) :
  tendsto (λn, ∫ x in a..b, F n x ∂μ) l (𝓝 $ ∫ x in a..b, f x ∂μ) :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
    ← ae_restrict_iff' measurable_set_interval_oc] at *,
  exact tendsto_const_nhds.smul
    (tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_lim)
end

/-- Lebesgue dominated convergence theorem for series. -/
lemma has_sum_integral_of_dominated_convergence {ι} [encodable ι]
  {F : ι → α → E} (bound : ι → α → ℝ)
  (hF_meas : ∀ n, ae_measurable (F n) (μ.restrict (Ι a b)))
  (h_bound : ∀ n, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F n t∥ ≤ bound n t)
  (bound_summable : ∀ᵐ t ∂μ, t ∈ Ι a b → summable (λ n, bound n t))
  (bound_integrable : interval_integrable (λ t, ∑' n, bound n t) μ a b)
  (h_lim : ∀ᵐ t ∂μ, t ∈ Ι a b → has_sum (λ n, F n t) (f t)) :
  has_sum (λn, ∫ t in a..b, F n t ∂μ) (∫ t in a..b, f t ∂μ) :=
begin
  simp only [interval_integrable_iff, interval_integral_eq_integral_interval_oc,
    ← ae_restrict_iff' measurable_set_interval_oc] at *,
  exact (has_sum_integral_of_dominated_convergence bound hF_meas h_bound bound_summable
    bound_integrable h_lim).const_smul
end

open topological_space
variables {X : Type*} [topological_space X] [first_countable_topology X]

/-- Continuity of interval integral with respect to a parameter, at a point within a set.
  Given `F : X → α → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀` within `s` and at `x₀`, and assume it is bounded by a function integrable
  on `[a, b]` independent of `x` in a neighborhood of `x₀` within `s`. If `(λ x, F x t)`
  is continuous at `x₀` within `s` for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫ t in a..b, F x t ∂μ) s x₀`. -/
lemma continuous_within_at_of_dominated_interval
  {F : X → α → E} {x₀ : X} {bound : α → ℝ} {a b : α} {s : set X}
  (hF_meas : ∀ᶠ x in 𝓝[s] x₀, ae_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → continuous_within_at (λ x, F x t) s x₀) :
  continuous_within_at (λ x, ∫ t in a..b, F x t ∂μ) s x₀ :=
tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter at a point.
  Given `F : X → α → E`, assume `F x` is ae-measurable on `[a, b]` for `x` in a
  neighborhood of `x₀`, and assume it is bounded by a function integrable on
  `[a, b]` independent of `x` in a neighborhood of `x₀`. If `(λ x, F x t)`
  is continuous at `x₀` for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫ t in a..b, F x t ∂μ) s x₀`. -/
lemma continuous_at_of_dominated_interval
  {F : X → α → E} {x₀ : X} {bound : α → ℝ} {a b : α}
  (hF_meas : ∀ᶠ x in 𝓝 x₀, ae_measurable (F x) (μ.restrict $ Ι a b))
  (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → continuous_at (λ x, F x t) x₀) :
  continuous_at (λ x, ∫ t in a..b, F x t ∂μ) x₀ :=
tendsto_integral_filter_of_dominated_convergence bound hF_meas h_bound bound_integrable h_cont

/-- Continuity of interval integral with respect to a parameter.
  Given `F : X → α → E`, assume each `F x` is ae-measurable on `[a, b]`,
  and assume it is bounded by a function integrable on `[a, b]` independent of `x`.
  If `(λ x, F x t)` is continuous for almost every `t` in `[a, b]`
  then the same holds for `(λ x, ∫ t in a..b, F x t ∂μ) s x₀`. -/
lemma continuous_of_dominated_interval {F : X → α → E} {bound : α → ℝ} {a b : α}
  (hF_meas : ∀ x, ae_measurable (F x) $ μ.restrict $ Ι a b)
  (h_bound : ∀ x, ∀ᵐ t ∂μ, t ∈ Ι a b → ∥F x t∥ ≤ bound t)
  (bound_integrable : interval_integrable bound μ a b)
  (h_cont : ∀ᵐ t ∂μ, t ∈ Ι a b → continuous (λ x, F x t)) :
  continuous (λ x, ∫ t in a..b, F x t ∂μ) :=
continuous_iff_continuous_at.mpr (λ x₀, continuous_at_of_dominated_interval
  (eventually_of_forall hF_meas) (eventually_of_forall h_bound) bound_integrable $ h_cont.mono $
  λ x himp hx, (himp hx).continuous_at)

end order_closed_topology

section continuous_primitive
open topological_space

variables [topological_space α] [order_topology α] [opens_measurable_space α]
          [first_countable_topology α] {a b : α} {μ : measure α}

lemma continuous_within_at_primitive {f : α → E} {a b₀ b₁ b₂ : α} (hb₀ : μ {b₀} = 0)
  (h_int : interval_integrable f μ (min a b₁) (max a b₂)) :
  continuous_within_at (λ b, ∫ x in a .. b, f x ∂ μ) (Icc b₁ b₂) b₀ :=
begin
  by_cases h₀ : b₀ ∈ Icc b₁ b₂,
  { have h₁₂ : b₁ ≤ b₂ := h₀.1.trans h₀.2,
    have min₁₂ : min b₁ b₂ = b₁ := min_eq_left h₁₂,
    have h_int' : ∀ {x}, x ∈ Icc b₁ b₂ → interval_integrable f μ b₁ x,
    { rintros x ⟨h₁, h₂⟩,
      apply h_int.mono_set,
      apply interval_subset_interval,
      { exact ⟨min_le_of_left_le (min_le_right a b₁),
                h₁.trans (h₂.trans $ le_max_of_le_right $ le_max_right _ _)⟩ },
      { exact ⟨min_le_of_left_le $ (min_le_right _ _).trans h₁,
                le_max_of_le_right $ h₂.trans $ le_max_right _ _⟩ } },
    have : ∀ b ∈ Icc b₁ b₂, ∫ x in a..b, f x ∂μ = ∫ x in a..b₁, f x ∂μ + ∫ x in b₁..b, f x ∂μ,
    { rintros b ⟨h₁, h₂⟩,
      rw ← integral_add_adjacent_intervals _ (h_int' ⟨h₁, h₂⟩),
      apply h_int.mono_set,
      apply interval_subset_interval,
      { exact ⟨min_le_of_left_le (min_le_left a b₁), le_max_of_le_right (le_max_left _ _)⟩ },
      { exact ⟨min_le_of_left_le (min_le_right _ _),
                le_max_of_le_right (h₁.trans $ h₂.trans (le_max_right a b₂))⟩ } },
    apply continuous_within_at.congr _ this (this _ h₀), clear this,
    refine continuous_within_at_const.add _,
    have : (λ b, ∫ x in b₁..b, f x ∂μ) =ᶠ[𝓝[Icc b₁ b₂] b₀]
            λ b, ∫ x in b₁..b₂, indicator {x | x ≤ b} f x ∂ μ,
    { apply eventually_eq_of_mem self_mem_nhds_within,
      exact λ b b_in, (integral_indicator b_in).symm },

    apply continuous_within_at.congr_of_eventually_eq _ this (integral_indicator h₀).symm,
    have : interval_integrable (λ x, ∥f x∥) μ b₁ b₂,
      from interval_integrable.norm (h_int' $ right_mem_Icc.mpr h₁₂),
    refine continuous_within_at_of_dominated_interval _ _ this _ ; clear this,
    { apply eventually.mono (self_mem_nhds_within),
      intros x hx,
      erw [ae_measurable_indicator_iff, measure.restrict_restrict, Iic_inter_Ioc_of_le],
      { rw min₁₂,
        exact (h_int' hx).1.ae_measurable },
      { exact le_max_of_le_right hx.2 },
      exacts [measurable_set_Iic, measurable_set_Iic] },
    { refine eventually_of_forall (λ (x : α), eventually_of_forall (λ (t : α), _)),
      dsimp [indicator],
      split_ifs ; simp },
    { have : ∀ᵐ t ∂μ, t < b₀ ∨ b₀ < t,
      { apply eventually.mono (compl_mem_ae_iff.mpr hb₀),
        intros x hx,
        exact ne.lt_or_lt hx },
      apply this.mono,
      rintros x₀ (hx₀ | hx₀) -,
      { have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : α | t ≤ x}.indicator f x₀ = f x₀,
        { apply mem_nhds_within_of_mem_nhds,
          apply eventually.mono (Ioi_mem_nhds hx₀),
          intros x hx,
          simp [hx.le] },
        apply continuous_within_at_const.congr_of_eventually_eq  this,
        simp [hx₀.le] },
      { have : ∀ᶠ x in 𝓝[Icc b₁ b₂] b₀, {t : α | t ≤ x}.indicator f x₀ = 0,
        { apply mem_nhds_within_of_mem_nhds,
          apply eventually.mono (Iio_mem_nhds hx₀),
          intros x hx,
          simp [hx] },
        apply continuous_within_at_const.congr_of_eventually_eq this,
        simp [hx₀] } } },
  { apply continuous_within_at_of_not_mem_closure,
    rwa [closure_Icc] }
end

lemma continuous_on_primitive {f : α → E} {a b : α} [has_no_atoms μ]
  (h_int : integrable_on f (Icc a b) μ) :
  continuous_on (λ x, ∫ t in Ioc a x, f t ∂ μ) (Icc a b) :=
begin
  by_cases h : a ≤ b,
  { have : ∀ x ∈ Icc a b, ∫ (t : α) in Ioc a x, f t ∂μ = ∫ (t : α) in a..x, f t ∂μ,
    { intros x x_in,
      simp_rw [← interval_oc_of_le h, integral_of_le x_in.1] },
    rw continuous_on_congr this,
    intros x₀ hx₀,
    refine continuous_within_at_primitive (measure_singleton x₀) _,
    simp only [interval_integrable_iff_integrable_Ioc_of_le, min_eq_left, max_eq_right, h],
    exact h_int.mono Ioc_subset_Icc_self le_rfl },
  { rw Icc_eq_empty h,
    exact continuous_on_empty _ },
end

lemma continuous_on_primitive_Icc {f : α → E} {a b : α} [has_no_atoms μ]
  (h_int : integrable_on f (Icc a b) μ) :
  continuous_on (λ x, ∫ t in Icc a x, f t ∂ μ) (Icc a b) :=
begin
  rw show (λ x, ∫ t in Icc a x, f t ∂μ) = λ x, ∫ t in Ioc a x, f t ∂μ,
    by { ext x, exact integral_Icc_eq_integral_Ioc },
  exact continuous_on_primitive h_int
end

/-- Note: this assumes that `f` is `interval_integrable`, in contrast to some other lemmas here. -/
lemma continuous_on_primitive_interval' {f : α → E} {a b₁ b₂ : α} [has_no_atoms μ]
  (h_int : interval_integrable f μ b₁ b₂) (ha : a ∈ [b₁, b₂]) :
  continuous_on (λ b, ∫ x in a..b, f x ∂ μ) [b₁, b₂] :=
begin
  intros b₀ hb₀,
  refine continuous_within_at_primitive (measure_singleton _) _,
  rw [min_eq_right ha.1, max_eq_right ha.2],
  simpa [interval_integrable_iff, interval_oc] using h_int,
end

lemma continuous_on_primitive_interval {f : α → E} {a b : α} [has_no_atoms μ]
  (h_int : integrable_on f (interval a b) μ) :
  continuous_on (λ x, ∫ t in a..x, f t ∂ μ) (interval a b) :=
continuous_on_primitive_interval' h_int.interval_integrable left_mem_interval

lemma continuous_on_primitive_interval_left {f : α → E} {a b : α} [has_no_atoms μ]
  (h_int : integrable_on f (interval a b) μ) :
  continuous_on (λ x, ∫ t in x..b, f t ∂ μ) (interval a b) :=
begin
  rw interval_swap a b at h_int ⊢,
  simp only [integral_symm b],
  exact (continuous_on_primitive_interval h_int).neg,
end

variables [no_min_order α] [no_max_order α] [has_no_atoms μ]

lemma continuous_primitive {f : α → E} (h_int : ∀ a b : α, interval_integrable f μ a b) (a : α) :
  continuous (λ b, ∫ x in a..b, f x ∂ μ) :=
begin
  rw continuous_iff_continuous_at,
  intro b₀,
  cases exists_lt b₀ with b₁ hb₁,
  cases exists_gt b₀ with b₂ hb₂,
  apply continuous_within_at.continuous_at _ (Icc_mem_nhds hb₁ hb₂),
  exact continuous_within_at_primitive (measure_singleton b₀) (h_int _ _)
end

lemma _root_.measure_theory.integrable.continuous_primitive {f : α → E} (h_int : integrable f μ)
  (a : α) : continuous (λ b, ∫ x in a..b, f x ∂ μ) :=
continuous_primitive (λ _ _, h_int.interval_integrable) a

end continuous_primitive

section

variables {f g : α → ℝ} {a b : α} {μ : measure α}

lemma integral_eq_zero_iff_of_le_of_nonneg_ae (hab : a ≤ b)
  (hf : 0 ≤ᵐ[μ.restrict (Ioc a b)] f) (hfi : interval_integrable f μ a b) :
  ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b)] 0 :=
by rw [integral_of_le hab, integral_eq_zero_iff_of_nonneg_ae hf hfi.1]

lemma integral_eq_zero_iff_of_nonneg_ae
  (hf : 0 ≤ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] f) (hfi : interval_integrable f μ a b) :
  ∫ x in a..b, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict (Ioc a b ∪ Ioc b a)] 0 :=
begin
  cases le_total a b with hab hab;
    simp only [Ioc_eq_empty hab.not_lt, empty_union, union_empty] at hf ⊢,
  { exact integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi },
  { rw [integral_symm, neg_eq_zero, integral_eq_zero_iff_of_le_of_nonneg_ae hab hf hfi.symm] }
end

/-- If `f` is nonnegative and integrable on the unordered interval `set.interval_oc a b`, then its
integral over `a..b` is positive if and only if `a < b` and the measure of
`function.support f ∩ set.Ioc a b` is positive. -/
lemma integral_pos_iff_support_of_nonneg_ae'
  (hf : 0 ≤ᵐ[μ.restrict (Ι a b)] f) (hfi : interval_integrable f μ a b) :
  0 < ∫ x in a..b, f x ∂μ ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) :=
begin
  cases lt_or_le a b with hab hba,
  { rw interval_oc_of_le hab.le at hf,
    simp only [hab, true_and, integral_of_le hab.le,
      set_integral_pos_iff_support_of_nonneg_ae hf hfi.1] },
  { suffices : ∫ x in a..b, f x ∂μ ≤ 0, by simp only [this.not_lt, hba.not_lt, false_and],
    rw [integral_of_ge hba, neg_nonpos],
    rw [interval_oc_swap, interval_oc_of_le hba] at hf,
    exact integral_nonneg_of_ae hf }
end

/-- If `f` is nonnegative a.e.-everywhere and it is integrable on the unordered interval
`set.interval_oc a b`, then its integral over `a..b` is positive if and only if `a < b` and the
measure of `function.support f ∩ set.Ioc a b` is positive. -/
lemma integral_pos_iff_support_of_nonneg_ae (hf : 0 ≤ᵐ[μ] f) (hfi : interval_integrable f μ a b) :
  0 < ∫ x in a..b, f x ∂μ ↔ a < b ∧ 0 < μ (support f ∩ Ioc a b) :=
integral_pos_iff_support_of_nonneg_ae' (ae_mono measure.restrict_le_self hf) hfi

/-- If `f` and `g` are two functions that are interval integrable on `a..b`, `a ≤ b`,
`f x ≤ g x` for a.e. `x ∈ set.Ioc a b`, and `f x < g x` on a subset of `set.Ioc a b`
of nonzero measure, then `∫ x in a..b, f x ∂μ < ∫ x in a..b, g x ∂μ`. -/
lemma integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero (hab : a ≤ b)
  (hfi : interval_integrable f μ a b) (hgi : interval_integrable g μ a b)
  (hle : f ≤ᵐ[μ.restrict (Ioc a b)] g) (hlt : μ.restrict (Ioc a b) {x | f x < g x} ≠ 0) :
  ∫ x in a..b, f x ∂μ < ∫ x in a..b, g x ∂μ :=
begin
  rw [← sub_pos, ← integral_sub hgi hfi, integral_of_le hab,
    measure_theory.integral_pos_iff_support_of_nonneg_ae],
  { refine pos_iff_ne_zero.2 (mt (measure_mono_null _) hlt),
    exact λ x hx, (sub_pos.2 hx).ne' },
  exacts [hle.mono (λ x, sub_nonneg.2), hgi.1.sub hfi.1]
end

/-- If `f` and `g` are continuous on `[a, b]`, `a < b`, `f x ≤ g x` on this interval, and
`f c < g c` at some point `c ∈ [a, b]`, then `∫ x in a..b, f x < ∫ x in a..b, g x`. -/
lemma integral_lt_integral_of_continuous_on_of_le_of_exists_lt {f g : ℝ → ℝ} {a b : ℝ}
  (hab : a < b) (hfc : continuous_on f (Icc a b)) (hgc : continuous_on g (Icc a b))
  (hle : ∀ x ∈ Ioc a b, f x ≤ g x) (hlt : ∃ c ∈ Icc a b, f c < g c) :
  ∫ x in a..b, f x < ∫ x in a..b, g x :=
begin
  refine integral_lt_integral_of_ae_le_of_measure_set_of_lt_ne_zero hab.le
    (hfc.interval_integrable_of_Icc hab.le) (hgc.interval_integrable_of_Icc hab.le)
    ((ae_restrict_mem measurable_set_Ioc).mono hle) _,
  contrapose! hlt,
  have h_eq : f =ᵐ[volume.restrict (Ioc a b)] g,
  { simp only [← not_le, ← ae_iff] at hlt,
    exact eventually_le.antisymm ((ae_restrict_iff' measurable_set_Ioc).2 $
      eventually_of_forall hle) hlt },
  simp only [measure.restrict_congr_set Ioc_ae_eq_Icc] at h_eq,
  exact λ c hc, (measure.eq_on_Icc_of_ae_eq volume hab.ne h_eq hfc hgc hc).ge
end

lemma integral_nonneg_of_ae_restrict (hab : a ≤ b) (hf : 0 ≤ᵐ[μ.restrict (Icc a b)] f) :
  0 ≤ (∫ u in a..b, f u ∂μ) :=
let H := ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self hf in
by simpa only [integral_of_le hab] using set_integral_nonneg_of_ae_restrict H

lemma integral_nonneg_of_ae (hab : a ≤ b) (hf : 0 ≤ᵐ[μ] f) :
  0 ≤ (∫ u in a..b, f u ∂μ) :=
integral_nonneg_of_ae_restrict hab $ ae_restrict_of_ae hf

lemma integral_nonneg_of_forall (hab : a ≤ b) (hf : ∀ u, 0 ≤ f u) :
  0 ≤ (∫ u in a..b, f u ∂μ) :=
integral_nonneg_of_ae hab $ eventually_of_forall hf

lemma integral_nonneg [topological_space α] [opens_measurable_space α] [order_closed_topology α]
  (hab : a ≤ b) (hf : ∀ u, u ∈ Icc a b → 0 ≤ f u) :
  0 ≤ (∫ u in a..b, f u ∂μ) :=
integral_nonneg_of_ae_restrict hab $ (ae_restrict_iff' measurable_set_Icc).mpr $ ae_of_all μ hf

lemma abs_integral_le_integral_abs (hab : a ≤ b) :
  |∫ x in a..b, f x ∂μ| ≤ ∫ x in a..b, |f x| ∂μ :=
by simpa only [← real.norm_eq_abs] using norm_integral_le_integral_norm hab

section mono

variables (hab : a ≤ b) (hf : interval_integrable f μ a b) (hg : interval_integrable g μ a b)

include hab hf hg

lemma integral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict (Icc a b)] g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
let H := h.filter_mono $ ae_mono $ measure.restrict_mono Ioc_subset_Icc_self $ le_refl μ in
by simpa only [integral_of_le hab] using set_integral_mono_ae_restrict hf.1 hg.1 H

lemma integral_mono_ae (h : f ≤ᵐ[μ] g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
by simpa only [integral_of_le hab] using set_integral_mono_ae hf.1 hg.1 h

lemma integral_mono_on [topological_space α] [opens_measurable_space α] [order_closed_topology α]
  (h : ∀ x ∈ Icc a b, f x ≤ g x) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
let H := λ x hx, h x $ Ioc_subset_Icc_self hx in
by simpa only [integral_of_le hab] using set_integral_mono_on hf.1 hg.1 measurable_set_Ioc H

lemma integral_mono (h : f ≤ g) :
  ∫ u in a..b, f u ∂μ ≤ ∫ u in a..b, g u ∂μ :=
integral_mono_ae hab hf hg $ ae_of_all _ h

omit hg hab

lemma integral_mono_interval {c d} (hca : c ≤ a) (hab : a ≤ b) (hbd : b ≤ d)
  (hf : 0 ≤ᵐ[μ.restrict (Ioc c d)] f) (hfi : interval_integrable f μ c d):
  ∫ x in a..b, f x ∂μ ≤ ∫ x in c..d, f x ∂μ :=
begin
  rw [integral_of_le hab, integral_of_le (hca.trans (hab.trans hbd))],
  exact set_integral_mono_set hfi.1 hf (Ioc_subset_Ioc hca hbd).eventually_le
end

lemma abs_integral_mono_interval {c d } (h : Ι a b ⊆ Ι c d)
  (hf : 0 ≤ᵐ[μ.restrict (Ι c d)] f) (hfi : interval_integrable f μ c d) :
  |∫ x in a..b, f x ∂μ| ≤ |∫ x in c..d, f x ∂μ| :=
have hf' : 0 ≤ᵐ[μ.restrict (Ι a b)] f, from ae_mono (measure.restrict_mono h le_rfl) hf,
calc |∫ x in a..b, f x ∂μ| = |∫ x in Ι a b, f x ∂μ| : abs_integral_eq_abs_integral_interval_oc f
... = ∫ x in Ι a b, f x ∂μ : abs_of_nonneg (measure_theory.integral_nonneg_of_ae hf')
... ≤ ∫ x in Ι c d, f x ∂μ : set_integral_mono_set hfi.def hf h.eventually_le
... ≤ |∫ x in Ι c d, f x ∂μ| : le_abs_self _
... = |∫ x in c..d, f x ∂μ| : (abs_integral_eq_abs_integral_interval_oc f).symm

end mono

end

/-!
### Fundamental theorem of calculus, part 1, for any measure

In this section we prove a few lemmas that can be seen as versions of FTC-1 for interval integrals
w.r.t. any measure. Many theorems are formulated for one or two pairs of filters related by
`FTC_filter a l l'`. This typeclass has exactly four “real” instances: `(a, pure a, ⊥)`,
`(a, 𝓝[≥] a, 𝓝[>] a)`, `(a, 𝓝[≤] a, 𝓝[≤] a)`, `(a, 𝓝 a, 𝓝 a)`, and two instances
that are equal to the first and last “real” instances: `(a, 𝓝[{a}] a, ⊥)` and
`(a, 𝓝[univ] a, 𝓝[univ] a)`.  We use this approach to avoid repeating arguments in many very similar
cases.  Lean can automatically find both `a` and `l'` based on `l`.

The most general theorem `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` can be seen
as a generalization of lemma `integral_has_strict_fderiv_at` below which states strict
differentiability of `∫ x in u..v, f x` in `(u, v)` at `(a, b)` for a measurable function `f` that
is integrable on `a..b` and is continuous at `a` and `b`. The lemma is generalized in three
directions: first, `measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae` deals with any
locally finite measure `μ`; second, it works for one-sided limits/derivatives; third, it assumes
only that `f` has finite limits almost surely at `a` and `b`.

Namely, let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of
`FTC_filter`s around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f`
has finite limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.  Then
`∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ = ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
  o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This theorem is formulated with integral of constants instead of measures in the right hand sides
for two reasons: first, this way we avoid `min`/`max` in the statements; second, often it is
possible to write better `simp` lemmas for these integrals, see `integral_const` and
`integral_const_of_cdf`.

In the next subsection we apply this theorem to prove various theorems about differentiability
of the integral w.r.t. Lebesgue measure. -/

/-- An auxiliary typeclass for the Fundamental theorem of calculus, part 1. It is used to formulate
theorems that work simultaneously for left and right one-sided derivatives of `∫ x in u..v, f x`. -/
class FTC_filter {β : Type*} [linear_order β] [measurable_space β] [topological_space β]
  (a : out_param β) (outer : filter β) (inner : out_param $ filter β)
  extends tendsto_Ixx_class Ioc outer inner : Prop :=
(pure_le : pure a ≤ outer)
(le_nhds : inner ≤ 𝓝 a)
[meas_gen : is_measurably_generated inner]

/- The `dangerous_instance` linter doesn't take `out_param`s into account, so it thinks that
`FTC_filter.to_tendsto_Ixx_class` is dangerous. Disable this linter using `nolint`.
-/
attribute [nolint dangerous_instance] FTC_filter.to_tendsto_Ixx_class

namespace FTC_filter

variables [linear_order β] [measurable_space β] [topological_space β]

instance pure (a : β) : FTC_filter a (pure a) ⊥ :=
{ pure_le := le_rfl,
  le_nhds := bot_le }

instance nhds_within_singleton (a : β) : FTC_filter a (𝓝[{a}] a) ⊥ :=
by { rw [nhds_within, principal_singleton, inf_eq_right.2 (pure_le_nhds a)], apply_instance }

lemma finite_at_inner {a : β} (l : filter β) {l'} [h : FTC_filter a l l']
  {μ : measure β} [is_locally_finite_measure μ] :
  μ.finite_at_filter l' :=
(μ.finite_at_nhds a).filter_mono h.le_nhds

variables [opens_measurable_space β] [order_topology β]

instance nhds (a : β) : FTC_filter a (𝓝 a) (𝓝 a) :=
{ pure_le := pure_le_nhds a,
  le_nhds := le_rfl }

instance nhds_univ (a : β) : FTC_filter a (𝓝[univ] a) (𝓝 a) :=
by { rw nhds_within_univ, apply_instance }

instance nhds_left (a : β) : FTC_filter a (𝓝[≤] a) (𝓝[≤] a) :=
{ pure_le := pure_le_nhds_within right_mem_Iic,
  le_nhds := inf_le_left }

instance nhds_right (a : β) : FTC_filter a (𝓝[≥] a) (𝓝[>] a) :=
{ pure_le := pure_le_nhds_within left_mem_Ici,
  le_nhds := inf_le_left }

instance nhds_Icc {x a b : β} [h : fact (x ∈ Icc a b)] :
  FTC_filter x (𝓝[Icc a b] x) (𝓝[Icc a b] x) :=
{ pure_le := pure_le_nhds_within h.out,
  le_nhds := inf_le_left }

instance nhds_interval {x a b : β} [h : fact (x ∈ [a, b])] :
  FTC_filter x (𝓝[[a, b]] x) (𝓝[[a, b]] x) :=
by { haveI : fact (x ∈ set.Icc (min a b) (max a b)) := h, exact FTC_filter.nhds_Icc }

end FTC_filter

open asymptotics

section

variables {f : α → E} {a b : α} {c ca cb : E} {l l' la la' lb lb' : filter α} {lt : filter β}
  {μ : measure α} {u v ua va ub vb : β → α}

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, where `μ` is a measure
finite at `l'`, then `∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both
`u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hl : μ.finite_at_filter l')
  (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
begin
  have A := hf.integral_sub_linear_is_o_ae hfm hl (hu.Ioc hv),
  have B := hf.integral_sub_linear_is_o_ae hfm hl (hv.Ioc hu),
  simp only [integral_const'],
  convert (A.trans_le _).sub (B.trans_le _),
  { ext t,
    simp_rw [interval_integral, sub_smul],
    abel },
  all_goals { intro t, cases le_total (u t) (v t) with huv huv; simp [huv] }
end

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both
`u` and `v` tend to `l` so that `u ≤ v`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hl : μ.finite_at_filter l') (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c)
    (λ t, (μ $ Ioc (u t) (v t)).to_real) lt :=
(measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf hl hu hv).congr'
  (huv.mono $ λ x hx, by simp [integral_const', hx])
  (huv.mono $ λ x hx, by simp [integral_const', hx])

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `tendsto_Ixx_class Ioc`.
If `f` has a finite limit `c` at `l ⊓ μ.ae`, where `μ` is a measure
finite at `l`, then `∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both
`u` and `v` tend to `l` so that `v ≤ u`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge` for a version assuming
`[FTC_filter a l l']` and `[is_locally_finite_measure μ]`. If `l` is one of `𝓝[≥] a`,
`𝓝[≤] a`, `𝓝 a`, then it's easier to apply the non-primed version.
The primed version also works, e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'
  [is_measurably_generated l'] [tendsto_Ixx_class Ioc l l']
  (hfm : measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hl : μ.finite_at_filter l') (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c)
    (λ t, (μ $ Ioc (v t) (u t)).to_real) lt :=
(measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf hl hv hu huv).neg_left.congr_left $
  λ t, by simp [integral_symm (u t), add_comm]

variables [topological_space α]

section

variables [is_locally_finite_measure μ] [FTC_filter a l l']

include a

local attribute [instance] FTC_filter.meas_gen

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, 1 ∂μ)` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae'` for a version that also works, e.g., for
`l = l' = at_top`.

We use integrals of constants instead of measures because this way it is easier to formulate
a statement that works in both cases `u ≤ v` and `v ≤ u`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae (hfm : measurable_at_filter f l' μ)
  (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
measure_integral_sub_linear_is_o_of_tendsto_ae' hfm hf (FTC_filter.finite_at_inner l) hu hv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = μ (Ioc u v) • c + o(μ(Ioc u v))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_le'` for a version that also works,
e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_le
  (hfm : measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : u ≤ᶠ[lt] v) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ - (μ (Ioc (u t) (v t))).to_real • c)
    (λ t, (μ $ Ioc (u t) (v t)).to_real) lt :=
measure_integral_sub_linear_is_o_of_tendsto_ae_of_le' hfm hf (FTC_filter.finite_at_inner l)
  hu hv huv

/-- Fundamental theorem of calculus-1, local version for any measure.
Let filters `l` and `l'` be related by `[FTC_filter a l l']`; let `μ` be a locally finite measure.
If `f` has a finite limit `c` at `l' ⊓ μ.ae`, then
`∫ x in u..v, f x ∂μ = -μ (Ioc v u) • c + o(μ(Ioc v u))` as both `u` and `v` tend to `l`.

See also `measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge'` for a version that also works,
e.g., for `l = l' = at_top`. -/
lemma measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge
  (hfm : measurable_at_filter f l' μ) (hf : tendsto f (l' ⊓ μ.ae) (𝓝 c))
  (hu : tendsto u lt l) (hv : tendsto v lt l) (huv : v ≤ᶠ[lt] u) :
  is_o (λ t, ∫ x in u t..v t, f x ∂μ + (μ (Ioc (v t) (u t))).to_real • c)
    (λ t, (μ $ Ioc (v t) (u t)).to_real) lt :=
measure_integral_sub_linear_is_o_of_tendsto_ae_of_ge' hfm hf (FTC_filter.finite_at_inner l)
  hu hv huv

end

variables [order_topology α] [borel_space α]

local attribute [instance] FTC_filter.meas_gen

variables [FTC_filter a la la'] [FTC_filter b lb lb'] [is_locally_finite_measure μ]

/-- Fundamental theorem of calculus-1, strict derivative in both limits for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`; let `(lb, lb')` be a pair of `FTC_filter`s around `b`. Suppose that `f` has finite
limits `ca` and `cb` at `la' ⊓ μ.ae` and `lb' ⊓ μ.ae`, respectively.
Then `∫ x in va..vb, f x ∂μ - ∫ x in ua..ub, f x ∂μ =
  ∫ x in ub..vb, cb ∂μ - ∫ x in ua..va, ca ∂μ +
    o(∥∫ x in ua..va, (1:ℝ) ∂μ∥ + ∥∫ x in ub..vb, (1:ℝ) ∂μ∥)`
as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hab : interval_integrable f μ a b)
  (hmeas_a : measurable_at_filter f la' μ) (hmeas_b : measurable_at_filter f lb' μ)
  (ha_lim : tendsto f (la' ⊓ μ.ae) (𝓝 ca)) (hb_lim : tendsto f (lb' ⊓ μ.ae) (𝓝 cb))
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  is_o (λ t, (∫ x in va t..vb t, f x ∂μ) - (∫ x in ua t..ub t, f x ∂μ) -
    (∫ x in ub t..vb t, cb ∂μ - ∫ x in ua t..va t, ca ∂μ))
    (λ t, ∥∫ x in ua t..va t, (1:ℝ) ∂μ∥ + ∥∫ x in ub t..vb t, (1:ℝ) ∂μ∥) lt :=
begin
  refine
    ((measure_integral_sub_linear_is_o_of_tendsto_ae hmeas_a ha_lim hua hva).neg_left.add_add
    (measure_integral_sub_linear_is_o_of_tendsto_ae hmeas_b hb_lim hub hvb)).congr'
      _ eventually_eq.rfl,
  have A : ∀ᶠ t in lt, interval_integrable f μ (ua t) (va t) :=
    ha_lim.eventually_interval_integrable_ae hmeas_a (FTC_filter.finite_at_inner la) hua hva,
  have A' : ∀ᶠ t in lt, interval_integrable f μ a (ua t) :=
    ha_lim.eventually_interval_integrable_ae hmeas_a (FTC_filter.finite_at_inner la)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hua,
  have B : ∀ᶠ t in lt, interval_integrable f μ (ub t) (vb t) :=
    hb_lim.eventually_interval_integrable_ae hmeas_b (FTC_filter.finite_at_inner lb) hub hvb,
  have B' : ∀ᶠ t in lt, interval_integrable f μ b (ub t) :=
    hb_lim.eventually_interval_integrable_ae hmeas_b (FTC_filter.finite_at_inner lb)
      (tendsto_const_pure.mono_right FTC_filter.pure_le) hub,
  filter_upwards [A, A', B, B'] with _ ua_va a_ua ub_vb b_ub,
  rw [← integral_interval_sub_interval_comm'],
  { dsimp only [], abel, },
  exacts [ub_vb, ua_va, b_ub.symm.trans $ hab.symm.trans a_ua]
end

/-- Fundamental theorem of calculus-1, strict derivative in right endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(lb, lb')` be a pair of `FTC_filter`s
around `b`. Suppose that `f` has a finite limit `c` at `lb' ⊓ μ.ae`.

Then `∫ x in a..v, f x ∂μ - ∫ x in a..u, f x ∂μ = ∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `lb`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  (hab : interval_integrable f μ a b) (hmeas : measurable_at_filter f lb' μ)
  (hf : tendsto f (lb' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  is_o (λ t, ∫ x in a..v t, f x ∂μ - ∫ x in a..u t, f x ∂μ - ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  hab measurable_at_bot hmeas ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left)
  hf (tendsto_const_pure : tendsto _ _ (pure a)) tendsto_const_pure hu hv

/-- Fundamental theorem of calculus-1, strict derivative in left endpoint for a locally finite
measure.

Let `f` be a measurable function integrable on `a..b`. Let `(la, la')` be a pair of `FTC_filter`s
around `a`. Suppose that `f` has a finite limit `c` at `la' ⊓ μ.ae`.

Then `∫ x in v..b, f x ∂μ - ∫ x in u..b, f x ∂μ = -∫ x in u..v, c ∂μ + o(∫ x in u..v, (1:ℝ) ∂μ)`
as `u` and `v` tend to `la`.
-/
lemma measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  (hab : interval_integrable f μ a b) (hmeas : measurable_at_filter f la' μ)
  (hf : tendsto f (la' ⊓ μ.ae) (𝓝 c)) (hu : tendsto u lt la) (hv : tendsto v lt la) :
  is_o (λ t, ∫ x in v t..b, f x ∂μ - ∫ x in u t..b, f x ∂μ + ∫ x in u t..v t, c ∂μ)
    (λ t, ∫ x in u t..v t, (1:ℝ) ∂μ) lt :=
by simpa using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  hab hmeas measurable_at_bot hf ((tendsto_bot : tendsto _ ⊥ (𝓝 0)).mono_left inf_le_left)
  hu hv (tendsto_const_pure : tendsto _ _ (pure b)) tendsto_const_pure

end

/-!
### Fundamental theorem of calculus-1 for Lebesgue measure

In this section we restate theorems from the previous section for Lebesgue measure.
In particular, we prove that `∫ x in u..v, f x` is strictly differentiable in `(u, v)`
at `(a, b)` provided that `f` is integrable on `a..b` and is continuous at `a` and `b`.
-/

variables {f : ℝ → E} {c ca cb : E} {l l' la la' lb lb' : filter ℝ} {lt : filter β}
  {a b z : ℝ} {u v ua ub va vb : β → ℝ} [FTC_filter a la la'] [FTC_filter b lb lb']

/-!
#### Auxiliary `is_o` statements

In this section we prove several lemmas that can be interpreted as strict differentiability of
`(u, v) ↦ ∫ x in u..v, f x ∂μ` in `u` and/or `v` at a filter. The statements use `is_o` because
we have no definition of `has_strict_(f)deriv_at_filter` in the library.
-/

/-- Fundamental theorem of calculus-1, local version. If `f` has a finite limit `c` almost surely at
`l'`, where `(l, l')` is an `FTC_filter` pair around `a`, then
`∫ x in u..v, f x ∂μ = (v - u) • c + o (v - u)` as both `u` and `v` tend to `l`. -/
lemma integral_sub_linear_is_o_of_tendsto_ae [FTC_filter a l l']
  (hfm : measurable_at_filter f l') (hf : tendsto f (l' ⊓ volume.ae) (𝓝 c))
  {u v : β → ℝ} (hu : tendsto u lt l) (hv : tendsto v lt l) :
  is_o (λ t, (∫ x in u t..v t, f x) - (v t - u t) • c) (v - u) lt :=
by simpa [integral_const] using measure_integral_sub_linear_is_o_of_tendsto_ae hfm hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair around
`a`, and `(lb, lb')` is an `FTC_filter` pair around `b`, and `f` has finite limits `ca` and `cb`
almost surely at `la'` and `lb'`, respectively, then
`(∫ x in va..vb, f x) - ∫ x in ua..ub, f x = (vb - ub) • cb - (va - ua) • ca +
  o(∥va - ua∥ + ∥vb - ub∥)` as `ua` and `va` tend to `la` while `ub` and `vb` tend to `lb`.

This lemma could've been formulated using `has_strict_fderiv_at_filter` if we had this
definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae
  (hab : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f la') (hmeas_b : measurable_at_filter f lb')
  (ha_lim : tendsto f (la' ⊓ volume.ae) (𝓝 ca)) (hb_lim : tendsto f (lb' ⊓ volume.ae) (𝓝 cb))
  (hua : tendsto ua lt la) (hva : tendsto va lt la)
  (hub : tendsto ub lt lb) (hvb : tendsto vb lt lb) :
  is_o (λ t, (∫ x in va t..vb t, f x) - (∫ x in ua t..ub t, f x) -
    ((vb t - ub t) • cb - (va t - ua t) • ca)) (λ t, ∥va t - ua t∥ + ∥vb t - ub t∥) lt :=
by simpa [integral_const]
  using measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae hab hmeas_a hmeas_b
    ha_lim hb_lim hua hva hub hvb

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(lb, lb')` is an `FTC_filter` pair
around `b`, and `f` has a finite limit `c` almost surely at `lb'`, then
`(∫ x in a..v, f x) - ∫ x in a..u, f x = (v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `lb`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right
  (hab : interval_integrable f volume a b) (hmeas : measurable_at_filter f lb')
  (hf : tendsto f (lb' ⊓ volume.ae) (𝓝 c)) (hu : tendsto u lt lb) (hv : tendsto v lt lb) :
  is_o (λ t, (∫ x in a..v t, f x) - (∫ x in a..u t, f x) - (v t - u t) • c) (v - u) lt :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hab hmeas hf hu hv

/-- Fundamental theorem of calculus-1, strict differentiability at filter in both endpoints.
If `f` is a measurable function integrable on `a..b`, `(la, la')` is an `FTC_filter` pair
around `a`, and `f` has a finite limit `c` almost surely at `la'`, then
`(∫ x in v..b, f x) - ∫ x in u..b, f x = -(v - u) • c + o(∥v - u∥)` as `u` and `v` tend to `la`.

This lemma could've been formulated using `has_strict_deriv_at_filter` if we had this definition. -/
lemma integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left
  (hab : interval_integrable f volume a b) (hmeas : measurable_at_filter f la')
  (hf : tendsto f (la' ⊓ volume.ae) (𝓝 c)) (hu : tendsto u lt la) (hv : tendsto v lt la) :
  is_o (λ t, (∫ x in v t..b, f x) - (∫ x in u t..b, f x) + (v t - u t) • c) (v - u) lt :=
by simpa only [integral_const, smul_eq_mul, mul_one] using
  measure_integral_sub_integral_sub_linear_is_o_of_tendsto_ae_left hab hmeas hf hu hv

open continuous_linear_map (fst snd smul_right sub_apply smul_right_apply coe_fst' coe_snd' map_sub)

/-!
#### Strict differentiability

In this section we prove that for a measurable function `f` integrable on `a..b`,

* `integral_has_strict_fderiv_at_of_tendsto_ae`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)` in the sense of strict differentiability
  provided that `f` tends to `ca` and `cb` almost surely as `x` tendsto to `a` and `b`,
  respectively;

* `integral_has_strict_fderiv_at`: the function `(u, v) ↦ ∫ x in u..v, f x` has
  derivative `(u, v) ↦ v • f b - u • f a` at `(a, b)` in the sense of strict differentiability
  provided that `f` is continuous at `a` and `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_right`: the function `u ↦ ∫ x in a..u, f x` has
  derivative `c` at `b` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `b`;

* `integral_has_strict_deriv_at_right`: the function `u ↦ ∫ x in a..u, f x` has derivative `f b` at
  `b` in the sense of strict differentiability provided that `f` is continuous at `b`;

* `integral_has_strict_deriv_at_of_tendsto_ae_left`: the function `u ↦ ∫ x in u..b, f x` has
  derivative `-c` at `a` in the sense of strict differentiability provided that `f` tends to `c`
  almost surely as `x` tends to `a`;

* `integral_has_strict_deriv_at_left`: the function `u ↦ ∫ x in u..b, f x` has derivative `-f a` at
  `a` in the sense of strict differentiability provided that `f` is continuous at `a`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`
in the sense of strict differentiability. -/
lemma integral_has_strict_fderiv_at_of_tendsto_ae
  (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f (𝓝 a)) (hmeas_b : measurable_at_filter f (𝓝 b))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  has_strict_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (a, b) :=
begin
  have := integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf hmeas_a hmeas_b ha hb
    ((continuous_fst.comp continuous_snd).tendsto ((a, b), (a, b)))
    ((continuous_fst.comp continuous_fst).tendsto ((a, b), (a, b)))
    ((continuous_snd.comp continuous_snd).tendsto ((a, b), (a, b)))
    ((continuous_snd.comp continuous_fst).tendsto ((a, b), (a, b))),
  refine (this.congr_left _).trans_is_O _,
  { intro x, simp [sub_smul] },
  { exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left }
end

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)` in the sense of strict differentiability. -/
lemma integral_has_strict_fderiv_at
  (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f (𝓝 a)) (hmeas_b : measurable_at_filter f (𝓝 b))
  (ha : continuous_at f a) (hb : continuous_at f b) :
  has_strict_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b
  (ha.mono_left inf_le_left) (hb.mono_left inf_le_left)

/-- **First Fundamental Theorem of Calculus**: if `f : ℝ → E` is integrable on `a..b` and `f x` has
a finite limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b` in
the sense of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 b))
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : has_strict_deriv_at (λ u, ∫ x in a..u, f x) c b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb continuous_at_snd
  continuous_at_fst

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b` in the sense of strict
differentiability. -/
lemma integral_has_strict_deriv_at_right
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 b))
  (hb : continuous_at f b) : has_strict_deriv_at (λ u, ∫ x in a..u, f x) (f b) b :=
integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a` in the sense
of strict differentiability. -/
lemma integral_has_strict_deriv_at_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 a))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : has_strict_deriv_at (λ u, ∫ x in u..b, f x) (-c) a :=
by simpa only [← integral_symm]
  using (integral_has_strict_deriv_at_of_tendsto_ae_right hf.symm hmeas ha).neg

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a` in the sense of strict
differentiability. -/
lemma integral_has_strict_deriv_at_left
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 a))
  (ha : continuous_at f a) : has_strict_deriv_at (λ u, ∫ x in u..b, f x) (-f a) a :=
by simpa only [← integral_symm] using (integral_has_strict_deriv_at_right hf.symm hmeas ha).neg

/-!
#### Fréchet differentiability

In this subsection we restate results from the previous subsection in terms of `has_fderiv_at`,
`has_deriv_at`, `fderiv`, and `deriv`.
-/

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then
`(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca` at `(a, b)`. -/
lemma integral_has_fderiv_at_of_tendsto_ae (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f (𝓝 a)) (hmeas_b : measurable_at_filter f (𝓝 b))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  has_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (a, b) :=
(integral_has_strict_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).has_fderiv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `(u, v) ↦ ∫ x in u..v, f x` has derivative `(u, v) ↦ v • cb - u • ca`
at `(a, b)`. -/
lemma integral_has_fderiv_at (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f (𝓝 a)) (hmeas_b : measurable_at_filter f (𝓝 b))
  (ha : continuous_at f a) (hb : continuous_at f b) :
  has_fderiv_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (a, b) :=
(integral_has_strict_fderiv_at hf hmeas_a hmeas_b ha hb).has_fderiv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has finite
limits `ca` and `cb` almost surely as `x` tends to `a` and `b`, respectively, then `fderiv`
derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦ v • cb - u • ca`. -/
lemma fderiv_integral_of_tendsto_ae (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f (𝓝 a)) (hmeas_b : measurable_at_filter f (𝓝 b))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 cb)) :
  fderiv ℝ (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x) (a, b) =
    (snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca :=
(integral_has_fderiv_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a` and `b`, then `fderiv` derivative of `(u, v) ↦ ∫ x in u..v, f x` at `(a, b)` equals `(u, v) ↦
v • cb - u • ca`. -/
lemma fderiv_integral (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f (𝓝 a)) (hmeas_b : measurable_at_filter f (𝓝 b))
  (ha : continuous_at f a) (hb : continuous_at f b) :
  fderiv ℝ (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x) (a, b) =
    (snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a) :=
(integral_has_fderiv_at hf hmeas_a hmeas_b ha hb).fderiv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `c` at `b`. -/
lemma integral_has_deriv_at_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 b))
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : has_deriv_at (λ u, ∫ x in a..u, f x) c b :=
(integral_has_strict_deriv_at_of_tendsto_ae_right hf hmeas hb).has_deriv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then `u ↦ ∫ x in a..u, f x` has derivative `f b` at `b`. -/
lemma integral_has_deriv_at_right
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 b))
  (hb : continuous_at f b) : has_deriv_at (λ u, ∫ x in a..u, f x) (f b) b :=
(integral_has_strict_deriv_at_right hf hmeas hb).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_integral_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 b))
  (hb : tendsto f (𝓝 b ⊓ volume.ae) (𝓝 c)) : deriv (λ u, ∫ x in a..u, f x) b = c :=
(integral_has_deriv_at_of_tendsto_ae_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `b`, then the derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
lemma deriv_integral_right
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 b))
  (hb : continuous_at f b) :
  deriv (λ u, ∫ x in a..u, f x) b = f b :=
(integral_has_deriv_at_right hf hmeas hb).deriv

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-c` at `a`. -/
lemma integral_has_deriv_at_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 a))
  (ha : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : has_deriv_at (λ u, ∫ x in u..b, f x) (-c) a :=
(integral_has_strict_deriv_at_of_tendsto_ae_left hf hmeas ha).has_deriv_at

/-- Fundamental theorem of calculus-1: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then `u ↦ ∫ x in u..b, f x` has derivative `-f a` at `a`. -/
lemma integral_has_deriv_at_left
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 a))
  (ha : continuous_at f a) :
  has_deriv_at (λ u, ∫ x in u..b, f x) (-f a) a :=
(integral_has_strict_deriv_at_left hf hmeas ha).has_deriv_at

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` has a finite
limit `c` almost surely at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
lemma deriv_integral_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 a))
  (hb : tendsto f (𝓝 a ⊓ volume.ae) (𝓝 c)) : deriv (λ u, ∫ x in u..b, f x) a = -c :=
(integral_has_deriv_at_of_tendsto_ae_left hf hmeas hb).deriv

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f` is continuous
at `a`, then the derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
lemma deriv_integral_left
  (hf : interval_integrable f volume a b) (hmeas : measurable_at_filter f (𝓝 a))
  (hb : continuous_at f a) :
  deriv (λ u, ∫ x in u..b, f x) a = -f a :=
(integral_has_deriv_at_left hf hmeas hb).deriv

/-!
#### One-sided derivatives
-/

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • cb - u • ca` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to `ca`
and `cb` almost surely at the filters `la` and `lb` from the following table.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
lemma integral_has_fderiv_within_at_of_tendsto_ae
  (hf : interval_integrable f volume a b)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (hmeas_a : measurable_at_filter f la) (hmeas_b : measurable_at_filter f lb)
  (ha : tendsto f (la ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (lb ⊓ volume.ae) (𝓝 cb)) :
  has_fderiv_within_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) (s ×ˢ t) (a, b) :=
begin
  rw [has_fderiv_within_at, nhds_within_prod_eq],
  have := integral_sub_integral_sub_linear_is_o_of_tendsto_ae hf hmeas_a hmeas_b ha hb
    (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[s] a)) tendsto_fst
    (tendsto_const_pure.mono_right FTC_filter.pure_le : tendsto _ _ (𝓝[t] b)) tendsto_snd,
  refine (this.congr_left _).trans_is_O _,
  { intro x, simp [sub_smul] },
  { exact is_O_fst_prod.norm_left.add is_O_snd_prod.norm_left }
end

/-- Let `f` be a measurable function integrable on `a..b`. The function `(u, v) ↦ ∫ x in u..v, f x`
has derivative `(u, v) ↦ v • f b - u • f a` within `s × t` at `(a, b)`, where
`s ∈ {Iic a, {a}, Ici a, univ}` and `t ∈ {Iic b, {b}, Ici b, univ}` provided that `f` tends to
`f a` and `f b` at the filters `la` and `lb` from the following table. In most cases this assumption
is definitionally equal `continuous_at f _` or `continuous_within_at f _ _`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
lemma integral_has_fderiv_within_at
  (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f la) (hmeas_b : measurable_at_filter f lb)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f la (𝓝 $ f a)) (hb : tendsto f lb (𝓝 $ f b)) :
  has_fderiv_within_at (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x)
    ((snd ℝ ℝ ℝ).smul_right (f b) - (fst ℝ ℝ ℝ).smul_right (f a)) (s ×ˢ t) (a, b) :=
integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b (ha.mono_left inf_le_left)
  (hb.mono_left inf_le_left)

/-- An auxiliary tactic closing goals `unique_diff_within_at ℝ s a` where
`s ∈ {Iic a, Ici a, univ}`. -/
meta def unique_diff_within_at_Ici_Iic_univ : tactic unit :=
`[apply_rules [unique_diff_on.unique_diff_within_at, unique_diff_on_Ici, unique_diff_on_Iic,
  left_mem_Ici, right_mem_Iic, unique_diff_within_at_univ]]

/-- Let `f` be a measurable function integrable on `a..b`. Choose `s ∈ {Iic a, Ici a, univ}`
and `t ∈ {Iic b, Ici b, univ}`. Suppose that `f` tends to `ca` and `cb` almost surely at the filters
`la` and `lb` from the table below. Then `fderiv_within ℝ (λ p, ∫ x in p.1..p.2, f x) (s ×ˢ t)`
is equal to `(u, v) ↦ u • cb - v • ca`.

| `s`     | `la`     | `t`     | `lb`     |
| ------- | ----     | ---     | ----     |
| `Iic a` | `𝓝[≤] a` | `Iic b` | `𝓝[≤] b` |
| `Ici a` | `𝓝[>] a` | `Ici b` | `𝓝[>] b` |
| `{a}`   | `⊥`      | `{b}`   | `⊥`      |
| `univ`  | `𝓝 a`    | `univ`  | `𝓝 b`    |
-/
lemma fderiv_within_integral_of_tendsto_ae
  (hf : interval_integrable f volume a b)
  (hmeas_a : measurable_at_filter f la) (hmeas_b : measurable_at_filter f lb)
  {s t : set ℝ} [FTC_filter a (𝓝[s] a) la] [FTC_filter b (𝓝[t] b) lb]
  (ha : tendsto f (la ⊓ volume.ae) (𝓝 ca)) (hb : tendsto f (lb ⊓ volume.ae) (𝓝 cb))
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ)
  (ht : unique_diff_within_at ℝ t b . unique_diff_within_at_Ici_Iic_univ) :
  fderiv_within ℝ (λ p : ℝ × ℝ, ∫ x in p.1..p.2, f x) (s ×ˢ t) (a, b) =
    ((snd ℝ ℝ ℝ).smul_right cb - (fst ℝ ℝ ℝ).smul_right ca) :=
(integral_has_fderiv_within_at_of_tendsto_ae hf hmeas_a hmeas_b ha hb).fderiv_within $ hs.prod ht

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left,
then `u ↦ ∫ x in a..u, f x` has right (resp., left) derivative `c` at `b`. -/
lemma integral_has_deriv_within_at_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas : measurable_at_filter f (𝓝[t] b)) (hb : tendsto f (𝓝[t] b ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) c s b :=
integral_sub_integral_sub_linear_is_o_of_tendsto_ae_right hf hmeas hb
  (tendsto_const_pure.mono_right FTC_filter.pure_le) tendsto_id

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `b`, then `u ↦ ∫ x in a..u, f x` has left (resp., right)
derivative `f b` at `b`. -/
lemma integral_has_deriv_within_at_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas : measurable_at_filter f (𝓝[t] b)) (hb : continuous_within_at f t b) :
  has_deriv_within_at (λ u, ∫ x in a..u, f x) (f b) s b :=
integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas (hb.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `b` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in a..u, f x` at `b` equals `c`. -/
lemma deriv_within_integral_of_tendsto_ae_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas: measurable_at_filter f (𝓝[t] b)) (hb : tendsto f (𝓝[t] b ⊓ volume.ae) (𝓝 c))
  (hs : unique_diff_within_at ℝ s b . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in a..u, f x) s b = c :=
(integral_has_deriv_within_at_of_tendsto_ae_right hf hmeas hb).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `b`, then the right (resp., left) derivative of
`u ↦ ∫ x in a..u, f x` at `b` equals `f b`. -/
lemma deriv_within_integral_right
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter b (𝓝[s] b) (𝓝[t] b)]
  (hmeas : measurable_at_filter f (𝓝[t] b)) (hb : continuous_within_at f t b)
  (hs : unique_diff_within_at ℝ s b . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in a..u, f x) s b = f b :=
(integral_has_deriv_within_at_right hf hmeas hb).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left,
then `u ↦ ∫ x in u..b, f x` has right (resp., left) derivative `-c` at `a`. -/
lemma integral_has_deriv_within_at_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : measurable_at_filter f (𝓝[t] a)) (ha : tendsto f (𝓝[t] a ⊓ volume.ae) (𝓝 c)) :
  has_deriv_within_at (λ u, ∫ x in u..b, f x) (-c) s a :=
by { simp only [integral_symm b],
  exact (integral_has_deriv_within_at_of_tendsto_ae_right hf.symm hmeas ha).neg }

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
from the left or from the right at `a`, then `u ↦ ∫ x in u..b, f x` has left (resp., right)
derivative `-f a` at `a`. -/
lemma integral_has_deriv_within_at_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : measurable_at_filter f (𝓝[t] a)) (ha : continuous_within_at f t a) :
  has_deriv_within_at (λ u, ∫ x in u..b, f x) (-f a) s a :=
integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas (ha.mono_left inf_le_left)

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` has a finite
limit `c` almost surely as `x` tends to `a` from the right or from the left, then the right
(resp., left) derivative of `u ↦ ∫ x in u..b, f x` at `a` equals `-c`. -/
lemma deriv_within_integral_of_tendsto_ae_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : measurable_at_filter f (𝓝[t] a)) (ha : tendsto f (𝓝[t] a ⊓ volume.ae) (𝓝 c))
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in u..b, f x) s a = -c :=
(integral_has_deriv_within_at_of_tendsto_ae_left hf hmeas ha).deriv_within hs

/-- Fundamental theorem of calculus: if `f : ℝ → E` is integrable on `a..b` and `f x` is continuous
on the right or on the left at `a`, then the right (resp., left) derivative of
`u ↦ ∫ x in u..b, f x` at `a` equals `-f a`. -/
lemma deriv_within_integral_left
  (hf : interval_integrable f volume a b) {s t : set ℝ} [FTC_filter a (𝓝[s] a) (𝓝[t] a)]
  (hmeas : measurable_at_filter f (𝓝[t] a)) (ha : continuous_within_at f t a)
  (hs : unique_diff_within_at ℝ s a . unique_diff_within_at_Ici_Iic_univ) :
  deriv_within (λ u, ∫ x in u..b, f x) s a = -f a :=
(integral_has_deriv_within_at_left hf hmeas ha).deriv_within hs

/-- The integral of a continuous function is differentiable on a real set `s`. -/
theorem differentiable_on_integral_of_continuous {s : set ℝ}
  (hintg : ∀ x ∈ s, interval_integrable f volume a x) (hcont : continuous f) :
  differentiable_on ℝ (λ u, ∫ x in a..u, f x) s :=
λ y hy, (integral_has_deriv_at_right (hintg y hy)
  hcont.measurable.ae_measurable.measurable_at_filter
    hcont.continuous_at) .differentiable_at.differentiable_within_at

/-!
### Fundamental theorem of calculus, part 2

This section contains theorems pertaining to FTC-2 for interval integrals, i.e., the assertion
that `∫ x in a..b, f' x = f b - f a` under suitable assumptions.

The most classical version of this theorem assumes that `f'` is continuous. However, this is
unnecessarily strong: the result holds if `f'` is just integrable. We prove the strong version,
following [Rudin, *Real and Complex Analysis* (Theorem 7.21)][rudin2006real]. The proof is first
given for real-valued functions, and then deduced for functions with a general target space. For
a real-valued function `g`, it suffices to show that `g b - g a ≤ (∫ x in a..b, g' x) + ε` for all
positive `ε`. To prove this, choose a lower-semicontinuous function `G'` with `g' < G'` and with
integral close to that of `g'` (its existence is guaranteed by the Vitali-Carathéodory theorem).
It satisfies `g t - g a ≤ ∫ x in a..t, G' x` for all `t ∈ [a, b]`: this inequality holds at `a`,
and if it holds at `t` then it holds for `u` close to `t` on its right, as the left hand side
increases by `g u - g t ∼ (u -t) g' t`, while the right hand side increases by
`∫ x in t..u, G' x` which is roughly at least `∫ x in t..u, G' t = (u - t) G' t`, by lower
semicontinuity. As  `g' t < G' t`, this gives the conclusion. One can therefore push progressively
this inequality to the right until the point `b`, where it gives the desired conclusion.
-/

variables {g' g : ℝ → ℝ}

/-- Hard part of FTC-2 for integrable derivatives, real-valued functions: one has
`g b - g a ≤ ∫ y in a..b, g' y`.
Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`. -/
lemma sub_le_integral_of_has_deriv_right_of_le (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ico a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (g'int : integrable_on g' (Icc a b)) :
  g b - g a ≤ ∫ y in a..b, g' y :=
begin
  refine le_of_forall_pos_le_add (λ ε εpos, _),
  -- Bound from above `g'` by a lower-semicontinuous function `G'`.
  rcases exists_lt_lower_semicontinuous_integral_lt g' g'int εpos with
    ⟨G', g'_lt_G', G'cont, G'int, G'lt_top, hG'⟩,
  -- we will show by "induction" that `g t - g a ≤ ∫ u in a..t, G' u` for all `t ∈ [a, b]`.
  set s := {t | g t - g a ≤ ∫ u in a..t, (G' u).to_real} ∩ Icc a b,
  -- the set `s` of points where this property holds is closed.
  have s_closed : is_closed s,
  { have : continuous_on (λ t, (g t - g a, ∫ u in a..t, (G' u).to_real)) (Icc a b),
    { rw ← interval_of_le hab at G'int ⊢ hcont,
      exact (hcont.sub continuous_on_const).prod (continuous_on_primitive_interval G'int) },
    simp only [s, inter_comm],
    exact this.preimage_closed_of_closed is_closed_Icc order_closed_topology.is_closed_le' },
  have main : Icc a b ⊆ {t | g t - g a ≤ ∫ u in a..t, (G' u).to_real },
  { -- to show that the set `s` is all `[a, b]`, it suffices to show that any point `t` in `s`
    -- with `t < b` admits another point in `s` slightly to its right
    -- (this is a sort of real induction).
    apply s_closed.Icc_subset_of_forall_exists_gt
      (by simp only [integral_same, mem_set_of_eq, sub_self]) (λ t ht v t_lt_v, _),
    obtain ⟨y, g'_lt_y', y_lt_G'⟩ : ∃ (y : ℝ), (g' t : ereal) < y ∧ (y : ereal) < G' t :=
      ereal.lt_iff_exists_real_btwn.1 (g'_lt_G' t),
    -- bound from below the increase of `∫ x in a..u, G' x` on the right of `t`, using the lower
    -- semicontinuity of `G'`.
    have I1 : ∀ᶠ u in 𝓝[>] t, (u - t) * y ≤ ∫ w in t..u, (G' w).to_real,
    { have B : ∀ᶠ u in 𝓝 t, (y : ereal) < G' u :=
        G'cont.lower_semicontinuous_at _ _ y_lt_G',
      rcases mem_nhds_iff_exists_Ioo_subset.1 B with ⟨m, M, ⟨hm, hM⟩, H⟩,
      have : Ioo t (min M b) ∈ 𝓝[>] t := mem_nhds_within_Ioi_iff_exists_Ioo_subset.2
        ⟨min M b, by simp only [hM, ht.right.right, lt_min_iff, mem_Ioi, and_self], subset.refl _⟩,
      filter_upwards [this] with u hu,
      have I : Icc t u ⊆ Icc a b := Icc_subset_Icc ht.2.1 (hu.2.le.trans (min_le_right _ _)),
      calc (u - t) * y = ∫ v in Icc t u, y :
        by simp only [hu.left.le, measure_theory.integral_const, algebra.id.smul_eq_mul, sub_nonneg,
                      measurable_set.univ, real.volume_Icc, measure.restrict_apply, univ_inter,
                      ennreal.to_real_of_real]
      ... ≤ ∫ w in t..u, (G' w).to_real :
      begin
        rw [interval_integral.integral_of_le hu.1.le, ← integral_Icc_eq_integral_Ioc],
        apply set_integral_mono_ae_restrict,
        { simp only [integrable_on_const, real.volume_Icc, ennreal.of_real_lt_top, or_true] },
        { exact integrable_on.mono_set G'int I },
        { have C1 : ∀ᵐ (x : ℝ) ∂volume.restrict (Icc t u), G' x < ⊤ :=
            ae_mono (measure.restrict_mono I le_rfl) G'lt_top,
          have C2 : ∀ᵐ (x : ℝ) ∂volume.restrict (Icc t u), x ∈ Icc t u :=
            ae_restrict_mem measurable_set_Icc,
          filter_upwards [C1, C2] with x G'x hx,
          apply ereal.coe_le_coe_iff.1,
          have : x ∈ Ioo m M, by simp only [hm.trans_le hx.left,
            (hx.right.trans_lt hu.right).trans_le (min_le_left M b), mem_Ioo, and_self],
          convert le_of_lt (H this),
          exact ereal.coe_to_real G'x.ne (ne_bot_of_gt (g'_lt_G' x)) }
      end },
    -- bound from above the increase of `g u - g a` on the right of `t`, using the derivative at `t`
    have I2 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ (u - t) * y,
    { have g'_lt_y : g' t < y := ereal.coe_lt_coe_iff.1 g'_lt_y',
      filter_upwards [(hderiv t ⟨ht.2.1, ht.2.2⟩).limsup_slope_le'
        (not_mem_Ioi.2 le_rfl) g'_lt_y, self_mem_nhds_within] with u hu t_lt_u,
      have := mul_le_mul_of_nonneg_left hu.le (sub_pos.2 t_lt_u).le,
      rwa [← smul_eq_mul, sub_smul_slope] at this },
    -- combine the previous two bounds to show that `g u - g a` increases less quickly than
    -- `∫ x in a..u, G' x`.
    have I3 : ∀ᶠ u in 𝓝[>] t, g u - g t ≤ ∫ w in t..u, (G' w).to_real,
    { filter_upwards [I1, I2] with u hu1 hu2 using hu2.trans hu1, },
    have I4 : ∀ᶠ u in 𝓝[>] t, u ∈ Ioc t (min v b),
    { refine mem_nhds_within_Ioi_iff_exists_Ioc_subset.2 ⟨min v b, _, subset.refl _⟩,
      simp only [lt_min_iff, mem_Ioi],
      exact ⟨t_lt_v, ht.2.2⟩ },
    -- choose a point `x` slightly to the right of `t` which satisfies the above bound
    rcases (I3.and I4).exists with ⟨x, hx, h'x⟩,
    -- we check that it belongs to `s`, essentially by construction
    refine ⟨x, _, Ioc_subset_Ioc le_rfl (min_le_left _ _) h'x⟩,
    calc g x - g a = (g t - g a) + (g x - g t) : by abel
    ... ≤ (∫ w in a..t, (G' w).to_real) + ∫ w in t..x, (G' w).to_real : add_le_add ht.1 hx
    ... = ∫ w in a..x, (G' w).to_real :
    begin
      apply integral_add_adjacent_intervals,
      { rw interval_integrable_iff_integrable_Ioc_of_le ht.2.1,
        exact integrable_on.mono_set G'int
          (Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2.2.le)) },
      { rw interval_integrable_iff_integrable_Ioc_of_le h'x.1.le,
        apply integrable_on.mono_set G'int,
        refine Ioc_subset_Icc_self.trans (Icc_subset_Icc ht.2.1 (h'x.2.trans (min_le_right _ _))) }
    end },
  -- now that we know that `s` contains `[a, b]`, we get the desired result by applying this to `b`.
  calc g b - g a ≤ ∫ y in a..b, (G' y).to_real : main (right_mem_Icc.2 hab)
  ... ≤ (∫ y in a..b, g' y) + ε :
    begin
      convert hG'.le;
      { rw interval_integral.integral_of_le hab,
        simp only [integral_Icc_eq_integral_Ioc', real.volume_singleton] },
    end
end

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`. -/
lemma integral_le_sub_of_has_deriv_right_of_le (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ico a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (g'int : integrable_on g' (Icc a b)) :
  ∫ y in a..b, g' y ≤ g b - g a :=
begin
  rw ← neg_le_neg_iff,
  convert sub_le_integral_of_has_deriv_right_of_le hab hcont.neg (λ x hx, (hderiv x hx).neg)
    g'int.neg,
  { abel },
  { simp only [integral_neg] }
end

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`: real version -/
lemma integral_eq_sub_of_has_deriv_right_of_le_real (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ico a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (g'int : integrable_on g' (Icc a b)) :
  ∫ y in a..b, g' y = g b - g a :=
le_antisymm
  (integral_le_sub_of_has_deriv_right_of_le hab hcont hderiv g'int)
  (sub_le_integral_of_has_deriv_right_of_le hab hcont hderiv g'int)

/-- Auxiliary lemma in the proof of `integral_eq_sub_of_has_deriv_right_of_le`: real version, not
requiring differentiability as the left endpoint of the interval. Follows from
`integral_eq_sub_of_has_deriv_right_of_le_real` together with a continuity argument. -/
lemma integral_eq_sub_of_has_deriv_right_of_le_real' (hab : a ≤ b)
  (hcont : continuous_on g (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at g (g' x) (Ioi x) x)
  (g'int : integrable_on g' (Icc a b)) :
  ∫ y in a..b, g' y = g b - g a :=
begin
  obtain rfl|a_lt_b := hab.eq_or_lt, { simp },
  set s := {t | ∫ u in t..b, g' u = g b - g t} ∩ Icc a b,
  have s_closed : is_closed s,
  { have : continuous_on (λ t, (∫ u in t..b, g' u, g b - g t)) (Icc a b),
    { rw ← interval_of_le hab at ⊢ hcont g'int,
      exact (continuous_on_primitive_interval_left g'int).prod (continuous_on_const.sub hcont) },
    simp only [s, inter_comm],
    exact this.preimage_closed_of_closed is_closed_Icc is_closed_diagonal, },
  have A : closure (Ioc a b) ⊆ s,
  { apply s_closed.closure_subset_iff.2,
    assume t ht,
    refine ⟨_, ⟨ht.1.le, ht.2⟩⟩,
    exact integral_eq_sub_of_has_deriv_right_of_le_real ht.2
      (hcont.mono (Icc_subset_Icc ht.1.le le_rfl))
      (λ x hx, hderiv x ⟨ht.1.trans_le hx.1, hx.2⟩)
      (g'int.mono_set (Icc_subset_Icc ht.1.le le_rfl)) },
  rw closure_Ioc a_lt_b.ne at A,
  exact (A (left_mem_Icc.2 hab)).1,
end

variable {f' : ℝ → E}

/-- **Fundamental theorem of calculus-2**: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`)
  and has a right derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`,
  then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right_of_le (hab : a ≤ b) (hcont : continuous_on f (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_within_at f (f' x) (Ioi x) x)
  (f'int : interval_integrable f' volume a b) :
  ∫ y in a..b, f' y = f b - f a :=
begin
  refine (normed_space.eq_iff_forall_dual_eq ℝ).2 (λ g, _),
  rw [← g.interval_integral_comp_comm f'int, g.map_sub],
  exact integral_eq_sub_of_has_deriv_right_of_le_real' hab (g.continuous.comp_continuous_on hcont)
    (λ x hx, g.has_fderiv_at.comp_has_deriv_within_at x (hderiv x hx))
    (g.integrable_comp ((interval_integrable_iff_integrable_Icc_of_le hab).1 f'int))
end

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` and
  has a right derivative at `f' x` for all `x` in `[a, b)`, and `f'` is integrable on `[a, b]` then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_right (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hint : interval_integrable f' volume a b) :
  ∫ y in a..b, f' y = f b - f a :=
begin
  cases le_total a b with hab hab,
  { simp only [interval_of_le, min_eq_left, max_eq_right, hab] at hcont hderiv hint,
    apply integral_eq_sub_of_has_deriv_right_of_le hab hcont hderiv hint },
  { simp only [interval_of_ge, min_eq_right, max_eq_left, hab] at hcont hderiv,
    rw [integral_symm, integral_eq_sub_of_has_deriv_right_of_le hab hcont hderiv hint.symm,
        neg_sub] }
end

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is continuous on `[a, b]` (where `a ≤ b`) and
  has a derivative at `f' x` for all `x` in `(a, b)`, and `f'` is integrable on `[a, b]`, then
  `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at_of_le (hab : a ≤ b)
  (hcont : continuous_on f (Icc a b))
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hint : interval_integrable f' volume a b) :
  ∫ y in a..b, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_right_of_le hab hcont (λ x hx, (hderiv x hx).has_deriv_within_at) hint

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` has a derivative at `f' x` for all `x` in
  `[a, b]` and `f'` is integrable on `[a, b]`, then `∫ y in a..b, f' y` equals `f b - f a`. -/
theorem integral_eq_sub_of_has_deriv_at
  (hderiv : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (hint : interval_integrable f' volume a b) :
  ∫ y in a..b, f' y = f b - f a :=
integral_eq_sub_of_has_deriv_right (has_deriv_at.continuous_on hderiv)
  (λ x hx, (hderiv _ (mem_Icc_of_Ioo hx)).has_deriv_within_at) hint

theorem integral_eq_sub_of_has_deriv_at_of_tendsto (hab : a < b) {fa fb}
  (hderiv : ∀ x ∈ Ioo a b, has_deriv_at f (f' x) x) (hint : interval_integrable f' volume a b)
  (ha : tendsto f (𝓝[>] a) (𝓝 fa)) (hb : tendsto f (𝓝[<] b) (𝓝 fb)) :
  ∫ y in a..b, f' y = fb - fa :=
begin
  set F : ℝ → E := update (update f a fa) b fb,
  have Fderiv : ∀ x ∈ Ioo a b, has_deriv_at F (f' x) x,
  { refine λ x hx, (hderiv x hx).congr_of_eventually_eq _,
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with _ hy, simp only [F],
    rw [update_noteq hy.2.ne, update_noteq hy.1.ne'], },
  have hcont : continuous_on F (Icc a b),
  { rw [continuous_on_update_iff, continuous_on_update_iff, Icc_diff_right, Ico_diff_left],
    refine ⟨⟨λ z hz, (hderiv z hz).continuous_at.continuous_within_at, _⟩, _⟩,
    { exact λ _, ha.mono_left (nhds_within_mono _ Ioo_subset_Ioi_self) },
    { rintro -,
      refine (hb.congr' _).mono_left (nhds_within_mono _ Ico_subset_Iio_self),
      filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.2 hab)]
        with _ hz using (update_noteq hz.1.ne' _ _).symm } },
  simpa [F, hab.ne, hab.ne'] using integral_eq_sub_of_has_deriv_at_of_le hab.le hcont Fderiv hint
end

/-- Fundamental theorem of calculus-2: If `f : ℝ → E` is differentiable at every `x` in `[a, b]` and
  its derivative is integrable on `[a, b]`, then `∫ y in a..b, deriv f y` equals `f b - f a`. -/
theorem integral_deriv_eq_sub (hderiv : ∀ x ∈ interval a b, differentiable_at ℝ f x)
  (hint : interval_integrable (deriv f) volume a b) :
  ∫ y in a..b, deriv f y = f b - f a :=
integral_eq_sub_of_has_deriv_at (λ x hx, (hderiv x hx).has_deriv_at) hint

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
  (hdiff : ∀ x ∈ interval a b, differentiable_at ℝ f x)
  (hcont : continuous_on f' (interval a b)) :
  ∫ y in a..b, f' y = f b - f a :=
begin
  rw [← hderiv, integral_deriv_eq_sub hdiff],
  rw hderiv,
  exact hcont.interval_integrable
end

/-!
### Integration by parts
-/

theorem integral_deriv_mul_eq_sub {u v u' v' : ℝ → ℝ}
  (hu : ∀ x ∈ interval a b, has_deriv_at u (u' x) x)
  (hv : ∀ x ∈ interval a b, has_deriv_at v (v' x) x)
  (hu' : interval_integrable u' volume a b) (hv' : interval_integrable v' volume a b) :
  ∫ x in a..b, u' x * v x + u x * v' x = u b * v b - u a * v a :=
integral_eq_sub_of_has_deriv_at (λ x hx, (hu x hx).mul (hv x hx)) $
  (hu'.mul_continuous_on (has_deriv_at.continuous_on hv)).add
    (hv'.continuous_on_mul ((has_deriv_at.continuous_on hu)))

theorem integral_mul_deriv_eq_deriv_mul {u v u' v' : ℝ → ℝ}
  (hu : ∀ x ∈ interval a b, has_deriv_at u (u' x) x)
  (hv : ∀ x ∈ interval a b, has_deriv_at v (v' x) x)
  (hu' : interval_integrable u' volume a b) (hv' : interval_integrable v' volume a b) :
  ∫ x in a..b, u x * v' x = u b * v b - u a * v a - ∫ x in a..b, v x * u' x :=
begin
  rw [← integral_deriv_mul_eq_sub hu hv hu' hv', ← integral_sub],
  { exact integral_congr (λ x hx, by simp only [mul_comm, add_sub_cancel']) },
  { exact ((hu'.mul_continuous_on (has_deriv_at.continuous_on hv)).add
      (hv'.continuous_on_mul (has_deriv_at.continuous_on hu))) },
  { exact hu'.continuous_on_mul (has_deriv_at.continuous_on hv) },
end

/-!
### Integration by substitution / Change of variables
-/

section smul

/--
Change of variables, general form. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.

We could potentially slightly weaken the conditions, by not requiring that `f'` and `g` are
continuous on the endpoints of these intervals, but in that case we need to additionally assume that
the functions are integrable on that interval.
-/
theorem integral_comp_smul_deriv'' {f f' : ℝ → ℝ} {g : ℝ → E}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g (f '' [a, b])) :
  ∫ x in a..b, f' x • (g ∘ f) x= ∫ u in f a..f b, g u :=
begin
  have h_cont : continuous_on (λ u, ∫ t in f a..f u, g t) [a, b],
  { rw [hf.image_interval] at hg,
    refine (continuous_on_primitive_interval' hg.interval_integrable _).comp hf _,
    { rw [← hf.image_interval], exact mem_image_of_mem f left_mem_interval },
    { rw [← image_subset_iff], exact hf.image_interval.subset } },
  have h_der : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at
    (λ u, ∫ t in f a..f u, g t) (f' x • ((g ∘ f) x)) (Ioi x) x,
  { intros x hx,
    let I := [Inf (f '' [a, b]), Sup (f '' [a, b])],
    have hI : f '' [a, b] = I := hf.image_interval,
    have h2x : f x ∈ I, { rw [← hI], exact mem_image_of_mem f (Ioo_subset_Icc_self hx) },
    have h2g : interval_integrable g volume (f a) (f x),
    { refine (hg.mono $ _).interval_integrable,
      exact hf.surj_on_interval left_mem_interval (Ioo_subset_Icc_self hx) },
    rw [hI] at hg,
    have h3g : measurable_at_filter g (𝓝[I] f x) volume :=
    hg.measurable_at_filter_nhds_within measurable_set_Icc (f x),
    haveI : fact (f x ∈ I) := ⟨h2x⟩,
    have : has_deriv_within_at (λ u, ∫ x in f a..u, g x) (g (f x)) I (f x) :=
    integral_has_deriv_within_at_right h2g h3g (hg (f x) h2x),
    refine (this.scomp x ((hff' x hx).Ioo_of_Ioi hx.2) _).Ioi_of_Ioo hx.2,
    rw ← hI,
    exact (maps_to_image _ _).mono (Ioo_subset_Icc_self.trans $ Icc_subset_Icc_left hx.1.le)
      subset.rfl },
  have h_int : interval_integrable (λ (x : ℝ), f' x • (g ∘ f) x) volume a b :=
  (hf'.smul (hg.comp hf $ subset_preimage_image f _)).interval_integrable,
  simp_rw [integral_eq_sub_of_has_deriv_right h_cont h_der h_int, integral_same, sub_zero],
end

/--
Change of variables. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
Compared to `interval_integral.integral_comp_smul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_smul_deriv' {f f' : ℝ → ℝ} {g : ℝ → E}
  (h : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (interval a b)) (hg : continuous_on g (f '' [a, b])) :
  ∫ x in a..b, f' x • (g ∘ f) x = ∫ x in f a..f b, g x :=
integral_comp_smul_deriv'' (λ x hx, (h x hx).continuous_at.continuous_within_at)
  (λ x hx, (h x $ Ioo_subset_Icc_self hx).has_deriv_within_at) h' hg

/--
Change of variables, most common version. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, f' x • (g ∘ f) x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_smul_deriv {f f' : ℝ → ℝ} {g : ℝ → E}
  (h : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (interval a b)) (hg : continuous g) :
  ∫ x in a..b, f' x • (g ∘ f) x = ∫ x in f a..f b, g x :=
integral_comp_smul_deriv' h h' hg.continuous_on

theorem integral_deriv_comp_smul_deriv' {f f' : ℝ → ℝ} {g g' : ℝ → E}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g [f a, f b])
  (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), has_deriv_within_at g (g' x) (Ioi x) x)
  (hg' : continuous_on g' (f '' [a, b])) :
  ∫ x in a..b, f' x • (g' ∘ f) x = (g ∘ f) b - (g ∘ f) a :=
begin
  rw [integral_comp_smul_deriv'' hf hff' hf' hg',
  integral_eq_sub_of_has_deriv_right hg hgg' (hg'.mono _).interval_integrable],
  exact intermediate_value_interval hf
end

theorem integral_deriv_comp_smul_deriv {f f' : ℝ → ℝ} {g g' : ℝ → E}
  (hf : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (hg : ∀ x ∈ interval a b, has_deriv_at g (g' (f x)) (f x))
  (hf' : continuous_on f' (interval a b)) (hg' : continuous g') :
  ∫ x in a..b, f' x • (g' ∘ f) x = (g ∘ f) b - (g ∘ f) a :=
integral_eq_sub_of_has_deriv_at (λ x hx, (hg x hx).scomp x $ hf x hx)
  (hf'.smul (hg'.comp_continuous_on $ has_deriv_at.continuous_on hf)).interval_integrable

end smul
section mul

/--
Change of variables, general form for scalar functions. If `f` is continuous on `[a, b]` and has
continuous right-derivative `f'` in `(a, b)`, and `g` is continuous on `f '' [a, b]` then we can
substitute `u = f x` to get `∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv'' {f f' g : ℝ → ℝ}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g (f '' [a, b])) :
  ∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u :=
by simpa [mul_comm] using integral_comp_smul_deriv'' hf hff' hf' hg

/--
Change of variables. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous on `f '' [a, b]`, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
Compared to `interval_integral.integral_comp_mul_deriv` we only require that `g` is continuous on
`f '' [a, b]`.
-/
theorem integral_comp_mul_deriv' {f f' g : ℝ → ℝ}
  (h : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (interval a b)) (hg : continuous_on g (f '' [a, b])) :
  ∫ x in a..b, (g ∘ f) x * f' x = ∫ x in f a..f b, g x :=
by simpa [mul_comm] using integral_comp_smul_deriv' h h' hg

/--
Change of variables, most common version. If `f` is has continuous derivative `f'` on `[a, b]`,
and `g` is continuous, then we can substitute `u = f x` to get
`∫ x in a..b, (g ∘ f) x * f' x = ∫ u in f a..f b, g u`.
-/
theorem integral_comp_mul_deriv {f f' g : ℝ → ℝ}
  (h : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (h' : continuous_on f' (interval a b)) (hg : continuous g) :
  ∫ x in a..b, (g ∘ f) x * f' x = ∫ x in f a..f b, g x :=
integral_comp_mul_deriv' h h' hg.continuous_on

theorem integral_deriv_comp_mul_deriv' {f f' g g' : ℝ → ℝ}
  (hf : continuous_on f [a, b])
  (hff' : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ioi x) x)
  (hf' : continuous_on f' [a, b])
  (hg : continuous_on g [f a, f b])
  (hgg' : ∀ x ∈ Ioo (min (f a) (f b)) (max (f a) (f b)), has_deriv_within_at g (g' x) (Ioi x) x)
  (hg' : continuous_on g' (f '' [a, b])) :
  ∫ x in a..b, (g' ∘ f) x * f' x = (g ∘ f) b - (g ∘ f) a :=
by simpa [mul_comm] using integral_deriv_comp_smul_deriv' hf hff' hf' hg hgg' hg'

theorem integral_deriv_comp_mul_deriv {f f' g g' : ℝ → ℝ}
  (hf : ∀ x ∈ interval a b, has_deriv_at f (f' x) x)
  (hg : ∀ x ∈ interval a b, has_deriv_at g (g' (f x)) (f x))
  (hf' : continuous_on f' (interval a b)) (hg' : continuous g') :
  ∫ x in a..b, (g' ∘ f) x * f' x = (g ∘ f) b - (g ∘ f) a :=
by simpa [mul_comm] using integral_deriv_comp_smul_deriv hf hg hf' hg'

end mul

end interval_integral
