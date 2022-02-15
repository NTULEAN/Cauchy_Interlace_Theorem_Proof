/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.metric_space.metric_separated
import measure_theory.constructions.borel_space
import measure_theory.measure.lebesgue
import analysis.special_functions.pow
import topology.metric_space.holder
import data.equiv.list

/-!
# Hausdorff measure and metric (outer) measures

In this file we define the `d`-dimensional Hausdorff measure on an (extended) metric space `X` and
the Hausdorff dimension of a set in an (extended) metric space. Let `μ d δ` be the maximal outer
measure such that `μ d δ s ≤ (emetric.diam s) ^ d` for every set of diameter less than `δ`. Then
the Hausdorff measure `μH[d] s` of `s` is defined as `⨆ δ > 0, μ d δ s`. By Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, this is a Borel measure on `X`.

The value of `μH[d]`, `d > 0`, on a set `s` (measurable or not) is given by
```
μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, emetric.diam (t n) ≤ r), ∑' n, emetric.diam (t n) ^ d
```

For every set `s` for any `d < d'` we have either `μH[d] s = ∞` or `μH[d'] s = 0`, see
`measure_theory.measure.hausdorff_measure_zero_or_top`. In
`topology.metric_space.hausdorff_dimension` we use this fact to define the Hausdorff dimension
`dimH` of a set in an (extended) metric space.

We also define two generalizations of the Hausdorff measure. In one generalization (see
`measure_theory.measure.mk_metric`) we take any function `m (diam s)` instead of `(diam s) ^ d`. In
an even more general definition (see `measure_theory.measure.mk_metric'`) we use any function
of `m : set X → ℝ≥0∞`. Some authors start with a partial function `m` defined only on some sets
`s : set X` (e.g., only on balls or only on measurable sets). This is equivalent to our definition
applied to `measure_theory.extend m`.

We also define a predicate `measure_theory.outer_measure.is_metric` which says that an outer measure
is additive on metric separated pairs of sets: `μ (s ∪ t) = μ s + μ t` provided that
`⨅ (x ∈ s) (y ∈ t), edist x y ≠ 0`. This is the property required for the Caratheodory theorem
`measure_theory.outer_measure.is_metric.borel_le_caratheodory`, so we prove this theorem for any
metric outer measure, then prove that outer measures constructed using `mk_metric'` are metric outer
measures.

## Main definitions

* `measure_theory.outer_measure.is_metric`: an outer measure `μ` is called *metric* if
  `μ (s ∪ t) = μ s + μ t` for any two metric separated sets `s` and `t`. A metric outer measure in a
  Borel extended metric space is guaranteed to satisfy the Caratheodory condition, see
  `measure_theory.outer_measure.is_metric.borel_le_caratheodory`.
* `measure_theory.outer_measure.mk_metric'` and its particular case
  `measure_theory.outer_measure.mk_metric`: a construction of an outer measure that is guaranteed to
  be metric. Both constructions are generalizations of the Hausdorff measure. The same measures
  interpreted as Borel measures are called `measure_theory.measure.mk_metric'` and
  `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure` a.k.a. `μH[d]`: the `d`-dimensional Hausdorff measure.
  There are many definitions of the Hausdorff measure that differ from each other by a
  multiplicative constant. We put
  `μH[d] s = ⨆ r > 0, ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n) (ht : ∀ n, emetric.diam (t n) ≤ r),
    ∑' n, ⨆ (ht : ¬set.subsingleton (t n)), (emetric.diam (t n)) ^ d`,
  see `measure_theory.measure.hausdorff_measure_apply'`. In the most interesting case `0 < d` one
  can omit the `⨆ (ht : ¬set.subsingleton (t n))` part.

## Main statements

### Basic properties

* `measure_theory.outer_measure.is_metric.borel_le_caratheodory`: if `μ` is a metric outer measure
  on an extended metric space `X` (that is, it is additive on pairs of metric separated sets), then
  every Borel set is Caratheodory measurable (hence, `μ` defines an actual
  `measure_theory.measure`). See also `measure_theory.measure.mk_metric`.
* `measure_theory.measure.hausdorff_measure_mono`: `μH[d] s` is an antitone function
  of `d`.
* `measure_theory.measure.hausdorff_measure_zero_or_top`: if `d₁ < d₂`, then for any `s`, either
  `μH[d₂] s = 0` or `μH[d₁] s = ∞`. Together with the previous lemma, this means that `μH[d] s` is
  equal to infinity on some ray `(-∞, D)` and is equal to zero on `(D, +∞)`, where `D` is a possibly
  infinite number called the *Hausdorff dimension* of `s`; `μH[D] s` can be zero, infinity, or
  anything in between.
* `measure_theory.measure.no_atoms_hausdorff`: Hausdorff measure has no atoms.

### Hausdorff measure in `ℝⁿ`

* `measure_theory.hausdorff_measure_pi_real`: for a nonempty `ι`, `μH[card ι]` on `ι → ℝ` equals
  Lebesgue measure.

## Notations

We use the following notation localized in `measure_theory`.

- `μH[d]` : `measure_theory.measure.hausdorff_measure d`

## Implementation notes

There are a few similar constructions called the `d`-dimensional Hausdorff measure. E.g., some
sources only allow coverings by balls and use `r ^ d` instead of `(diam s) ^ d`. While these
construction lead to different Hausdorff measures, they lead to the same notion of the Hausdorff
dimension.

## TODO

* prove that `1`-dimensional Hausdorff measure on `ℝ` equals `volume`;
* prove a similar statement for `ℝ × ℝ`.

## References

* [Herbert Federer, Geometric Measure Theory, Chapter 2.10][Federer1996]

## Tags

Hausdorff measure, measure, metric measure
-/

open_locale nnreal ennreal topological_space big_operators

open emetric set function filter encodable finite_dimensional topological_space

noncomputable theory

variables {ι X Y : Type*} [emetric_space X] [emetric_space Y]

namespace measure_theory

namespace outer_measure

/-!
### Metric outer measures

In this section we define metric outer measures and prove Caratheodory theorem: a metric outer
measure has the Caratheodory property.
-/

/-- We say that an outer measure `μ` in an (e)metric space is *metric* if `μ (s ∪ t) = μ s + μ t`
for any two metric separated sets `s`, `t`. -/
def is_metric (μ : outer_measure X) : Prop :=
∀ (s t : set X), is_metric_separated s t → μ (s ∪ t) = μ s + μ t

namespace is_metric

variables {μ : outer_measure X}

/-- A metric outer measure is additive on a finite set of pairwise metric separated sets. -/
lemma finset_Union_of_pairwise_separated (hm : is_metric μ) {I : finset ι} {s : ι → set X}
  (hI : ∀ (i ∈ I) (j ∈ I), i ≠ j → is_metric_separated (s i) (s j)) :
  μ (⋃ i ∈ I, s i) = ∑ i in I, μ (s i) :=
begin
  classical,
  induction I using finset.induction_on with i I hiI ihI hI, { simp },
  simp only [finset.mem_insert] at hI,
  rw [finset.set_bUnion_insert, hm, ihI, finset.sum_insert hiI],
  exacts [λ i hi j hj hij, (hI i (or.inr hi) j (or.inr hj) hij),
    is_metric_separated.finset_Union_right
      (λ j hj, hI i (or.inl rfl) j (or.inr hj) (ne_of_mem_of_not_mem hj hiI).symm)]
end

/-- Caratheodory theorem. If `m` is a metric outer measure, then every Borel measurable set `t` is
Caratheodory measurable: for any (not necessarily measurable) set `s` we have
`μ (s ∩ t) + μ (s \ t) = μ s`. -/
lemma borel_le_caratheodory (hm : is_metric μ) :
  borel X ≤ μ.caratheodory :=
begin
  rw [borel_eq_generate_from_is_closed],
  refine measurable_space.generate_from_le (λ t ht, μ.is_caratheodory_iff_le.2 $ λ s, _),
  set S : ℕ → set X := λ n, {x ∈ s | (↑n)⁻¹ ≤ inf_edist x t},
  have n0 : ∀ {n : ℕ}, (n⁻¹ : ℝ≥0∞) ≠ 0, from λ n, ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top,
  have Ssep : ∀ n, is_metric_separated (S n) t,
    from λ n, ⟨n⁻¹, n0, λ x hx y hy, hx.2.trans $ inf_edist_le_edist_of_mem hy⟩,
  have Ssep' : ∀ n, is_metric_separated (S n) (s ∩ t),
    from λ n, (Ssep n).mono subset.rfl (inter_subset_right _ _),
  have S_sub : ∀ n, S n ⊆ s \ t,
    from λ n, subset_inter (inter_subset_left _ _) (Ssep n).subset_compl_right,
  have hSs : ∀ n, μ (s ∩ t) + μ (S n) ≤ μ s, from λ n,
  calc μ (s ∩ t) + μ (S n) = μ (s ∩ t ∪ S n) :
    eq.symm $ hm _ _ $ (Ssep' n).symm
  ... ≤ μ (s ∩ t ∪ s \ t)  : by { mono*, exact le_rfl }
  ... = μ s : by rw [inter_union_diff],
  have Union_S : (⋃ n, S n) = s \ t,
  { refine subset.antisymm (Union_subset S_sub) _,
    rintro x ⟨hxs, hxt⟩,
    rw mem_iff_inf_edist_zero_of_closed ht at hxt,
    rcases ennreal.exists_inv_nat_lt hxt with ⟨n, hn⟩,
    exact mem_Union.2 ⟨n, hxs, hn.le⟩ },
  /- Now we have `∀ n, μ (s ∩ t) + μ (S n) ≤ μ s` and we need to prove
  `μ (s ∩ t) + μ (⋃ n, S n) ≤ μ s`. We can't pass to the limit because
  `μ` is only an outer measure. -/
  by_cases htop : μ (s \ t) = ∞,
  { rw [htop, ennreal.add_top, ← htop],
    exact μ.mono (diff_subset _ _) },
  suffices : μ (⋃ n, S n) ≤ ⨆ n, μ (S n),
  calc μ (s ∩ t) + μ (s \ t) = μ (s ∩ t) + μ (⋃ n, S n) :
    by rw Union_S
  ... ≤ μ (s ∩ t) + ⨆ n, μ (S n) :
    add_le_add le_rfl this
  ... = ⨆ n, μ (s ∩ t) + μ (S n) : ennreal.add_supr
  ... ≤ μ s : supr_le hSs,
  /- It suffices to show that `∑' k, μ (S (k + 1) \ S k) ≠ ∞`. Indeed, if we have this,
  then for all `N` we have `μ (⋃ n, S n) ≤ μ (S N) + ∑' k, m (S (N + k + 1) \ S (N + k))`
  and the second term tends to zero, see `outer_measure.Union_nat_of_monotone_of_tsum_ne_top`
  for details. -/
  have : ∀ n, S n ⊆ S (n + 1), from λ n x hx,
    ⟨hx.1, le_trans (ennreal.inv_le_inv.2 $ ennreal.coe_nat_le_coe_nat.2 n.le_succ) hx.2⟩,
  refine (μ.Union_nat_of_monotone_of_tsum_ne_top this _).le, clear this,
  /- While the sets `S (k + 1) \ S k` are not pairwise metric separated, the sets in each
  subsequence `S (2 * k + 1) \ S (2 * k)` and `S (2 * k + 2) \ S (2 * k)` are metric separated,
  so `m` is additive on each of those sequences. -/
  rw [← tsum_even_add_odd ennreal.summable ennreal.summable, ennreal.add_ne_top],
  suffices : ∀ a, (∑' (k : ℕ), μ (S (2 * k + 1 + a) \ S (2 * k + a))) ≠ ∞,
    from ⟨by simpa using this 0, by simpa using this 1⟩,
  refine λ r, ne_top_of_le_ne_top htop _,
  rw [← Union_S, ennreal.tsum_eq_supr_nat, supr_le_iff],
  intro n,
  rw [← hm.finset_Union_of_pairwise_separated],
  { exact μ.mono (Union_subset $ λ i, Union_subset $ λ hi x hx, mem_Union.2 ⟨_, hx.1⟩) },
  suffices : ∀ i  j, i < j → is_metric_separated (S (2 * i + 1 + r)) (s \ S (2 * j + r)),
    from λ i _ j _ hij, hij.lt_or_lt.elim
      (λ h, (this i j h).mono (inter_subset_left _ _) (λ x hx, ⟨hx.1.1, hx.2⟩))
      (λ h, (this j i h).symm.mono  (λ x hx, ⟨hx.1.1, hx.2⟩) (inter_subset_left _ _)),
  intros i j hj,
  have A : ((↑(2 * j + r))⁻¹ : ℝ≥0∞) < (↑(2 * i + 1 + r))⁻¹,
    by { rw [ennreal.inv_lt_inv, ennreal.coe_nat_lt_coe_nat], linarith },
  refine ⟨(↑(2 * i + 1 + r))⁻¹ - (↑(2 * j + r))⁻¹, by simpa using A, λ x hx y hy, _⟩,
  have : inf_edist y t < (↑(2 * j + r))⁻¹, from not_le.1 (λ hle, hy.2 ⟨hy.1, hle⟩),
  rcases inf_edist_lt_iff.mp this with ⟨z, hzt, hyz⟩,
  have hxz : (↑(2 * i + 1 + r))⁻¹ ≤ edist x z, from le_inf_edist.1 hx.2 _ hzt,
  apply ennreal.le_of_add_le_add_right hyz.ne_top,
  refine le_trans _ (edist_triangle _ _ _),
  refine (add_le_add le_rfl hyz.le).trans (eq.trans_le _ hxz),
  rw [tsub_add_cancel_of_le A.le]
end

lemma le_caratheodory [measurable_space X] [borel_space X] (hm : is_metric μ) :
  ‹measurable_space X› ≤ μ.caratheodory :=
by { rw @borel_space.measurable_eq X _ _, exact hm.borel_le_caratheodory }

end is_metric

/-!
### Constructors of metric outer measures

In this section we provide constructors `measure_theory.outer_measure.mk_metric'` and
`measure_theory.outer_measure.mk_metric` and prove that these outer measures are metric outer
measures. We also prove basic lemmas about `map`/`comap` of these measures.
-/

/-- Auxiliary definition for `outer_measure.mk_metric'`: given a function on sets
`m : set X → ℝ≥0∞`, returns the maximal outer measure `μ` such that `μ s ≤ m s`
for any set `s` of diameter at most `r`.-/
def mk_metric'.pre (m : set X → ℝ≥0∞) (r : ℝ≥0∞) :
  outer_measure X :=
bounded_by $ extend (λ s (hs : diam s ≤ r), m s)

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `mk_metric'.pre m r`
over `r > 0`. Equivalently, it is the limit of `mk_metric'.pre m r` as `r` tends to zero from
the right. -/
def mk_metric' (m : set X → ℝ≥0∞) :
  outer_measure X :=
⨆ r > 0, mk_metric'.pre m r

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞` and `r > 0`, let `μ r` be the maximal outer measure such that
`μ s ≤ m (emetric.diam s)` whenever `emetric.diam s < r`. Then
`mk_metric m = ⨆ r > 0, μ r`. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : outer_measure X :=
mk_metric' (λ s, m (diam s))

namespace mk_metric'

variables {m : set X → ℝ≥0∞} {r : ℝ≥0∞} {μ : outer_measure X} {s : set X}

lemma le_pre : μ ≤ pre m r ↔ ∀ s : set X, diam s ≤ r → μ s ≤ m s :=
by simp only [pre, le_bounded_by, extend, le_infi_iff]

lemma pre_le (hs : diam s ≤ r) : pre m r s ≤ m s :=
(bounded_by_le _).trans $ infi_le _ hs

lemma mono_pre (m : set X → ℝ≥0∞) {r r' : ℝ≥0∞} (h : r ≤ r') :
  pre m r' ≤ pre m r :=
le_pre.2 $ λ s hs, pre_le (hs.trans h)

lemma mono_pre_nat (m : set X → ℝ≥0∞) :
  monotone (λ k : ℕ, pre m k⁻¹) :=
λ k l h, le_pre.2 $ λ s hs, pre_le (hs.trans $ by simpa)

lemma tendsto_pre (m : set X → ℝ≥0∞) (s : set X) :
  tendsto (λ r, pre m r s) (𝓝[>] 0) (𝓝 $ mk_metric' m s) :=
begin
  rw [← map_coe_Ioi_at_bot, tendsto_map'_iff],
  simp only [mk_metric', outer_measure.supr_apply, supr_subtype'],
  exact tendsto_at_bot_supr (λ r r' hr, mono_pre _ hr _)
end

lemma tendsto_pre_nat (m : set X → ℝ≥0∞) (s : set X) :
  tendsto (λ n : ℕ, pre m n⁻¹ s) at_top (𝓝 $ mk_metric' m s) :=
begin
  refine (tendsto_pre m s).comp (tendsto_inf.2 ⟨ennreal.tendsto_inv_nat_nhds_zero, _⟩),
  refine tendsto_principal.2 (eventually_of_forall $ λ n, _),
  simp
end

lemma eq_supr_nat (m : set X → ℝ≥0∞) :
  mk_metric' m = ⨆ n : ℕ, mk_metric'.pre m n⁻¹ :=
begin
  ext1 s,
  rw supr_apply,
  refine tendsto_nhds_unique (mk_metric'.tendsto_pre_nat m s)
    (tendsto_at_top_supr $ λ k l hkl, mk_metric'.mono_pre_nat m hkl s)
end

/-- `measure_theory.outer_measure.mk_metric'.pre m r` is a trimmed measure provided that
`m (closure s) = m s` for any set `s`. -/
lemma trim_pre [measurable_space X] [opens_measurable_space X]
  (m : set X → ℝ≥0∞) (hcl : ∀ s, m (closure s) = m s) (r : ℝ≥0∞) :
  (pre m r).trim = pre m r :=
begin
  refine le_antisymm (le_pre.2 $ λ s hs, _) (le_trim _),
  rw trim_eq_infi,
  refine (infi_le_of_le (closure s) $ infi_le_of_le subset_closure $
    infi_le_of_le measurable_set_closure ((pre_le _).trans_eq (hcl _))),
  rwa diam_closure
end

end mk_metric'

/-- An outer measure constructed using `outer_measure.mk_metric'` is a metric outer measure. -/
lemma mk_metric'_is_metric (m : set X → ℝ≥0∞) :
  (mk_metric' m).is_metric :=
begin
  rintros s t ⟨r, r0, hr⟩,
  refine tendsto_nhds_unique_of_eventually_eq
    (mk_metric'.tendsto_pre _ _)
    ((mk_metric'.tendsto_pre _ _).add (mk_metric'.tendsto_pre _ _)) _,
  rw [← pos_iff_ne_zero] at r0,
  filter_upwards [Ioo_mem_nhds_within_Ioi ⟨le_rfl, r0⟩],
  rintro ε ⟨ε0, εr⟩,
  refine bounded_by_union_of_top_of_nonempty_inter _,
  rintro u ⟨x, hxs, hxu⟩ ⟨y, hyt, hyu⟩,
  have : ε < diam u, from εr.trans_le ((hr x hxs y hyt).trans $ edist_le_diam_of_mem hxu hyu),
  exact infi_eq_top.2 (λ h, (this.not_le h).elim)
end

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[≥] 0] c • m₂) :
  (mk_metric m₁ : outer_measure X) ≤ c • mk_metric m₂ :=
begin
  classical,
  rcases (mem_nhds_within_Ici_iff_exists_Ico_subset' ennreal.zero_lt_one).1 hle with ⟨r, hr0, hr⟩,
  refine λ s, le_of_tendsto_of_tendsto (mk_metric'.tendsto_pre _ s)
    (ennreal.tendsto.const_mul (mk_metric'.tendsto_pre _ s) (or.inr hc))
    (mem_of_superset (Ioo_mem_nhds_within_Ioi ⟨le_rfl, hr0⟩) (λ r' hr', _)),
  simp only [mem_set_of_eq, mk_metric'.pre],
  rw [← smul_apply, smul_bounded_by hc],
  refine le_bounded_by.2 (λ t, (bounded_by_le _).trans _) _,
  simp only [smul_eq_mul, pi.smul_apply, extend, infi_eq_if],
  split_ifs with ht ht,
  { apply hr,
    exact ⟨zero_le _, ht.trans_lt hr'.2⟩ },
  { simp [h0] }
end

/-- If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[≥] 0]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[≥] 0] m₂) :
  (mk_metric m₁ : outer_measure X) ≤ mk_metric m₂ :=
by { convert mk_metric_mono_smul ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

lemma isometry_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : isometry f)
  (H : monotone m ∨ surjective f) :
  comap f (mk_metric m) = mk_metric m :=
begin
  simp only [mk_metric, mk_metric', mk_metric'.pre, induced_outer_measure, comap_supr],
  refine supr_congr id surjective_id (λ ε, supr_congr id surjective_id $ λ hε, _),
  rw comap_bounded_by _ (H.imp (λ h_mono, _) id),
  { congr' with s : 1,
    apply extend_congr,
    { simp [hf.ediam_image] },
    { intros, simp [hf.injective.subsingleton_image_iff, hf.ediam_image] } },
  { assume s t hst,
    simp only [extend, le_infi_iff],
    assume ht,
    apply le_trans _ (h_mono (diam_mono hst)),
    simp only [(diam_mono hst).trans ht, le_refl, cinfi_pos] }
end

lemma isometry_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) {f : X → Y} (hf : isometry f)
  (H : monotone m ∨ surjective f) :
  map f (mk_metric m) = restrict (range f) (mk_metric m) :=
by rw [← isometry_comap_mk_metric _ hf H, map_comap]

lemma isometric_comap_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
  comap f (mk_metric m) = mk_metric m :=
isometry_comap_mk_metric _ f.isometry (or.inr f.surjective)

lemma isometric_map_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (f : X ≃ᵢ Y) :
  map f (mk_metric m) = mk_metric m :=
by rw [← isometric_comap_mk_metric _ f, map_comap_of_surjective f.surjective]

lemma trim_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : outer_measure X).trim = mk_metric m :=
begin
  simp only [mk_metric, mk_metric'.eq_supr_nat, trim_supr],
  congr' 1 with n : 1,
  refine mk_metric'.trim_pre _ (λ s, _) _,
  simp
end

lemma le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : outer_measure X)
  (r : ℝ≥0∞) (h0 : 0 < r) (hr : ∀ s, diam s ≤ r → μ s ≤ m (diam s)) :
  μ ≤ mk_metric m :=
le_bsupr_of_le r h0 $ mk_metric'.le_pre.2 $ λ s hs, hr _ hs

end outer_measure

/-!
### Metric measures

In this section we use `measure_theory.outer_measure.to_measure` and theorems about
`measure_theory.outer_measure.mk_metric'`/`measure_theory.outer_measure.mk_metric` to define
`measure_theory.measure.mk_metric'`/`measure_theory.measure.mk_metric`. We also restate some lemmas
about metric outer measures for metric measures.
-/

namespace measure

variables [measurable_space X] [borel_space X]

/-- Given a function `m : set X → ℝ≥0∞`, `mk_metric' m` is the supremum of `μ r`
over `r > 0`, where `μ r` is the maximal outer measure `μ` such that `μ s ≤ m s`
for all `s`. While each `μ r` is an *outer* measure, the supremum is a measure. -/
def mk_metric' (m : set X → ℝ≥0∞) : measure X :=
(outer_measure.mk_metric' m).to_measure (outer_measure.mk_metric'_is_metric _).le_caratheodory

/-- Given a function `m : ℝ≥0∞ → ℝ≥0∞`, `mk_metric m` is the supremum of `μ r` over `r > 0`, where
`μ r` is the maximal outer measure `μ` such that `μ s ≤ m s` for all sets `s` that contain at least
two points. While each `mk_metric'.pre` is an *outer* measure, the supremum is a measure. -/
def mk_metric (m : ℝ≥0∞ → ℝ≥0∞) : measure X :=
(outer_measure.mk_metric m).to_measure (outer_measure.mk_metric'_is_metric _).le_caratheodory

@[simp] lemma mk_metric'_to_outer_measure (m : set X → ℝ≥0∞) :
  (mk_metric' m).to_outer_measure = (outer_measure.mk_metric' m).trim :=
rfl

@[simp] lemma mk_metric_to_outer_measure (m : ℝ≥0∞ → ℝ≥0∞) :
  (mk_metric m : measure X).to_outer_measure = outer_measure.mk_metric m :=
outer_measure.trim_mk_metric m

end measure

lemma outer_measure.coe_mk_metric [measurable_space X] [borel_space X] (m : ℝ≥0∞ → ℝ≥0∞) :
  ⇑(outer_measure.mk_metric m : outer_measure X) = measure.mk_metric m :=
by rw [← measure.mk_metric_to_outer_measure, coe_to_outer_measure]

namespace measure

variables [measurable_space X] [borel_space X]

/-- If `c ∉ {0, ∞}` and `m₁ d ≤ c * m₂ d` for `d < ε` for some `ε > 0`
(we use `≤ᶠ[𝓝[≥] 0]` to state this), then `mk_metric m₁ hm₁ ≤ c • mk_metric m₂ hm₂`. -/
lemma mk_metric_mono_smul {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ∞) (h0 : c ≠ 0)
  (hle : m₁ ≤ᶠ[𝓝[≥] 0] c • m₂) :
  (mk_metric m₁ : measure X) ≤ c • mk_metric m₂ :=
begin
  intros s hs,
  rw [← outer_measure.coe_mk_metric, coe_smul, ← outer_measure.coe_mk_metric],
  exact outer_measure.mk_metric_mono_smul hc h0 hle s
end

/-- If `m₁ d ≤ m₂ d` for `d < ε` for some `ε > 0` (we use `≤ᶠ[𝓝[≥] 0]` to state this), then
`mk_metric m₁ hm₁ ≤ mk_metric m₂ hm₂`-/
lemma mk_metric_mono {m₁ m₂ : ℝ≥0∞ → ℝ≥0∞} (hle : m₁ ≤ᶠ[𝓝[≥] 0] m₂) :
  (mk_metric m₁ : measure X) ≤ mk_metric m₂ :=
by { convert mk_metric_mono_smul ennreal.one_ne_top ennreal.zero_lt_one.ne' _; simp * }

/-- A formula for `measure_theory.measure.mk_metric`. -/
lemma mk_metric_apply (m : ℝ≥0∞ → ℝ≥0∞) (s : set X) :
  mk_metric m s = ⨆ (r : ℝ≥0∞) (hr : 0 < r),
    ⨅ (t : ℕ → set X) (h : s ⊆ Union t) (h' : ∀ n, diam (t n) ≤ r),
      ∑' n, ⨆ (h : (t n).nonempty), m (diam (t n)) :=
begin
  -- We mostly unfold the definitions but we need to switch the order of `∑'` and `⨅`
  classical,
  simp only [← outer_measure.coe_mk_metric, outer_measure.mk_metric, outer_measure.mk_metric',
    outer_measure.supr_apply, outer_measure.mk_metric'.pre, outer_measure.bounded_by_apply,
    extend],
  refine supr_congr (λ r, r) surjective_id (λ r, supr_congr_Prop iff.rfl $ λ hr,
    infi_congr _ surjective_id $ λ t, infi_congr_Prop iff.rfl $ λ ht, _),
  by_cases htr : ∀ n, diam (t n) ≤ r,
  { rw [infi_eq_if, if_pos htr],
    congr' 1 with n : 1,
    simp only [infi_eq_if, htr n, id, if_true, supr_and'] },
  { rw [infi_eq_if, if_neg htr],
    push_neg at htr, rcases htr with ⟨n, hn⟩,
    refine ennreal.tsum_eq_top_of_eq_top ⟨n, _⟩,
    rw [supr_eq_if, if_pos, infi_eq_if, if_neg],
    exact hn.not_le,
    rcases diam_pos_iff.1 ((zero_le r).trans_lt hn) with ⟨x, hx, -⟩,
    exact ⟨x, hx⟩ }
end

lemma le_mk_metric (m : ℝ≥0∞ → ℝ≥0∞) (μ : measure X) (ε : ℝ≥0∞) (h₀ : 0 < ε)
  (h : ∀ s : set X, diam s ≤ ε → μ s ≤ m (diam s)) :
  μ ≤ mk_metric m :=
begin
  rw [← to_outer_measure_le, mk_metric_to_outer_measure],
  exact outer_measure.le_mk_metric m μ.to_outer_measure ε h₀ h
end

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of encodable types. -/
lemma mk_metric_le_liminf_tsum {β : Type*} {ι : β → Type*} [∀ n, encodable (ι n)] (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i)
  (m : ℝ≥0∞ → ℝ≥0∞) :
  mk_metric m s ≤ liminf l (λ n, ∑' i, m (diam (t n i))) :=
begin
  simp only [mk_metric_apply],
  refine bsupr_le (λ ε hε, _),
  refine le_of_forall_le_of_dense (λ c hc, _),
  rcases ((frequently_lt_of_liminf_lt (by apply_auto_param) hc).and_eventually
    ((hr.eventually (gt_mem_nhds hε)).and (ht.and hst))).exists with ⟨n, hn, hrn, htn, hstn⟩,
  set u : ℕ → set X := λ j, ⋃ b ∈ decode₂ (ι n) j, t n b,
  refine binfi_le_of_le u (by rwa Union_decode₂) _,
  refine infi_le_of_le (λ j, _) _,
  { rw emetric.diam_Union_mem_option,
    exact bsupr_le (λ _ _, (htn _).trans hrn.le) },
  { calc (∑' (j : ℕ), ⨆ (h : (u j).nonempty), m (diam (u j))) = _ :
              tsum_Union_decode₂ (λ t : set X, ⨆ (h : t.nonempty), m (diam t)) (by simp) _
    ... ≤ ∑' (i : ι n), m (diam (t n i)) :
      ennreal.tsum_le_tsum (λ b, supr_le $ λ htb, le_rfl)
    ... ≤ c : hn.le }
end

/-- To bound the Hausdorff measure (or, more generally, for a measure defined using
`measure_theory.measure.mk_metric`) of a set, one may use coverings with maximum diameter tending to
`0`, indexed by any sequence of finite types. -/
lemma mk_metric_le_liminf_sum {β : Type*} {ι : β → Type*} [hι : ∀ n, fintype (ι n)] (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i)
  (m : ℝ≥0∞ → ℝ≥0∞) :
  mk_metric m s ≤ liminf l (λ n, ∑ i, m (diam (t n i))) :=
begin
  haveI : ∀ n, encodable (ι n), from λ n, fintype.encodable _,
  simpa only [tsum_fintype] using mk_metric_le_liminf_tsum s r hr t ht hst m,
end

/-!
### Hausdorff measure and Hausdorff dimension
-/

/-- Hausdorff measure on an (e)metric space. -/
def hausdorff_measure (d : ℝ) : measure X := mk_metric (λ r, r ^ d)

localized "notation `μH[` d `]` := measure_theory.measure.hausdorff_measure d" in measure_theory

lemma le_hausdorff_measure (d : ℝ) (μ : measure X) (ε : ℝ≥0∞) (h₀ : 0 < ε)
  (h : ∀ s : set X, diam s ≤ ε → μ s ≤ diam s ^ d) :
  μ ≤ μH[d] :=
le_mk_metric _ μ ε h₀ h

/-- A formula for `μH[d] s`. -/
lemma hausdorff_measure_apply (d : ℝ) (s : set X) :
  μH[d] s = ⨆ (r : ℝ≥0∞) (hr : 0 < r), ⨅ (t : ℕ → set X) (hts : s ⊆ ⋃ n, t n)
    (ht : ∀ n, diam (t n) ≤ r), ∑' n, ⨆ (h : (t n).nonempty), (diam (t n)) ^ d :=
mk_metric_apply _ _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of encodable types. -/
lemma hausdorff_measure_le_liminf_tsum {β : Type*}  {ι : β → Type*} [hι : ∀ n, encodable (ι n)]
  (d : ℝ) (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) :
  μH[d] s ≤ liminf l (λ n, ∑' i, diam (t n i) ^ d) :=
mk_metric_le_liminf_tsum s r hr t ht hst _

/-- To bound the Hausdorff measure of a set, one may use coverings with maximum diameter tending
to `0`, indexed by any sequence of finite types. -/
lemma hausdorff_measure_le_liminf_sum {β : Type*}  {ι : β → Type*} [hι : ∀ n, fintype (ι n)]
  (d : ℝ) (s : set X)
  {l : filter β} (r : β → ℝ≥0∞) (hr : tendsto r l (𝓝 0)) (t : Π (n : β), ι n → set X)
  (ht : ∀ᶠ n in l, ∀ i, diam (t n i) ≤ r n) (hst : ∀ᶠ n in l, s ⊆ ⋃ i, t n i) :
  μH[d] s ≤ liminf l (λ n, ∑ i, diam (t n i) ^ d) :=
mk_metric_le_liminf_sum s r hr t ht hst _

/-- If `d₁ < d₂`, then for any set `s` we have either `μH[d₂] s = 0`, or `μH[d₁] s = ∞`. -/
lemma hausdorff_measure_zero_or_top {d₁ d₂ : ℝ} (h : d₁ < d₂) (s : set X) :
  μH[d₂] s = 0 ∨ μH[d₁] s = ∞ :=
begin
  by_contra' H, 
  suffices : ∀ (c : ℝ≥0), c ≠ 0 → μH[d₂] s ≤ c * μH[d₁] s,
  { rcases ennreal.exists_nnreal_pos_mul_lt H.2 H.1 with ⟨c, hc0, hc⟩,
    exact hc.not_le (this c (pos_iff_ne_zero.1 hc0)) },
  intros c hc,
  refine le_iff'.1 (mk_metric_mono_smul ennreal.coe_ne_top (by exact_mod_cast hc) _) s,
  have : 0 < (c ^ (d₂ - d₁)⁻¹ : ℝ≥0∞),
  { rw [ennreal.coe_rpow_of_ne_zero hc, pos_iff_ne_zero, ne.def, ennreal.coe_eq_zero,
      nnreal.rpow_eq_zero_iff],
    exact mt and.left hc },
  filter_upwards [Ico_mem_nhds_within_Ici ⟨le_rfl, this⟩],
  rintro r ⟨hr₀, hrc⟩,
  lift r to ℝ≥0 using ne_top_of_lt hrc,
  rw [pi.smul_apply, smul_eq_mul, ← ennreal.div_le_iff_le_mul (or.inr ennreal.coe_ne_top)
    (or.inr $ mt ennreal.coe_eq_zero.1 hc)],
  rcases eq_or_ne r 0 with rfl|hr₀,
  { rcases lt_or_le 0 d₂ with h₂|h₂,
    { simp only [h₂, ennreal.zero_rpow_of_pos, zero_le', ennreal.coe_nonneg, ennreal.zero_div,
        ennreal.coe_zero] },
    { simp only [h.trans_le h₂, ennreal.div_top, zero_le', ennreal.coe_nonneg,
        ennreal.zero_rpow_of_neg, ennreal.coe_zero] } },
  { have : (r : ℝ≥0∞) ≠ 0, by simpa only [ennreal.coe_eq_zero, ne.def] using hr₀,
    rw [← ennreal.rpow_sub _ _ this ennreal.coe_ne_top],
    refine (ennreal.rpow_lt_rpow hrc (sub_pos.2 h)).le.trans _,
    rw [← ennreal.rpow_mul, inv_mul_cancel (sub_pos.2 h).ne', ennreal.rpow_one],
    exact le_rfl }
end

/-- Hausdorff measure `μH[d] s` is monotone in `d`. -/
lemma hausdorff_measure_mono {d₁ d₂ : ℝ} (h : d₁ ≤ d₂) (s : set X) : μH[d₂] s ≤ μH[d₁] s :=
begin
  rcases h.eq_or_lt with rfl|h, { exact le_rfl },
  cases hausdorff_measure_zero_or_top h s with hs hs,
  { rw hs, exact zero_le _ },
  { rw hs, exact le_top }
end

variables (X)
lemma no_atoms_hausdorff {d : ℝ} (hd : 0 < d) : has_no_atoms (hausdorff_measure d : measure X) :=
begin
  refine ⟨λ x, _⟩,
  rw [← nonpos_iff_eq_zero, hausdorff_measure_apply],
  refine bsupr_le (λ ε ε0, binfi_le_of_le (λ n, {x}) _ (infi_le_of_le (λ n, _) _)),
  { exact subset_Union (λ n, {x} : ℕ → set X) 0 },
  { simp only [emetric.diam_singleton, zero_le] },
  { simp [hd] }
end
variables {X}

@[simp] lemma hausdorff_measure_zero_singleton (x : X) : μH[0] ({x} : set X) = 1 :=
begin
  apply le_antisymm,
  { let r : ℕ → ℝ≥0∞ := λ _, 0,
    let t : ℕ → unit → set X := λ n _, {x},
    have ht : ∀ᶠ n in at_top, ∀ i, diam (t n i) ≤ r n,
      by simp only [implies_true_iff, eq_self_iff_true, diam_singleton, eventually_at_top,
        nonpos_iff_eq_zero, exists_const],
    simpa [liminf_const] using hausdorff_measure_le_liminf_sum 0 {x} r tendsto_const_nhds t ht },
  { rw hausdorff_measure_apply,
    suffices : (1 : ℝ≥0∞) ≤ ⨅ (t : ℕ → set X) (hts : {x} ⊆ ⋃ n, t n)
      (ht : ∀ n, diam (t n) ≤ 1), ∑' n, ⨆ (h : (t n).nonempty), (diam (t n)) ^ (0 : ℝ),
    { apply le_trans this _,
      convert le_bsupr (1 : ℝ≥0∞) (ennreal.zero_lt_one),
      refl },
    simp only [ennreal.rpow_zero, le_infi_iff],
    assume t hst h't,
    rcases mem_Union.1 (hst (mem_singleton x)) with ⟨m, hm⟩,
    have A : (t m).nonempty := ⟨x, hm⟩,
    calc (1 : ℝ≥0∞) = ⨆ (h : (t m).nonempty), 1 : by simp only [A, csupr_pos]
    ... ≤ ∑' n, ⨆ (h : (t n).nonempty), 1 : ennreal.le_tsum _ }
end

lemma one_le_hausdorff_measure_zero_of_nonempty {s : set X} (h : s.nonempty) :
  1 ≤ μH[0] s :=
begin
  rcases h with ⟨x, hx⟩,
  calc (1 : ℝ≥0∞) = μH[0] ({x} : set X) : (hausdorff_measure_zero_singleton x).symm
  ... ≤ μH[0] s : measure_mono (singleton_subset_iff.2 hx)
end

lemma hausdorff_measure_le_one_of_subsingleton
  {s : set X} (hs : s.subsingleton) {d : ℝ} (hd : 0 ≤ d) :
  μH[d] s ≤ 1 :=
begin
  rcases eq_empty_or_nonempty s with rfl|⟨x, hx⟩,
  { simp only [measure_empty, zero_le] },
  { rw (subsingleton_iff_singleton hx).1 hs,
    rcases eq_or_lt_of_le hd with rfl|dpos,
    { simp only [le_refl, hausdorff_measure_zero_singleton] },
    { haveI := no_atoms_hausdorff X dpos,
      simp only [zero_le, measure_singleton] } }
end

end measure

open_locale measure_theory
open measure

/-!
### Hausdorff measure and Lebesgue measure
-/

/-- In the space `ι → ℝ`, Hausdorff measure coincides exactly with Lebesgue measure. -/
@[simp] theorem hausdorff_measure_pi_real {ι : Type*} [fintype ι] :
  (μH[fintype.card ι] : measure (ι → ℝ)) = volume :=
begin
  classical,
  -- it suffices to check that the two measures coincide on products of rational intervals
  refine (pi_eq_generate_from (λ i, real.borel_eq_generate_from_Ioo_rat.symm)
    (λ i, real.is_pi_system_Ioo_rat) (λ i, real.finite_spanning_sets_in_Ioo_rat _)
    _).symm,
  simp only [mem_Union, mem_singleton_iff],
  -- fix such a product `s` of rational intervals, of the form `Π (a i, b i)`.
  intros s hs,
  choose a b H using hs,
  obtain rfl : s = λ i, Ioo (a i) (b i), from funext (λ i, (H i).2), replace H := λ i, (H i).1,
  apply le_antisymm _,
  -- first check that `volume s ≤ μH s`
  { have Hle : volume ≤ (μH[fintype.card ι] : measure (ι → ℝ)),
    { refine le_hausdorff_measure _ _ ∞ ennreal.coe_lt_top (λ s _, _),
      rw [ennreal.rpow_nat_cast],
      exact real.volume_pi_le_diam_pow s },
    rw [← volume_pi_pi (λ i, Ioo (a i : ℝ) (b i))],
    exact measure.le_iff'.1 Hle _ },
  /- For the other inequality `μH s ≤ volume s`, we use a covering of `s` by sets of small diameter
  `1/n`, namely cubes with left-most point of the form `a i + f i / n` with `f i` ranging between
  `0` and `⌈(b i - a i) * n⌉`. Their number is asymptotic to `n^d * Π (b i - a i)`. -/
  have I : ∀ i, 0 ≤ (b i : ℝ) - a i := λ i, by simpa only [sub_nonneg, rat.cast_le] using (H i).le,
  let γ := λ (n : ℕ), (Π (i : ι), fin ⌈((b i : ℝ) - a i) * n⌉₊),
  let t : Π (n : ℕ), γ n → set (ι → ℝ) :=
    λ n f, set.pi univ (λ i, Icc (a i + f i / n) (a i + (f i + 1) / n)),
  have A : tendsto (λ (n : ℕ), 1/(n : ℝ≥0∞)) at_top (𝓝 0),
    by simp only [one_div, ennreal.tendsto_inv_nat_nhds_zero],
  have B : ∀ᶠ n in at_top, ∀ (i : γ n), diam (t n i) ≤ 1 / n,
  { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
    assume f,
    apply diam_pi_le_of_le (λ b, _),
    simp only [real.ediam_Icc, add_div, ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), le_refl,
      add_sub_add_left_eq_sub, add_sub_cancel', ennreal.of_real_one, ennreal.of_real_coe_nat] },
  have C : ∀ᶠ n in at_top, set.pi univ (λ (i : ι), Ioo (a i : ℝ) (b i)) ⊆ ⋃ (i : γ n), t n i,
  { apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
    have npos : (0 : ℝ) < n := nat.cast_pos.2 hn,
    assume x hx,
    simp only [mem_Ioo, mem_univ_pi] at hx,
    simp only [mem_Union, mem_Ioo, mem_univ_pi, coe_coe],
    let f : γ n := λ i, ⟨⌊(x i - a i) * n⌋₊,
    begin
      apply nat.floor_lt_ceil_of_lt_of_pos,
      { refine (mul_lt_mul_right npos).2 _,
        simp only [(hx i).right, sub_lt_sub_iff_right] },
      { refine mul_pos _ npos,
        simpa only [rat.cast_lt, sub_pos] using H i }
    end⟩,
    refine ⟨f, λ i, ⟨_, _⟩⟩,
    { calc (a i : ℝ) + ⌊(x i - a i) * n⌋₊ / n
      ≤ (a i : ℝ) + ((x i - a i) * n) / n :
          begin
            refine add_le_add le_rfl ((div_le_div_right npos).2 _),
            exact nat.floor_le (mul_nonneg (sub_nonneg.2 (hx i).1.le) npos.le),
          end
      ... = x i : by field_simp [npos.ne'] },
    { calc x i
      = (a i : ℝ) + ((x i - a i) * n) / n : by field_simp [npos.ne']
      ... ≤ (a i : ℝ) + (⌊(x i - a i) * n⌋₊ + 1) / n :
        add_le_add le_rfl ((div_le_div_right npos).2 (nat.lt_floor_add_one _).le) } },
  calc μH[fintype.card ι] (set.pi univ (λ (i : ι), Ioo (a i : ℝ) (b i)))
    ≤ liminf at_top (λ (n : ℕ), ∑ (i : γ n), diam (t n i) ^ ↑(fintype.card ι)) :
      hausdorff_measure_le_liminf_sum _ (set.pi univ (λ i, Ioo (a i : ℝ) (b i)))
        (λ (n : ℕ), 1/(n : ℝ≥0∞)) A t B C
  ... ≤ liminf at_top (λ (n : ℕ), ∑ (i : γ n), (1/n) ^ (fintype.card ι)) :
    begin
      refine liminf_le_liminf _ (by is_bounded_default),
      filter_upwards [B] with _ hn,
      apply finset.sum_le_sum (λ i _, _),
      rw ennreal.rpow_nat_cast,
      exact pow_le_pow_of_le_left' (hn i) _,
    end
  ... = liminf at_top (λ (n : ℕ), ∏ (i : ι), (⌈((b i : ℝ) - a i) * n⌉₊ : ℝ≥0∞) / n) :
  begin
    simp only [finset.card_univ, nat.cast_prod, one_mul, fintype.card_fin,
      finset.sum_const, nsmul_eq_mul, fintype.card_pi, div_eq_mul_inv, finset.prod_mul_distrib,
      finset.prod_const]
  end
  ... = ∏ (i : ι), volume (Ioo (a i : ℝ) (b i)) :
  begin
    simp only [real.volume_Ioo],
    apply tendsto.liminf_eq,
    refine ennreal.tendsto_finset_prod_of_ne_top _ (λ i hi, _) (λ i hi, _),
    { apply tendsto.congr' _ ((ennreal.continuous_of_real.tendsto _).comp
        ((tendsto_nat_ceil_mul_div_at_top (I i)).comp tendsto_coe_nat_at_top_at_top)),
      apply eventually_at_top.2 ⟨1, λ n hn, _⟩,
      simp only [ennreal.of_real_div_of_pos (nat.cast_pos.mpr hn), comp_app,
        ennreal.of_real_coe_nat] },
    { simp only [ennreal.of_real_ne_top, ne.def, not_false_iff] }
  end
end

end measure_theory

/-!
### Hausdorff measure, Hausdorff dimension, and Hölder or Lipschitz continuous maps
-/

open_locale measure_theory
open measure_theory measure_theory.measure

variables [measurable_space X] [borel_space X] [measurable_space Y] [borel_space Y]

namespace holder_on_with

variables {C r : ℝ≥0} {f : X → Y} {s t : set X}

/-- If `f : X → Y` is Hölder continuous on `s` with a positive exponent `r`, then
`μH[d] (f '' s) ≤ C ^ d * μH[r * d] s`. -/
lemma hausdorff_measure_image_le (h : holder_on_with C r f s) (hr : 0 < r) {d : ℝ} (hd : 0 ≤ d) :
  μH[d] (f '' s) ≤ C ^ d * μH[r * d] s :=
begin
  -- We start with the trivial case `C = 0`
  rcases (zero_le C).eq_or_lt with rfl|hC0,
  { rcases eq_empty_or_nonempty s with rfl|⟨x, hx⟩,
    { simp only [measure_empty, nonpos_iff_eq_zero, mul_zero, image_empty] },
    have : f '' s = {f x},
    { have : (f '' s).subsingleton, by simpa [diam_eq_zero_iff] using h.ediam_image_le,
      exact (subsingleton_iff_singleton (mem_image_of_mem f hx)).1 this },
    rw this,
    rcases eq_or_lt_of_le hd with rfl|h'd,
    { simp only [ennreal.rpow_zero, one_mul, mul_zero],
      rw hausdorff_measure_zero_singleton,
      exact one_le_hausdorff_measure_zero_of_nonempty ⟨x, hx⟩ },
    { haveI := no_atoms_hausdorff Y h'd,
      simp only [zero_le, measure_singleton] } },
  -- Now assume `C ≠ 0`
  { have hCd0 : (C : ℝ≥0∞) ^ d ≠ 0, by simp [hC0.ne'],
    have hCd : (C : ℝ≥0∞) ^ d ≠ ∞, by simp [hd],
    simp only [hausdorff_measure_apply, ennreal.mul_supr, ennreal.mul_infi_of_ne hCd0 hCd,
      ← ennreal.tsum_mul_left],
    refine supr_le (λ R, supr_le $ λ hR, _),
    have : tendsto (λ d : ℝ≥0∞, (C : ℝ≥0∞) * d ^ (r : ℝ)) (𝓝 0) (𝓝 0),
      from ennreal.tendsto_const_mul_rpow_nhds_zero_of_pos ennreal.coe_ne_top hr,
    rcases ennreal.nhds_zero_basis_Iic.eventually_iff.1 (this.eventually (gt_mem_nhds hR))
      with ⟨δ, δ0, H⟩,
    refine le_supr_of_le δ (le_supr_of_le δ0 $ le_binfi $ λ t hst, le_infi $ λ htδ, _),
    refine binfi_le_of_le (λ n, f '' (t n ∩ s)) _ (infi_le_of_le (λ n, _) _),
    { rw [← image_Union, ← Union_inter],
      exact image_subset _ (subset_inter hst subset.rfl) },
    { exact (h.ediam_image_inter_le (t n)).trans (H (htδ n)).le },
    { apply ennreal.tsum_le_tsum (λ n, _),
      simp only [supr_le_iff, nonempty_image_iff],
      assume hft,
      simp only [nonempty.mono ((t n).inter_subset_left s) hft, csupr_pos],
      rw [ennreal.rpow_mul, ← ennreal.mul_rpow_of_nonneg _ _ hd],
      exact ennreal.rpow_le_rpow (h.ediam_image_inter_le _) hd } }
end

end holder_on_with

namespace lipschitz_on_with

variables {K : ℝ≥0} {f : X → Y} {s t : set X}

/-- If `f : X → Y` is `K`-Lipschitz on `s`, then `μH[d] (f '' s) ≤ K ^ d * μH[d] s`. -/
lemma hausdorff_measure_image_le (h : lipschitz_on_with K f s) {d : ℝ} (hd : 0 ≤ d) :
  μH[d] (f '' s) ≤ K ^ d * μH[d] s :=
by simpa only [nnreal.coe_one, one_mul]
  using h.holder_on_with.hausdorff_measure_image_le zero_lt_one hd

end lipschitz_on_with

namespace lipschitz_with

variables {K : ℝ≥0} {f : X → Y}

/-- If `f` is a `K`-Lipschitz map, then it increases the Hausdorff `d`-measures of sets at most
by the factor of `K ^ d`.-/
lemma hausdorff_measure_image_le (h : lipschitz_with K f) {d : ℝ} (hd : 0 ≤ d) (s : set X) :
  μH[d] (f '' s) ≤ K ^ d * μH[d] s :=
(h.lipschitz_on_with s).hausdorff_measure_image_le hd

end lipschitz_with

/-!
### Antilipschitz maps do not decrease Hausdorff measures and dimension
-/

namespace antilipschitz_with

variables {f : X → Y} {K : ℝ≥0} {d : ℝ}

lemma hausdorff_measure_preimage_le (hf : antilipschitz_with K f) (hd : 0 ≤ d) (s : set Y) :
  μH[d] (f ⁻¹' s) ≤ K ^ d * μH[d] s :=
begin
  rcases eq_or_ne K 0 with rfl|h0,
  { rcases eq_empty_or_nonempty (f ⁻¹' s) with hs|⟨x, hx⟩,
    { simp only [hs, measure_empty, zero_le], },
    have : f ⁻¹' s = {x},
    { haveI : subsingleton X := hf.subsingleton,
      have : (f ⁻¹' s).subsingleton, from subsingleton_univ.mono (subset_univ _),
      exact (subsingleton_iff_singleton hx).1 this },
    rw this,
    rcases eq_or_lt_of_le hd with rfl|h'd,
    { simp only [ennreal.rpow_zero, one_mul, mul_zero],
      rw hausdorff_measure_zero_singleton,
      exact one_le_hausdorff_measure_zero_of_nonempty ⟨f x, hx⟩ },
    { haveI := no_atoms_hausdorff X h'd,
      simp only [zero_le, measure_singleton] } },
  have hKd0 : (K : ℝ≥0∞) ^ d ≠ 0, by simp [h0],
  have hKd : (K : ℝ≥0∞) ^ d ≠ ∞, by simp [hd],
  simp only [hausdorff_measure_apply, ennreal.mul_supr, ennreal.mul_infi_of_ne hKd0 hKd,
    ← ennreal.tsum_mul_left],
  refine bsupr_le (λ ε ε0, _),
  refine le_bsupr_of_le (ε / K) (by simp [ε0.ne']) _,
  refine le_binfi (λ t hst, le_infi $ λ htε, _),
  replace hst : f ⁻¹' s ⊆ _ := preimage_mono hst, rw preimage_Union at hst,
  refine binfi_le_of_le _ hst (infi_le_of_le (λ n, _) _),
  { exact (hf.ediam_preimage_le _).trans (ennreal.mul_le_of_le_div' $ htε n) },
  { refine ennreal.tsum_le_tsum (λ n, supr_le_iff.2 (λ hft, _)),
    simp only [nonempty_of_nonempty_preimage hft, csupr_pos],
    rw [← ennreal.mul_rpow_of_nonneg _ _ hd],
    exact ennreal.rpow_le_rpow (hf.ediam_preimage_le _) hd }
end

lemma le_hausdorff_measure_image (hf : antilipschitz_with K f) (hd : 0 ≤ d) (s : set X) :
  μH[d] s ≤ K ^ d * μH[d] (f '' s) :=
calc μH[d] s ≤ μH[d] (f ⁻¹' (f '' s)) : measure_mono (subset_preimage_image _ _)
         ... ≤ K ^ d * μH[d] (f '' s) : hf.hausdorff_measure_preimage_le hd (f '' s)

end antilipschitz_with

/-!
### Isometries preserve the Hausdorff measure and Hausdorff dimension
-/

namespace isometry

variables {f : X → Y} {d : ℝ}

lemma hausdorff_measure_image (hf : isometry f) (hd : 0 ≤ d ∨ surjective f) (s : set X) :
  μH[d] (f '' s) = μH[d] s :=
begin
  simp only [hausdorff_measure, ← outer_measure.coe_mk_metric, ← outer_measure.comap_apply],
  rw [outer_measure.isometry_comap_mk_metric _ hf (hd.imp_left _)],
  exact λ hd x y hxy, ennreal.rpow_le_rpow hxy hd
end

lemma hausdorff_measure_preimage (hf : isometry f) (hd : 0 ≤ d ∨ surjective f) (s : set Y) :
  μH[d] (f ⁻¹' s) = μH[d] (s ∩ range f) :=
by rw [← hf.hausdorff_measure_image hd, image_preimage_eq_inter_range]

lemma map_hausdorff_measure (hf : isometry f) (hd : 0 ≤ d ∨ surjective f) :
  measure.map f μH[d] = (μH[d]).restrict (range f) :=
begin
  ext1 s hs,
  rw [map_apply hf.continuous.measurable hs, restrict_apply hs, hf.hausdorff_measure_preimage hd]
end

end isometry

namespace isometric

@[simp] lemma hausdorff_measure_image (e : X ≃ᵢ Y) (d : ℝ) (s : set X) :
  μH[d] (e '' s) = μH[d] s :=
e.isometry.hausdorff_measure_image (or.inr e.surjective) s

@[simp] lemma hausdorff_measure_preimage (e : X ≃ᵢ Y) (d : ℝ) (s : set Y) :
  μH[d] (e ⁻¹' s) = μH[d] s :=
by rw [← e.image_symm, e.symm.hausdorff_measure_image]

end isometric
