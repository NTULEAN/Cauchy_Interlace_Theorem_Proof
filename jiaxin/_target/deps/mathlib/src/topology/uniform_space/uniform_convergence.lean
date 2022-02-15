/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.uniform_space.basic

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `at_top`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α`to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `tendsto_uniformly_on F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `tendsto_uniformly F f p`: same notion with `s = univ`.
* `tendsto_uniformly_on.continuous_on`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `tendsto_uniformly.continuous`: a uniform limit of continuous functions is continuous.
* `tendsto_uniformly_on.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `tendsto_uniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

We also define notions where the convergence is locally uniform, called
`tendsto_locally_uniformly_on F f p s` and `tendsto_locally_uniformly F f p`. The previous theorems
all have corresponding versions under locally uniform convergence.

## Implementation notes

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
 -/

noncomputable theory
open_locale topological_space classical uniformity filter

open set filter

universes u v w
variables {α β γ ι : Type*} [uniform_space β]
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {g : ι → α}

/-!
### Different notions of uniform convergence

We define uniform convergence and locally uniform convergence, on a set or in the whole space.
-/

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`. -/
def tendsto_uniformly_on (F : ι → α → β) (f : α → β) (p : filter ι) (s : set α) :=
∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x ∈ s, (f x, F n x) ∈ u

/--
A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ 𝓟 s` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `s`.
-/
lemma tendsto_uniformly_on_iff_tendsto {F : ι → α → β} {f : α → β} {p : filter ι} {s : set α} :
  tendsto_uniformly_on F f p s ↔ tendsto (λ q : ι × α, (f q.2, F q.1 q.2)) (p ×ᶠ 𝓟 s) (𝓤 β) :=
forall₂_congr $ λ u u_in, by simp [mem_map, filter.eventually, mem_prod_principal]

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
def tendsto_uniformly (F : ι → α → β) (f : α → β) (p : filter ι) :=
∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ x, (f x, F n x) ∈ u

lemma tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe :
  tendsto_uniformly_on F f p s ↔ tendsto_uniformly (λ i (x : s), F i x) (f ∘ coe) p :=
forall₂_congr $ λ V hV, by simp

/--
A sequence of functions `Fₙ` converges uniformly to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ ⊤` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit.
-/
lemma tendsto_uniformly_iff_tendsto {F : ι → α → β} {f : α → β} {p : filter ι} :
  tendsto_uniformly F f p ↔ tendsto (λ q : ι × α, (f q.2, F q.1 q.2)) (p ×ᶠ ⊤) (𝓤 β) :=
forall₂_congr $ λ u u_in, by simp [mem_map, filter.eventually, mem_prod_top]

lemma tendsto_uniformly_on_univ :
  tendsto_uniformly_on F f p univ ↔ tendsto_uniformly F f p :=
by simp [tendsto_uniformly_on, tendsto_uniformly]

lemma tendsto_uniformly_on.mono {s' : set α}
  (h : tendsto_uniformly_on F f p s) (h' : s' ⊆ s) : tendsto_uniformly_on F f p s' :=
λ u hu, (h u hu).mono (λ n hn x hx, hn x (h' hx))

protected lemma tendsto_uniformly.tendsto_uniformly_on
  (h : tendsto_uniformly F f p) : tendsto_uniformly_on F f p s :=
(tendsto_uniformly_on_univ.2 h).mono (subset_univ s)

/-- Composing on the right by a function preserves uniform convergence on a set -/
lemma tendsto_uniformly_on.comp (h : tendsto_uniformly_on F f p s) (g : γ → α) :
  tendsto_uniformly_on (λ n, F n ∘ g) (f ∘ g) p (g ⁻¹' s) :=
λ u hu, (h u hu).mono (λ i hi, λ a, hi (g a))

/-- Composing on the right by a function preserves uniform convergence -/
lemma tendsto_uniformly.comp (h : tendsto_uniformly F f p) (g : γ → α) :
  tendsto_uniformly (λ n, F n ∘ g) (f ∘ g) p :=
λ u hu, (h u hu).mono (λ i hi, λ a, hi (g a))

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a set -/
lemma tendsto_uniformly_on.comp' [uniform_space γ] {g : β → γ} (h : tendsto_uniformly_on F f p s)
  (hg : uniform_continuous g) : tendsto_uniformly_on (λ i, g ∘ (F i)) (g ∘ f) p s :=
λ u hu, h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves uniform convergence -/
lemma tendsto_uniformly.comp' [uniform_space γ] {g : β → γ} (h : tendsto_uniformly F f p)
  (hg : uniform_continuous g) : tendsto_uniformly (λ i, g ∘ (F i)) (g ∘ f) p :=
λ u hu, h _ (hg hu)

lemma tendsto_uniformly_on.prod_map {ι' α' β' : Type*} [uniform_space β']
  {F' : ι' → α' → β'} {f' : α' → β'} {p' : filter ι'} {s' : set α'}
  (h : tendsto_uniformly_on F f p s) (h' : tendsto_uniformly_on F' f' p' s') :
  tendsto_uniformly_on (λ (i : ι × ι'), prod.map (F i.1) (F' i.2))
    (prod.map f f') (p.prod p') (s ×ˢ s') :=
begin
  intros u hu,
  rw [uniformity_prod_eq_prod, mem_map, mem_prod_iff] at hu,
  obtain ⟨v, hv, w, hw, hvw⟩ := hu,
  exact mem_prod_iff.mpr ⟨_, h v hv, _, h' w hw,
    λ i hi a ha, hvw (show (_, _) ∈ v ×ˢ w, from ⟨hi.1 a.1 ha.1, hi.2 a.2 ha.2⟩)⟩,
end

lemma tendsto_uniformly.prod_map {ι' α' β' : Type*} [uniform_space β'] {F' : ι' → α' → β'}
  {f' : α' → β'} {p' : filter ι'} (h : tendsto_uniformly F f p) (h' : tendsto_uniformly F' f' p') :
  tendsto_uniformly (λ (i : ι × ι'), prod.map (F i.1) (F' i.2)) (prod.map f f') (p.prod p') :=
begin
  rw [←tendsto_uniformly_on_univ, ←univ_prod_univ] at *,
  exact h.prod_map h',
end

lemma tendsto_uniformly_on.prod {ι' β' : Type*} [uniform_space β'] {F' : ι' → α → β'} {f' : α → β'}
  {p' : filter ι'} (h : tendsto_uniformly_on F f p s) (h' : tendsto_uniformly_on F' f' p' s) :
  tendsto_uniformly_on (λ (i : ι × ι') a, (F i.1 a, F' i.2 a)) (λ a, (f a, f' a)) (p.prod p') s :=
(congr_arg _ s.inter_self).mp ((h.prod_map h').comp (λ a, (a, a)))

lemma tendsto_uniformly.prod {ι' β' : Type*} [uniform_space β'] {F' : ι' → α → β'} {f' : α → β'}
  {p' : filter ι'} (h : tendsto_uniformly F f p) (h' : tendsto_uniformly F' f' p') :
  tendsto_uniformly (λ (i : ι × ι') a, (F i.1 a, F' i.2 a)) (λ a, (f a, f' a)) (p.prod p') :=
(h.prod_map h').comp (λ a, (a, a))

/-- Uniform convergence to a constant function is equivalent to convergence in `p ×ᶠ ⊤`. -/
lemma tendsto_prod_top_iff {c : β} : tendsto ↿F (p ×ᶠ ⊤) (𝓝 c) ↔ tendsto_uniformly F (λ _, c) p :=
let j : β → β × β := prod.mk c in
calc tendsto ↿F (p ×ᶠ ⊤) (𝓝 c)
    ↔ map ↿F (p ×ᶠ ⊤) ≤ (𝓝 c) : iff.rfl
... ↔ map ↿F (p ×ᶠ ⊤) ≤ comap j (𝓤 β) : by rw nhds_eq_comap_uniformity
... ↔ map j (map ↿F (p ×ᶠ ⊤)) ≤ 𝓤 β : map_le_iff_le_comap.symm
... ↔ map (j ∘ ↿F) (p ×ᶠ ⊤) ≤ 𝓤 β : by rw map_map
... ↔ ∀ V ∈ 𝓤 β, {x | (c, ↿F x) ∈ V} ∈ p ×ᶠ (⊤ : filter α) : iff.rfl
... ↔ ∀ V ∈ 𝓤 β, {i | ∀ a, (c, F i a) ∈ V} ∈ p : by simpa [mem_prod_top]

lemma uniform_continuous_on.tendsto_uniformly [uniform_space α] [uniform_space γ]
  {x : α} {U : set α} (hU : U ∈ 𝓝 x)
  {F : α → β → γ} (hF : uniform_continuous_on ↿F (U ×ˢ (univ : set β))) :
  tendsto_uniformly F (F x) (𝓝 x) :=
begin
  let φ := (λ q : α × β, ((x, q.2), q)),
  rw [tendsto_uniformly_iff_tendsto,
      show (λ q : α × β, (F x q.2, F q.1 q.2)) = prod.map ↿F ↿F ∘ φ, by { ext ; simpa }],
  apply hF.comp (tendsto_inf.mpr ⟨_, _⟩),
  { rw [uniformity_prod, tendsto_inf, tendsto_comap_iff, tendsto_comap_iff,
      show (λp : (α × β) × α × β, (p.1.1, p.2.1)) ∘ φ = (λa, (x, a)) ∘ prod.fst, by { ext, simp },
      show (λp : (α × β) × α × β, (p.1.2, p.2.2)) ∘ φ = (λb, (b, b)) ∘ prod.snd, by { ext, simp }],
    exact ⟨tendsto_left_nhds_uniformity.comp tendsto_fst,
           (tendsto_diag_uniformity id ⊤).comp tendsto_top⟩ },
  { rw tendsto_principal,
    apply mem_of_superset (prod_mem_prod hU (mem_top.mpr rfl)) (λ q h, _),
    simp [h.1, mem_of_mem_nhds hU] }
end

lemma uniform_continuous₂.tendsto_uniformly [uniform_space α] [uniform_space γ]
  {f : α → β → γ} (h : uniform_continuous₂ f) {x : α} : tendsto_uniformly f (f x) (𝓝 x) :=
uniform_continuous_on.tendsto_uniformly univ_mem $
  by rwa [univ_prod_univ, uniform_continuous_on_univ]

variable [topological_space α]

/-- A sequence of functions `Fₙ` converges locally uniformly on a set `s` to a limiting function
`f` with respect to a filter `p` if, for any entourage of the diagonal `u`, for any `x ∈ s`, one
has `p`-eventually `(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x` in `s`. -/
def tendsto_locally_uniformly_on (F : ι → α → β) (f : α → β) (p : filter ι) (s : set α) :=
  ∀ u ∈ 𝓤 β, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u

/-- A sequence of functions `Fₙ` converges locally uniformly to a limiting function `f` with respect
to a filter `p` if, for any entourage of the diagonal `u`, for any `x`, one has `p`-eventually
`(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x`. -/
def tendsto_locally_uniformly (F : ι → α → β) (f : α → β) (p : filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ (x : α), ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u

lemma tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe :
  tendsto_locally_uniformly_on F f p s ↔
  tendsto_locally_uniformly (λ i (x : s), F i x) (f ∘ coe) p :=
begin
  refine forall₂_congr (λ V hV, _),
  simp only [exists_prop, function.comp_app, set_coe.forall, subtype.coe_mk],
  refine forall₂_congr (λ x hx, ⟨_, _⟩),
  { rintro ⟨t, ht₁, ht₂⟩,
    obtain ⟨u, hu₁, hu₂⟩ := mem_nhds_within_iff_exists_mem_nhds_inter.mp ht₁,
    exact ⟨coe⁻¹' u,
           (mem_nhds_subtype _ _ _).mpr ⟨u, hu₁, rfl.subset⟩,
           ht₂.mono (λ i hi y hy₁ hy₂, hi y (hu₂ ⟨hy₂, hy₁⟩))⟩, },
  { rintro ⟨t, ht₁, ht₂⟩,
    obtain ⟨u, hu₁, hu₂⟩ := (mem_nhds_subtype _ _ _).mp ht₁,
    exact ⟨u ∩ s,
           mem_nhds_within_iff_exists_mem_nhds_inter.mpr ⟨u, hu₁, rfl.subset⟩,
           ht₂.mono (λ i hi y hy, hi y hy.2 (hu₂ (by simp [hy.1])))⟩, },
end

protected lemma tendsto_uniformly_on.tendsto_locally_uniformly_on
  (h : tendsto_uniformly_on F f p s) : tendsto_locally_uniformly_on F f p s :=
λ u hu x hx, ⟨s, self_mem_nhds_within, h u hu⟩

protected lemma tendsto_uniformly.tendsto_locally_uniformly
  (h : tendsto_uniformly F f p) : tendsto_locally_uniformly F f p :=
λ u hu x, ⟨univ, univ_mem, by simpa using h u hu⟩

lemma tendsto_locally_uniformly_on.mono (h : tendsto_locally_uniformly_on F f p s) (h' : s' ⊆ s) :
  tendsto_locally_uniformly_on F f p s' :=
begin
  assume u hu x hx,
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩,
  exact ⟨t, nhds_within_mono x h' ht, H.mono (λ n, id)⟩
end

lemma tendsto_locally_uniformly_on_univ :
  tendsto_locally_uniformly_on F f p univ ↔ tendsto_locally_uniformly F f p :=
by simp [tendsto_locally_uniformly_on, tendsto_locally_uniformly, nhds_within_univ]

protected lemma tendsto_locally_uniformly.tendsto_locally_uniformly_on
  (h : tendsto_locally_uniformly F f p) : tendsto_locally_uniformly_on F f p s :=
(tendsto_locally_uniformly_on_univ.mpr h).mono (subset_univ _)

/-- On a compact space, locally uniform convergence is just uniform convergence. -/
lemma tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space [compact_space α] :
  tendsto_locally_uniformly F f p ↔ tendsto_uniformly F f p :=
begin
  refine ⟨λ h V hV, _, tendsto_uniformly.tendsto_locally_uniformly⟩,
  choose U hU using h V hV,
  obtain ⟨t, ht⟩ := compact_univ.elim_nhds_subcover' (λ k hk, U k) (λ k hk, (hU k).1),
  replace hU := λ (x : t), (hU x).2,
  rw ← eventually_all at hU,
  refine hU.mono (λ i hi x, _),
  specialize ht (mem_univ x),
  simp only [exists_prop, mem_Union, set_coe.exists, exists_and_distrib_right,subtype.coe_mk] at ht,
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := ht,
  exact hi ⟨⟨y, hy₁⟩, hy₂⟩ x hy₃,
end

/-- For a compact set `s`, locally uniform convergence on `s` is just uniform convergence on `s`. -/
lemma tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_of_compact (hs : is_compact s) :
  tendsto_locally_uniformly_on F f p s ↔ tendsto_uniformly_on F f p s :=
begin
  haveI : compact_space s := is_compact_iff_compact_space.mp hs,
  refine ⟨λ h, _, tendsto_uniformly_on.tendsto_locally_uniformly_on⟩,
  rwa [tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe,
    tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space,
    ← tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe] at h,
end

lemma tendsto_locally_uniformly_on.comp [topological_space γ] {t : set γ}
  (h : tendsto_locally_uniformly_on F f p s)
  (g : γ → α) (hg : maps_to g t s) (cg : continuous_on g t) :
  tendsto_locally_uniformly_on (λ n, (F n) ∘ g) (f ∘ g) p t :=
begin
  assume u hu x hx,
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩,
  have : g⁻¹' a ∈ 𝓝[t] x :=
    ((cg x hx).preimage_mem_nhds_within' (nhds_within_mono (g x) hg.image_subset ha)),
  exact ⟨g ⁻¹' a, this, H.mono (λ n hn y hy, hn _ hy)⟩
end

lemma tendsto_locally_uniformly.comp [topological_space γ]
  (h : tendsto_locally_uniformly F f p) (g : γ → α) (cg : continuous g) :
  tendsto_locally_uniformly (λ n, (F n) ∘ g) (f ∘ g) p :=
begin
  rw ← tendsto_locally_uniformly_on_univ at h ⊢,
  rw continuous_iff_continuous_on_univ at cg,
  exact h.comp _ (maps_to_univ _ _) cg
end

/-!
### Uniform approximation

In this section, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`. -/

/-- A function which can be locally uniformly approximated by functions which are continuous
within a set at a point is continuous within this set at this point. -/
lemma continuous_within_at_of_locally_uniform_approx_of_continuous_within_at
  (hx : x ∈ s) (L : ∀ u ∈ 𝓤 β, ∃ (t ∈ 𝓝[s] x) (F : α → β), continuous_within_at F s x ∧
    ∀ y ∈ t, (f y, F y) ∈ u) : continuous_within_at f s x :=
begin
  apply uniform.continuous_within_at_iff'_left.2 (λ u₀ hu₀, _),
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ (u : set (β × β)) (H : u ∈ 𝓤 β), comp_rel u u ⊆ u₀ :=
    comp_mem_uniformity_sets hu₀,
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : ∃ (u : set (β × β)) (H : u ∈ 𝓤 β),
    (∀{a b}, (a, b) ∈ u → (b, a) ∈ u) ∧ comp_rel u u ⊆ u₁ := comp_symm_of_uniformity h₁,
  rcases L u₂ h₂ with ⟨t, tx, F, hFc, hF⟩,
  have A : ∀ᶠ y in 𝓝[s] x, (f y, F y) ∈ u₂ := eventually.mono tx hF,
  have B : ∀ᶠ y in 𝓝[s] x, (F y, F x) ∈ u₂ :=
    uniform.continuous_within_at_iff'_left.1 hFc h₂,
  have C : ∀ᶠ y in 𝓝[s] x, (f y, F x) ∈ u₁ :=
    (A.and B).mono (λ y hy, u₂₁ (prod_mk_mem_comp_rel hy.1 hy.2)),
  have : (F x, f x) ∈ u₁ :=
    u₂₁ (prod_mk_mem_comp_rel (refl_mem_uniformity h₂) (hsymm (A.self_of_nhds_within hx))),
  exact C.mono (λ y hy, u₁₀ (prod_mk_mem_comp_rel hy this))
end

/-- A function which can be locally uniformly approximated by functions which are continuous at
a point is continuous at this point. -/
lemma continuous_at_of_locally_uniform_approx_of_continuous_at
  (L : ∀ u ∈ 𝓤 β, ∃ (t ∈ 𝓝 x) F, continuous_at F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
  continuous_at f x :=
begin
  rw ← continuous_within_at_univ,
  apply continuous_within_at_of_locally_uniform_approx_of_continuous_within_at (mem_univ _) _,
  simpa only [exists_prop, nhds_within_univ, continuous_within_at_univ] using L
end

/-- A function which can be locally uniformly approximated by functions which are continuous
on a set is continuous on this set. -/
lemma continuous_on_of_locally_uniform_approx_of_continuous_within_at
  (L : ∀ (x ∈ s) (u ∈ 𝓤 β), ∃ (t ∈ 𝓝[s] x) F,
    continuous_within_at F s x ∧ ∀ y ∈ t, (f y, F y) ∈ u) : continuous_on f s :=
λ x hx, continuous_within_at_of_locally_uniform_approx_of_continuous_within_at hx (L x hx)

/-- A function which can be uniformly approximated by functions which are continuous on a set
is continuous on this set. -/
lemma continuous_on_of_uniform_approx_of_continuous_on
  (L : ∀ u ∈ 𝓤 β, ∃ F, continuous_on F s ∧ ∀ y ∈ s, (f y, F y) ∈ u) : continuous_on f s :=
continuous_on_of_locally_uniform_approx_of_continuous_within_at $
  λ x hx u hu, ⟨s, self_mem_nhds_within, (L u hu).imp $
    λ F hF, ⟨hF.1.continuous_within_at hx, hF.2⟩⟩

/-- A function which can be locally uniformly approximated by continuous functions is continuous. -/
lemma continuous_of_locally_uniform_approx_of_continuous_at
  (L : ∀ (x : α), ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∃ F, continuous_at F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
  continuous f :=
continuous_iff_continuous_at.2 $ λ x, continuous_at_of_locally_uniform_approx_of_continuous_at (L x)

/-- A function which can be uniformly approximated by continuous functions is continuous. -/
lemma continuous_of_uniform_approx_of_continuous
  (L : ∀ u ∈ 𝓤 β, ∃ F, continuous F ∧ ∀ y, (f y, F y) ∈ u) : continuous f :=
continuous_iff_continuous_on_univ.mpr $ continuous_on_of_uniform_approx_of_continuous_on $
  by simpa [continuous_iff_continuous_on_univ] using L

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/

/-- A locally uniform limit on a set of functions which are continuous on this set is itself
continuous on this set. -/
protected lemma tendsto_locally_uniformly_on.continuous_on
  (h : tendsto_locally_uniformly_on F f p s) (hc : ∀ᶠ n in p, continuous_on (F n) s) [ne_bot p] :
  continuous_on f s :=
begin
  apply continuous_on_of_locally_uniform_approx_of_continuous_within_at (λ x hx u hu, _),
  rcases h u hu x hx with ⟨t, ht, H⟩,
  rcases (hc.and H).exists with ⟨n, hFc, hF⟩,
  exact ⟨t, ht, ⟨F n, hFc.continuous_within_at hx, hF⟩⟩
end

/-- A uniform limit on a set of functions which are continuous on this set is itself continuous
on this set. -/
protected lemma tendsto_uniformly_on.continuous_on (h : tendsto_uniformly_on F f p s)
  (hc : ∀ᶠ n in p, continuous_on (F n) s) [ne_bot p] : continuous_on f s :=
h.tendsto_locally_uniformly_on.continuous_on hc

/-- A locally uniform limit of continuous functions is continuous. -/
protected lemma tendsto_locally_uniformly.continuous (h : tendsto_locally_uniformly F f p)
  (hc : ∀ᶠ n in p, continuous (F n)) [ne_bot p] : continuous f :=
continuous_iff_continuous_on_univ.mpr $ h.tendsto_locally_uniformly_on.continuous_on $
  hc.mono $ λ n hn, hn.continuous_on

/-- A uniform limit of continuous functions is continuous. -/
protected lemma tendsto_uniformly.continuous (h : tendsto_uniformly F f p)
  (hc : ∀ᶠ n in p, continuous (F n)) [ne_bot p] : continuous f :=
h.tendsto_locally_uniformly.continuous hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to a function `f`
which is continuous at `x` within `s `, and `gₙ` tends to `x` within `s`, then `Fₙ (gₙ)` tends
to `f x`. -/
lemma tendsto_comp_of_locally_uniform_limit_within
  (h : continuous_within_at f s x) (hg : tendsto g p (𝓝[s] x))
  (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
begin
  apply uniform.tendsto_nhds_right.2 (λ u₀ hu₀, _),
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ (u : set (β × β)) (H : u ∈ 𝓤 β), comp_rel u u ⊆ u₀ :=
    comp_mem_uniformity_sets hu₀,
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩,
  have A : ∀ᶠ n in p, g n ∈ s := hg sx,
  have B : ∀ᶠ n in p, (f x, f (g n)) ∈ u₁ := hg (uniform.continuous_within_at_iff'_right.1 h h₁),
  refine ((hs.and A).and B).mono (λ y hy, _),
  rcases hy with ⟨⟨H1, H2⟩, H3⟩,
  exact u₁₀ (prod_mk_mem_comp_rel H3 (H1 _ H2))
end

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` which is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`. -/
lemma tendsto_comp_of_locally_uniform_limit (h : continuous_at f x) (hg : tendsto g p (𝓝 x))
  (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
begin
  rw ← continuous_within_at_univ at h,
  rw ← nhds_within_univ at hunif hg,
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif
end

/-- If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`. -/
lemma tendsto_locally_uniformly_on.tendsto_comp (h : tendsto_locally_uniformly_on F f p s)
  (hf : continuous_within_at f s x) (hx : x ∈ s) (hg : tendsto g p (𝓝[s] x)) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
tendsto_comp_of_locally_uniform_limit_within hf hg (λ u hu, h u hu x hx)

/-- If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then `Fₙ gₙ`
tends to `f x` if `f` is continuous at `x` within `s`. -/
lemma tendsto_uniformly_on.tendsto_comp (h : tendsto_uniformly_on F f p s)
  (hf : continuous_within_at f s x) (hg : tendsto g p (𝓝[s] x)) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
tendsto_comp_of_locally_uniform_limit_within hf hg (λ u hu, ⟨s, self_mem_nhds_within, h u hu⟩)

/-- If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
lemma tendsto_locally_uniformly.tendsto_comp (h : tendsto_locally_uniformly F f p)
  (hf : continuous_at f x) (hg : tendsto g p (𝓝 x)) : tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
tendsto_comp_of_locally_uniform_limit hf hg (λ u hu, h u hu x)

/-- If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
lemma tendsto_uniformly.tendsto_comp (h : tendsto_uniformly F f p)
  (hf : continuous_at f x) (hg : tendsto g p (𝓝 x)) : tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
h.tendsto_locally_uniformly.tendsto_comp hf hg
