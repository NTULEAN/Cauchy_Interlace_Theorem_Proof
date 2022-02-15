/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import order.filter.pi
import topology.bases
import data.finset.order
import data.set.accumulate
import tactic.tfae

/-!
# Properties of subsets of topological spaces

In this file we define various properties of subsets of a topological space, and some classes on
topological spaces.

## Main definitions

We define the following properties for sets in a topological space:

* `is_compact`: each open cover has a finite subcover. This is defined in mathlib using filters.
  The main property of a compact set is `is_compact.elim_finite_subcover`.
* `is_clopen`: a set that is both open and closed.
* `is_irreducible`: a nonempty set that has contains no non-trivial pair of disjoint opens.
  See also the section below in the module doc.

For each of these definitions (except for `is_clopen`), we also have a class stating that the whole
space satisfies that property:
`compact_space`, `irreducible_space`

Furthermore, we have three more classes:
* `locally_compact_space`: for every point `x`, every open neighborhood of `x` contains a compact
  neighborhood of `x`. The definition is formulated in terms of the neighborhood filter.
* `sigma_compact_space`: a space that is the union of a countably many compact subspaces;
* `noncompact_space`: a space that is not a compact space.

## On the definition of irreducible and connected sets/spaces

In informal mathematics, irreducible spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `is_preirreducible`.
In other words, the only difference is whether the empty space counts as irreducible.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/

open set filter classical topological_space
open_locale classical topological_space filter

universes u v
variables {α : Type u} {β : Type v}  {ι : Type*} {π : ι → Type*}
variables [topological_space α] [topological_space β] {s t : set α}

/- compact sets -/
section compact

/-- A set `s` is compact if for every nontrivial filter `f` that contains `s`,
    there exists `a ∈ s` such that every set of `f` meets every neighborhood of `a`. -/
def is_compact (s : set α) := ∀ ⦃f⦄ [ne_bot f], f ≤ 𝓟 s → ∃ a ∈ s, cluster_pt a f

/-- The complement to a compact set belongs to a filter `f` if it belongs to each filter
`𝓝 a ⊓ f`, `a ∈ s`. -/
lemma is_compact.compl_mem_sets (hs : is_compact s) {f : filter α} (hf : ∀ a ∈ s, sᶜ ∈ 𝓝 a ⊓ f) :
  sᶜ ∈ f :=
begin
  contrapose! hf,
  simp only [not_mem_iff_inf_principal_compl, compl_compl, inf_assoc, ← exists_prop] at hf ⊢,
  exact @hs _ hf inf_le_right
end

/-- The complement to a compact set belongs to a filter `f` if each `a ∈ s` has a neighborhood `t`
within `s` such that `tᶜ` belongs to `f`. -/
lemma is_compact.compl_mem_sets_of_nhds_within (hs : is_compact s) {f : filter α}
  (hf : ∀ a ∈ s, ∃ t ∈ 𝓝[s] a, tᶜ ∈ f) :
  sᶜ ∈ f :=
begin
  refine hs.compl_mem_sets (λ a ha, _),
  rcases hf a ha with ⟨t, ht, hst⟩,
  replace ht := mem_inf_principal.1 ht,
  apply mem_inf_of_inter ht hst,
  rintros x ⟨h₁, h₂⟩ hs,
  exact h₂ (h₁ hs)
end

/-- If `p : set α → Prop` is stable under restriction and union, and each point `x`
  of a compact set `s` has a neighborhood `t` within `s` such that `p t`, then `p s` holds. -/
@[elab_as_eliminator]
lemma is_compact.induction_on {s : set α} (hs : is_compact s) {p : set α → Prop} (he : p ∅)
  (hmono : ∀ ⦃s t⦄, s ⊆ t → p t → p s) (hunion : ∀ ⦃s t⦄, p s → p t → p (s ∪ t))
  (hnhds : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, p t) :
  p s :=
let f : filter α :=
  { sets := {t | p tᶜ},
    univ_sets := by simpa,
    sets_of_superset := λ t₁ t₂ ht₁ ht, hmono (compl_subset_compl.2 ht) ht₁,
    inter_sets := λ t₁ t₂ ht₁ ht₂, by simp [compl_inter, hunion ht₁ ht₂] } in
have sᶜ ∈ f, from hs.compl_mem_sets_of_nhds_within (by simpa using hnhds),
by simpa

/-- The intersection of a compact set and a closed set is a compact set. -/
lemma is_compact.inter_right (hs : is_compact s) (ht : is_closed t) :
  is_compact (s ∩ t) :=
begin
  introsI f hnf hstf,
  obtain ⟨a, hsa, ha⟩ : ∃ a ∈ s, cluster_pt a f :=
    hs (le_trans hstf (le_principal_iff.2 (inter_subset_left _ _))),
  have : a ∈ t :=
    (ht.mem_of_nhds_within_ne_bot $ ha.mono $
      le_trans hstf (le_principal_iff.2 (inter_subset_right _ _))),
  exact ⟨a, ⟨hsa, this⟩, ha⟩
end

/-- The intersection of a closed set and a compact set is a compact set. -/
lemma is_compact.inter_left (ht : is_compact t) (hs : is_closed s) : is_compact (s ∩ t) :=
inter_comm t s ▸ ht.inter_right hs

/-- The set difference of a compact set and an open set is a compact set. -/
lemma is_compact.diff (hs : is_compact s) (ht : is_open t) : is_compact (s \ t) :=
hs.inter_right (is_closed_compl_iff.mpr ht)

/-- A closed subset of a compact set is a compact set. -/
lemma compact_of_is_closed_subset (hs : is_compact s) (ht : is_closed t) (h : t ⊆ s) :
  is_compact t :=
inter_eq_self_of_subset_right h ▸ hs.inter_right ht

lemma is_compact.image_of_continuous_on {f : α → β} (hs : is_compact s) (hf : continuous_on f s) :
  is_compact (f '' s) :=
begin
  intros l lne ls,
  have : ne_bot (l.comap f ⊓ 𝓟 s) :=
    comap_inf_principal_ne_bot_of_image_mem lne (le_principal_iff.1 ls),
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, cluster_pt a (l.comap f ⊓ 𝓟 s) := @@hs this inf_le_right,
  use [f a, mem_image_of_mem f has],
  have : tendsto f (𝓝 a ⊓ (comap f l ⊓ 𝓟 s)) (𝓝 (f a) ⊓ l),
  { convert (hf a has).inf (@tendsto_comap _ _ f l) using 1,
    rw nhds_within,
    ac_refl },
  exact @@tendsto.ne_bot _ this ha,
end

lemma is_compact.image {f : α → β} (hs : is_compact s) (hf : continuous f) :
  is_compact (f '' s) :=
hs.image_of_continuous_on hf.continuous_on

lemma is_compact.adherence_nhdset {f : filter α}
  (hs : is_compact s) (hf₂ : f ≤ 𝓟 s) (ht₁ : is_open t) (ht₂ : ∀ a ∈ s, cluster_pt a f → a ∈ t) :
  t ∈ f :=
classical.by_cases mem_of_eq_bot $
  assume : f ⊓ 𝓟 tᶜ ≠ ⊥,
  let ⟨a, ha, (hfa : cluster_pt a $ f ⊓ 𝓟 tᶜ)⟩ := @@hs ⟨this⟩ $ inf_le_of_left_le hf₂ in
  have a ∈ t,
    from ht₂ a ha (hfa.of_inf_left),
  have tᶜ ∩ t ∈ 𝓝[tᶜ] a,
    from inter_mem_nhds_within _ (is_open.mem_nhds ht₁ this),
  have A : 𝓝[tᶜ] a = ⊥,
    from empty_mem_iff_bot.1 $ compl_inter_self t ▸ this,
  have 𝓝[tᶜ] a ≠ ⊥,
    from hfa.of_inf_right.ne,
  absurd A this

lemma is_compact_iff_ultrafilter_le_nhds :
  is_compact s ↔ (∀ f : ultrafilter α, ↑f ≤ 𝓟 s → ∃ a ∈ s, ↑f ≤ 𝓝 a) :=
begin
  refine (forall_ne_bot_le_iff _).trans _,
  { rintro f g hle ⟨a, has, haf⟩,
    exact ⟨a, has, haf.mono hle⟩ },
  { simp only [ultrafilter.cluster_pt_iff] }
end

alias is_compact_iff_ultrafilter_le_nhds ↔ is_compact.ultrafilter_le_nhds _

/-- For every open directed cover of a compact set, there exists a single element of the
cover which itself includes the set. -/
lemma is_compact.elim_directed_cover {ι : Type v} [hι : nonempty ι] (hs : is_compact s)
  (U : ι → set α) (hUo : ∀ i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) (hdU : directed (⊆) U) :
  ∃ i, s ⊆ U i :=
hι.elim $ λ i₀, is_compact.induction_on hs ⟨i₀, empty_subset _⟩
  (λ s₁ s₂ hs ⟨i, hi⟩, ⟨i, subset.trans hs hi⟩)
  (λ s₁ s₂ ⟨i, hi⟩ ⟨j, hj⟩, let ⟨k, hki, hkj⟩ := hdU i j in
    ⟨k, union_subset (subset.trans hi hki) (subset.trans hj hkj)⟩)
  (λ x hx, let ⟨i, hi⟩ := mem_Union.1 (hsU hx) in
    ⟨U i, mem_nhds_within_of_mem_nhds (is_open.mem_nhds (hUo i) hi), i, subset.refl _⟩)

/-- For every open cover of a compact set, there exists a finite subcover. -/
lemma is_compact.elim_finite_subcover {ι : Type v} (hs : is_compact s)
  (U : ι → set α) (hUo : ∀ i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) :
  ∃ t : finset ι, s ⊆ ⋃ i ∈ t, U i :=
hs.elim_directed_cover _ (λ t, is_open_bUnion $ λ i _, hUo i) (Union_eq_Union_finset U ▸ hsU)
  (directed_of_sup $ λ t₁ t₂ h, bUnion_subset_bUnion_left h)

lemma is_compact.elim_nhds_subcover' (hs : is_compact s) (U : Π x ∈ s, set α)
  (hU : ∀ x ∈ s, U x ‹x ∈ s› ∈ 𝓝 x) :
  ∃ t : finset s, s ⊆ ⋃ x ∈ t, U (x : s) x.2 :=
(hs.elim_finite_subcover (λ x : s, interior (U x x.2)) (λ x, is_open_interior)
  (λ x hx, mem_Union.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 $ hU _ _⟩)).imp $ λ t ht,
subset.trans ht $ Union₂_mono $ λ _ _, interior_subset

lemma is_compact.elim_nhds_subcover (hs : is_compact s) (U : α → set α) (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
  ∃ t : finset α, (∀ x ∈ t, x ∈ s) ∧ s ⊆ ⋃ x ∈ t, U x :=
let ⟨t, ht⟩ := hs.elim_nhds_subcover' (λ x _, U x) hU
in ⟨t.image coe, λ x hx, let ⟨y, hyt, hyx⟩ := finset.mem_image.1 hx in hyx ▸ y.2,
  by rwa finset.set_bUnion_finset_image⟩

/-- For every family of closed sets whose intersection avoids a compact set,
there exists a finite subfamily whose intersection avoids this compact set. -/
lemma is_compact.elim_finite_subfamily_closed {s : set α} {ι : Type v} (hs : is_compact s)
  (Z : ι → set α) (hZc : ∀ i, is_closed (Z i)) (hsZ : s ∩ (⋂ i, Z i) = ∅) :
  ∃ t : finset ι, s ∩ (⋂ i ∈ t, Z i) = ∅ :=
let ⟨t, ht⟩ := hs.elim_finite_subcover (λ i, (Z i)ᶜ) (λ i, (hZc i).is_open_compl)
  (by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
    exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using hsZ)
    in
⟨t, by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
    exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using ht⟩

/-- If `s` is a compact set in a topological space `α` and `f : ι → set α` is a locally finite
family of sets, then `f i ∩ s` is nonempty only for a finitely many `i`. -/
lemma locally_finite.finite_nonempty_inter_compact {ι : Type*} {f : ι → set α}
  (hf : locally_finite f) {s : set α} (hs : is_compact s) :
  finite {i | (f i ∩ s).nonempty} :=
begin
  choose U hxU hUf using hf,
  rcases hs.elim_nhds_subcover U (λ x _, hxU x) with ⟨t, -, hsU⟩,
  refine (t.finite_to_set.bUnion (λ x _, hUf x)).subset _,
  rintro i ⟨x, hx⟩,
  rcases mem_Union₂.1 (hsU hx.2) with ⟨c, hct, hcx⟩,
  exact mem_bUnion hct ⟨x, hx.1, hcx⟩
end

/-- To show that a compact set intersects the intersection of a family of closed sets,
  it is sufficient to show that it intersects every finite subfamily. -/
lemma is_compact.inter_Inter_nonempty {s : set α} {ι : Type v} (hs : is_compact s)
  (Z : ι → set α) (hZc : ∀ i, is_closed (Z i)) (hsZ : ∀ t : finset ι, (s ∩ ⋂ i ∈ t, Z i).nonempty) :
  (s ∩ ⋂ i, Z i).nonempty :=
begin
  simp only [← ne_empty_iff_nonempty] at hsZ ⊢,
  apply mt (hs.elim_finite_subfamily_closed Z hZc), push_neg, exact hsZ
end

/-- Cantor's intersection theorem:
the intersection of a directed family of nonempty compact closed sets is nonempty. -/
lemma is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
  {ι : Type v} [hι : nonempty ι] (Z : ι → set α) (hZd : directed (⊇) Z)
  (hZn : ∀ i, (Z i).nonempty) (hZc : ∀ i, is_compact (Z i)) (hZcl : ∀ i, is_closed (Z i)) :
  (⋂ i, Z i).nonempty :=
begin
  apply hι.elim,
  intro i₀,
  let Z' := λ i, Z i ∩ Z i₀,
  suffices : (⋂ i, Z' i).nonempty,
  { exact this.mono (Inter_mono $ λ i, inter_subset_left (Z i) (Z i₀)) },
  rw ← ne_empty_iff_nonempty,
  intro H,
  obtain ⟨t, ht⟩ : ∃ (t : finset ι), ((Z i₀) ∩ ⋂ (i ∈ t), Z' i) = ∅,
    from (hZc i₀).elim_finite_subfamily_closed Z'
      (assume i, is_closed.inter (hZcl i) (hZcl i₀)) (by rw [H, inter_empty]),
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : ι, Z i₁ ⊆ Z i₀ ∧ ∀ i ∈ t, Z i₁ ⊆ Z' i,
  { rcases directed.finset_le hZd t with ⟨i, hi⟩,
    rcases hZd i i₀ with ⟨i₁, hi₁, hi₁₀⟩,
    use [i₁, hi₁₀],
    intros j hj,
    exact subset_inter (subset.trans hi₁ (hi j hj)) hi₁₀ },
  suffices : ((Z i₀) ∩ ⋂ (i ∈ t), Z' i).nonempty,
  { rw ← ne_empty_iff_nonempty at this, contradiction },
  exact (hZn i₁).mono (subset_inter hi₁.left $ subset_Inter₂ hi₁.right),
end

/-- Cantor's intersection theorem for sequences indexed by `ℕ`:
the intersection of a decreasing sequence of nonempty compact closed sets is nonempty. -/
lemma is_compact.nonempty_Inter_of_sequence_nonempty_compact_closed
  (Z : ℕ → set α) (hZd : ∀ i, Z (i+1) ⊆ Z i)
  (hZn : ∀ i, (Z i).nonempty) (hZ0 : is_compact (Z 0)) (hZcl : ∀ i, is_closed (Z i)) :
  (⋂ i, Z i).nonempty :=
have Zmono : antitone Z := antitone_nat_of_succ_le hZd,
have hZd : directed (⊇) Z, from directed_of_sup Zmono,
have ∀ i, Z i ⊆ Z 0, from assume i, Zmono $ zero_le i,
have hZc : ∀ i, is_compact (Z i), from assume i, compact_of_is_closed_subset hZ0 (hZcl i) (this i),
is_compact.nonempty_Inter_of_directed_nonempty_compact_closed Z hZd hZn hZc hZcl

/-- For every open cover of a compact set, there exists a finite subcover. -/
lemma is_compact.elim_finite_subcover_image {b : set ι} {c : ι → set α}
  (hs : is_compact s) (hc₁ : ∀ i ∈ b, is_open (c i)) (hc₂ : s ⊆ ⋃ i ∈ b, c i) :
  ∃ b' ⊆ b, finite b' ∧ s ⊆ ⋃ i ∈ b', c i :=
begin
  rcases hs.elim_finite_subcover (λ i, c i : b → set α) _ _ with ⟨d, hd⟩;
    [skip, simpa using hc₁, simpa using hc₂],
  refine ⟨↑(d.image coe), _, finset.finite_to_set _, _⟩,
  { simp },
  { rwa [finset.coe_image, bUnion_image] }
end

/-- A set `s` is compact if for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem is_compact_of_finite_subfamily_closed
  (h : Π {ι : Type u} (Z : ι → (set α)), (∀ i, is_closed (Z i)) →
    s ∩ (⋂ i, Z i) = ∅ → (∃ (t : finset ι), s ∩ (⋂ i ∈ t, Z i) = ∅)) :
  is_compact s :=
assume f hfn hfs, classical.by_contradiction $ assume : ¬ (∃ x ∈ s, cluster_pt x f),
  have hf : ∀ x ∈ s, 𝓝 x ⊓ f = ⊥,
    by simpa only [cluster_pt, not_exists, not_not, ne_bot_iff],
  have ¬ ∃ x ∈ s, ∀ t ∈ f.sets, x ∈ closure t,
    from assume ⟨x, hxs, hx⟩,
    have ∅ ∈ 𝓝 x ⊓ f, by rw [empty_mem_iff_bot, hf x hxs],
    let ⟨t₁, ht₁, t₂, ht₂, ht⟩ := by rw [mem_inf_iff] at this; exact this in
    have ∅ ∈ 𝓝[t₂] x,
      by { rw [ht, inter_comm], exact inter_mem_nhds_within _ ht₁ },
    have 𝓝[t₂] x = ⊥,
      by rwa [empty_mem_iff_bot] at this,
    by simp only [closure_eq_cluster_pts] at hx; exact (hx t₂ ht₂).ne this,
  let ⟨t, ht⟩ := h (λ i : f.sets, closure i.1) (λ i, is_closed_closure)
    (by simpa [eq_empty_iff_forall_not_mem, not_exists]) in
  have (⋂ i ∈ t, subtype.val i) ∈ f,
    from t.Inter_mem_sets.2 $ assume i hi, i.2,
  have s ∩ (⋂ i ∈ t, subtype.val i) ∈ f,
    from inter_mem (le_principal_iff.1 hfs) this,
  have ∅ ∈ f,
    from mem_of_superset this $ assume x ⟨hxs, hx⟩,
    let ⟨i, hit, hxi⟩ := (show ∃ i ∈ t, x ∉ closure (subtype.val i),
      by { rw [eq_empty_iff_forall_not_mem] at ht, simpa [hxs, not_forall] using ht x }) in
    have x ∈ closure i.val, from subset_closure (by { rw mem_Inter₂ at hx, exact hx i hit }),
    show false, from hxi this,
  hfn.ne $ by rwa [empty_mem_iff_bot] at this

/-- A set `s` is compact if for every open cover of `s`, there exists a finite subcover. -/
lemma is_compact_of_finite_subcover
  (h : Π {ι : Type u} (U : ι → (set α)), (∀ i, is_open (U i)) →
    s ⊆ (⋃ i, U i) → (∃ (t : finset ι), s ⊆ (⋃ i ∈ t, U i))) :
  is_compact s :=
is_compact_of_finite_subfamily_closed $
  assume ι Z hZc hsZ,
  let ⟨t, ht⟩ := h (λ i, (Z i)ᶜ) (assume i, is_open_compl_iff.mpr $ hZc i)
    (by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
      exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using hsZ)
      in
  ⟨t, by simpa only [subset_def, not_forall, eq_empty_iff_forall_not_mem, mem_Union,
      exists_prop, mem_inter_eq, not_and, iff_self, mem_Inter, mem_compl_eq] using ht⟩

/-- A set `s` is compact if and only if
for every open cover of `s`, there exists a finite subcover. -/
lemma is_compact_iff_finite_subcover :
  is_compact s ↔ (Π {ι : Type u} (U : ι → (set α)), (∀ i, is_open (U i)) →
    s ⊆ (⋃ i, U i) → (∃ (t : finset ι), s ⊆ (⋃ i ∈ t, U i))) :=
⟨assume hs ι, hs.elim_finite_subcover, is_compact_of_finite_subcover⟩

/-- A set `s` is compact if and only if
for every family of closed sets whose intersection avoids `s`,
there exists a finite subfamily whose intersection avoids `s`. -/
theorem is_compact_iff_finite_subfamily_closed :
  is_compact s ↔ (Π {ι : Type u} (Z : ι → (set α)), (∀ i, is_closed (Z i)) →
    s ∩ (⋂ i, Z i) = ∅ → (∃ (t : finset ι), s ∩ (⋂ i ∈ t, Z i) = ∅)) :=
⟨assume hs ι, hs.elim_finite_subfamily_closed, is_compact_of_finite_subfamily_closed⟩

/--
To show that `∀ y ∈ K, P x y` holds for `x` close enough to `x₀` when `K` is compact,
it is sufficient to show that for all `y₀ ∈ K` there `P x y` holds for `(x, y)` close enough
to `(x₀, y₀)`.
-/
lemma is_compact.eventually_forall_of_forall_eventually {x₀ : α} {K : set β} (hK : is_compact K)
  {P : α → β → Prop} (hP : ∀ y ∈ K, ∀ᶠ (z : α × β) in 𝓝 (x₀, y), P z.1 z.2):
  ∀ᶠ x in 𝓝 x₀, ∀ y ∈ K, P x y :=
begin
  refine hK.induction_on _ _ _ _,
  { exact eventually_of_forall (λ x y, false.elim) },
  { intros s t hst ht, refine ht.mono (λ x h y hys, h y $ hst hys) },
  { intros s t hs ht, filter_upwards [hs, ht], rintro x h1 h2 y (hys|hyt),
    exacts [h1 y hys, h2 y hyt] },
  { intros y hyK,
    specialize hP y hyK,
    rw [nhds_prod_eq, eventually_prod_iff] at hP,
    rcases hP with ⟨p, hp, q, hq, hpq⟩,
    exact ⟨{y | q y}, mem_nhds_within_of_mem_nhds hq, eventually_of_mem hp @hpq⟩ }
end

@[simp]
lemma is_compact_empty : is_compact (∅ : set α) :=
assume f hnf hsf, not.elim hnf.ne $
empty_mem_iff_bot.1 $ le_principal_iff.1 hsf

@[simp]
lemma is_compact_singleton {a : α} : is_compact ({a} : set α) :=
λ f hf hfa, ⟨a, rfl, cluster_pt.of_le_nhds'
  (hfa.trans $ by simpa only [principal_singleton] using pure_le_nhds a) hf⟩

lemma set.subsingleton.is_compact {s : set α} (hs : s.subsingleton) : is_compact s :=
subsingleton.induction_on hs is_compact_empty $ λ x, is_compact_singleton

lemma set.finite.compact_bUnion {s : set ι} {f : ι → set α} (hs : finite s)
  (hf : ∀ i ∈ s, is_compact (f i)) :
  is_compact (⋃ i ∈ s, f i) :=
is_compact_of_finite_subcover $ assume ι U hUo hsU,
  have ∀ i : subtype s, ∃ t : finset ι, f i ⊆ (⋃ j ∈ t, U j), from
    assume ⟨i, hi⟩, (hf i hi).elim_finite_subcover _ hUo
      (calc f i ⊆ ⋃ i ∈ s, f i : subset_bUnion_of_mem hi
            ... ⊆ ⋃ j, U j     : hsU),
  let ⟨finite_subcovers, h⟩ := axiom_of_choice this in
  by haveI : fintype (subtype s) := hs.fintype; exact
  let t := finset.bUnion finset.univ finite_subcovers in
  have (⋃ i ∈ s, f i) ⊆ (⋃ i ∈ t, U i), from Union₂_subset $
    assume i hi, calc
    f i ⊆ (⋃ j ∈ finite_subcovers ⟨i, hi⟩, U j) : (h ⟨i, hi⟩)
    ... ⊆ (⋃ j ∈ t, U j) : bUnion_subset_bUnion_left $
      assume j hj, finset.mem_bUnion.mpr ⟨_, finset.mem_univ _, hj⟩,
  ⟨t, this⟩

lemma finset.compact_bUnion (s : finset ι) {f : ι → set α} (hf : ∀ i ∈ s, is_compact (f i)) :
  is_compact (⋃ i ∈ s, f i) :=
s.finite_to_set.compact_bUnion hf

lemma compact_accumulate {K : ℕ → set α} (hK : ∀ n, is_compact (K n)) (n : ℕ) :
  is_compact (accumulate K n) :=
(finite_le_nat n).compact_bUnion $ λ k _, hK k

lemma compact_Union {f : ι → set α} [fintype ι]
  (h : ∀ i, is_compact (f i)) : is_compact (⋃ i, f i) :=
by rw ← bUnion_univ; exact finite_univ.compact_bUnion (λ i _, h i)

lemma set.finite.is_compact (hs : finite s) : is_compact s :=
bUnion_of_singleton s ▸ hs.compact_bUnion (λ _ _, is_compact_singleton)

lemma is_compact.finite_of_discrete [discrete_topology α] {s : set α} (hs : is_compact s) :
  s.finite :=
begin
  have : ∀ x : α, ({x} : set α) ∈ 𝓝 x, by simp [nhds_discrete],
  rcases hs.elim_nhds_subcover (λ x, {x}) (λ x hx, this x) with ⟨t, hts, hst⟩,
  simp only [← t.set_bUnion_coe, bUnion_of_singleton] at hst,
  exact t.finite_to_set.subset hst
end

lemma is_compact_iff_finite [discrete_topology α] {s : set α} : is_compact s ↔ s.finite :=
⟨λ h, h.finite_of_discrete, λ h, h.is_compact⟩

lemma is_compact.union (hs : is_compact s) (ht : is_compact t) : is_compact (s ∪ t) :=
by rw union_eq_Union; exact compact_Union (λ b, by cases b; assumption)

lemma is_compact.insert (hs : is_compact s) (a) : is_compact (insert a s) :=
is_compact_singleton.union hs

/-- If `V : ι → set α` is a decreasing family of closed compact sets then any neighborhood of
`⋂ i, V i` contains some `V i`. We assume each `V i` is compact *and* closed because `α` is
not assumed to be Hausdorff. See `exists_subset_nhd_of_compact` for version assuming this. -/
lemma exists_subset_nhd_of_compact' {ι : Type*} [nonempty ι] {V : ι → set α} (hV : directed (⊇) V)
  (hV_cpct : ∀ i, is_compact (V i)) (hV_closed : ∀ i, is_closed (V i))
  {U : set α} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
begin
  obtain ⟨W, hsubW, W_op, hWU⟩ := exists_open_set_nhds hU,
  suffices : ∃ i, V i ⊆ W,
  { rcases this with ⟨i, hi⟩,
    refine ⟨i, set.subset.trans hi hWU⟩ },
  by_contra' H,
  replace H : ∀ i, (V i ∩ Wᶜ).nonempty := λ i, set.inter_compl_nonempty_iff.mpr (H i),
  have : (⋂ i, V i ∩ Wᶜ).nonempty,
  { refine is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ (λ i j, _) H
      (λ i, (hV_cpct i).inter_right W_op.is_closed_compl)
      (λ i, (hV_closed i).inter W_op.is_closed_compl),
    rcases hV i j with ⟨k, hki, hkj⟩,
    refine ⟨k, ⟨λ x, _, λ x, _⟩⟩ ; simp only [and_imp, mem_inter_eq, mem_compl_eq] ; tauto },
  have : ¬ (⋂ (i : ι), V i) ⊆ W, by simpa [← Inter_inter, inter_compl_nonempty_iff],
  contradiction
end

namespace filter

/-- `filter.cocompact` is the filter generated by complements to compact sets. -/
def cocompact (α : Type*) [topological_space α] : filter α :=
⨅ (s : set α) (hs : is_compact s), 𝓟 (sᶜ)

lemma has_basis_cocompact : (cocompact α).has_basis is_compact compl :=
has_basis_binfi_principal'
  (λ s hs t ht, ⟨s ∪ t, hs.union ht, compl_subset_compl.2 (subset_union_left s t),
    compl_subset_compl.2 (subset_union_right s t)⟩)
  ⟨∅, is_compact_empty⟩

lemma mem_cocompact : s ∈ cocompact α ↔ ∃ t, is_compact t ∧ tᶜ ⊆ s :=
has_basis_cocompact.mem_iff.trans $ exists_congr $ λ t, exists_prop

lemma mem_cocompact' : s ∈ cocompact α ↔ ∃ t, is_compact t ∧ sᶜ ⊆ t :=
mem_cocompact.trans $ exists_congr $ λ t, and_congr_right $ λ ht, compl_subset_comm

lemma _root_.is_compact.compl_mem_cocompact (hs : is_compact s) : sᶜ ∈ filter.cocompact α :=
has_basis_cocompact.mem_of_mem hs

lemma cocompact_le_cofinite : cocompact α ≤ cofinite :=
λ s hs, compl_compl s ▸ hs.is_compact.compl_mem_cocompact

lemma cocompact_eq_cofinite (α : Type*) [topological_space α] [discrete_topology α] :
  cocompact α = cofinite :=
has_basis_cocompact.eq_of_same_basis $
  by { convert has_basis_cofinite, ext s, exact is_compact_iff_finite }

@[simp] lemma _root_.nat.cocompact_eq : cocompact ℕ = at_top :=
(cocompact_eq_cofinite ℕ).trans nat.cofinite_eq_at_top

lemma tendsto.is_compact_insert_range_of_cocompact {f : α → β} {b}
  (hf : tendsto f (cocompact α) (𝓝 b)) (hfc : continuous f) :
  is_compact (insert b (range f)) :=
begin
  introsI l hne hle,
  by_cases hb : cluster_pt b l, { exact ⟨b, or.inl rfl, hb⟩ },
  simp only [cluster_pt_iff, not_forall, ← not_disjoint_iff_nonempty_inter, not_not] at hb,
  rcases hb with ⟨s, hsb, t, htl, hd⟩,
  rcases mem_cocompact.1 (hf hsb) with ⟨K, hKc, hKs⟩,
  have : f '' K ∈ l,
  { filter_upwards [htl, le_principal_iff.1 hle] with y hyt hyf,
    rcases hyf with (rfl|⟨x, rfl⟩),
    exacts [(hd ⟨mem_of_mem_nhds hsb, hyt⟩).elim,
      mem_image_of_mem _ (not_not.1 $ λ hxK, hd ⟨hKs hxK, hyt⟩)] },
  rcases hKc.image hfc (le_principal_iff.2 this) with ⟨y, hy, hyl⟩,
  exact ⟨y, or.inr $ image_subset_range _ _ hy, hyl⟩
end

lemma tendsto.is_compact_insert_range_of_cofinite {f : ι → α} {a}
  (hf : tendsto f cofinite (𝓝 a)) :
  is_compact (insert a (range f)) :=
begin
  letI : topological_space ι := ⊥, haveI : discrete_topology ι := ⟨rfl⟩,
  rw ← cocompact_eq_cofinite at hf,
  exact hf.is_compact_insert_range_of_cocompact continuous_of_discrete_topology
end

lemma tendsto.is_compact_insert_range {f : ℕ → α} {a} (hf : tendsto f at_top (𝓝 a)) :
  is_compact (insert a (range f)) :=
filter.tendsto.is_compact_insert_range_of_cofinite $ nat.cofinite_eq_at_top.symm ▸ hf

/-- `filter.coclosed_compact` is the filter generated by complements to closed compact sets.
In a Hausdorff space, this is the same as `filter.cocompact`. -/
def coclosed_compact (α : Type*) [topological_space α] : filter α :=
⨅ (s : set α) (h₁ : is_closed s) (h₂ : is_compact s), 𝓟 (sᶜ)

lemma has_basis_coclosed_compact :
  (filter.coclosed_compact α).has_basis (λ s, is_closed s ∧ is_compact s) compl :=
begin
  simp only [filter.coclosed_compact, infi_and'],
  refine has_basis_binfi_principal' _ ⟨∅, is_closed_empty, is_compact_empty⟩,
  rintro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩,
  exact ⟨s ∪ t, ⟨⟨hs₁.union ht₁, hs₂.union ht₂⟩, compl_subset_compl.2 (subset_union_left _ _),
    compl_subset_compl.2 (subset_union_right _ _)⟩⟩
end

lemma mem_coclosed_compact : s ∈ coclosed_compact α ↔ ∃ t, is_closed t ∧ is_compact t ∧ tᶜ ⊆ s :=
by simp [has_basis_coclosed_compact.mem_iff, and_assoc]

lemma mem_coclosed_compact' : s ∈ coclosed_compact α ↔ ∃ t, is_closed t ∧ is_compact t ∧ sᶜ ⊆ t :=
by simp only [mem_coclosed_compact, compl_subset_comm]

lemma cocompact_le_coclosed_compact : cocompact α ≤ coclosed_compact α :=
infi_le_infi $ λ s, le_infi $ λ _, le_rfl

end filter

section tube_lemma

/-- `nhds_contain_boxes s t` means that any open neighborhood of `s × t` in `α × β` includes
a product of an open neighborhood of `s` by an open neighborhood of `t`. -/
def nhds_contain_boxes (s : set α) (t : set β) : Prop :=
∀ (n : set (α × β)) (hn : is_open n) (hp : s ×ˢ t ⊆ n),
∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n

lemma nhds_contain_boxes.symm {s : set α} {t : set β} :
  nhds_contain_boxes s t → nhds_contain_boxes t s :=
assume H n hn hp,
  let ⟨u, v, uo, vo, su, tv, p⟩ :=
    H (prod.swap ⁻¹' n)
      (hn.preimage continuous_swap)
      (by rwa [←image_subset_iff, image_swap_prod]) in
  ⟨v, u, vo, uo, tv, su,
    by rwa [←image_subset_iff, image_swap_prod] at p⟩

lemma nhds_contain_boxes.comm {s : set α} {t : set β} :
  nhds_contain_boxes s t ↔ nhds_contain_boxes t s :=
iff.intro nhds_contain_boxes.symm nhds_contain_boxes.symm

lemma nhds_contain_boxes_of_singleton {x : α} {y : β} :
  nhds_contain_boxes ({x} : set α) ({y} : set β) :=
assume n hn hp,
  let ⟨u, v, uo, vo, xu, yv, hp'⟩ :=
    is_open_prod_iff.mp hn x y (hp $ by simp) in
  ⟨u, v, uo, vo, by simpa, by simpa, hp'⟩

lemma nhds_contain_boxes_of_compact {s : set α} (hs : is_compact s) (t : set β)
  (H : ∀ x ∈ s, nhds_contain_boxes ({x} : set α) t) : nhds_contain_boxes s t :=
assume n hn hp,
have ∀ x : s, ∃ uv : set α × set β,
     is_open uv.1 ∧ is_open uv.2 ∧ {↑x} ⊆ uv.1 ∧ t ⊆ uv.2 ∧ uv.1 ×ˢ uv.2 ⊆ n,
  from assume ⟨x, hx⟩,
    have ({x} : set α) ×ˢ t ⊆ n, from
      subset.trans (prod_mono (by simpa) subset.rfl) hp,
    let ⟨ux,vx,H1⟩ := H x hx n hn this in ⟨⟨ux,vx⟩,H1⟩,
let ⟨uvs, h⟩ := classical.axiom_of_choice this in
have us_cover : s ⊆ ⋃ i, (uvs i).1, from
  assume x hx, subset_Union _ ⟨x,hx⟩ (by simpa using (h ⟨x,hx⟩).2.2.1),
let ⟨s0, s0_cover⟩ :=
  hs.elim_finite_subcover _ (λi, (h i).1) us_cover in
let u := ⋃(i ∈ s0), (uvs i).1 in
let v := ⋂(i ∈ s0), (uvs i).2 in
have is_open u, from is_open_bUnion (λi _, (h i).1),
have is_open v, from is_open_bInter s0.finite_to_set (λi _, (h i).2.1),
have t ⊆ v, from subset_Inter₂ (λi _, (h i).2.2.2.1),
have u ×ˢ v ⊆ n, from assume ⟨x',y'⟩ ⟨hx',hy'⟩,
  have ∃ i ∈ s0, x' ∈ (uvs i).1, by simpa using hx',
  let ⟨i,is0,hi⟩ := this in
  (h i).2.2.2.2 ⟨hi, (bInter_subset_of_mem is0 : v ⊆ (uvs i).2) hy'⟩,
⟨u, v, ‹is_open u›, ‹is_open v›, s0_cover, ‹t ⊆ v›, ‹u ×ˢ v ⊆ n›⟩

/-- If `s` and `t` are compact sets and `n` is an open neighborhood of `s × t`, then there exist
open neighborhoods `u ⊇ s` and `v ⊇ t` such that `u × v ⊆ n`. -/
lemma generalized_tube_lemma {s : set α} (hs : is_compact s) {t : set β} (ht : is_compact t)
  {n : set (α × β)} (hn : is_open n) (hp : s ×ˢ t ⊆ n) :
  ∃ (u : set α) (v : set β), is_open u ∧ is_open v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n :=
have _, from
  nhds_contain_boxes_of_compact hs t $ assume x _, nhds_contain_boxes.symm $
    nhds_contain_boxes_of_compact ht {x} $ assume y _, nhds_contain_boxes_of_singleton,
this n hn hp

end tube_lemma

/-- Type class for compact spaces. Separation is sometimes included in the definition, especially
in the French literature, but we do not include it here. -/
class compact_space (α : Type*) [topological_space α] : Prop :=
(compact_univ : is_compact (univ : set α))

@[priority 10] -- see Note [lower instance priority]
instance subsingleton.compact_space [subsingleton α] : compact_space α :=
⟨subsingleton_univ.is_compact⟩

lemma is_compact_univ_iff : is_compact (univ : set α) ↔ compact_space α := ⟨λ h, ⟨h⟩, λ h, h.1⟩

lemma compact_univ [h : compact_space α] : is_compact (univ : set α) := h.compact_univ

lemma cluster_point_of_compact [compact_space α] (f : filter α) [ne_bot f] :
  ∃ x, cluster_pt x f :=
by simpa using compact_univ (show f ≤ 𝓟 univ, by simp)

lemma compact_space.elim_nhds_subcover [compact_space α]
  (U : α → set α) (hU : ∀ x, U x ∈ 𝓝 x) :
  ∃ t : finset α, (⋃ x ∈ t, U x) = ⊤ :=
begin
  obtain ⟨t, -, s⟩ := is_compact.elim_nhds_subcover compact_univ U (λ x m, hU x),
  exact ⟨t, by { rw eq_top_iff, exact s }⟩,
end

theorem compact_space_of_finite_subfamily_closed
  (h : Π {ι : Type u} (Z : ι → (set α)), (∀ i, is_closed (Z i)) →
    (⋂ i, Z i) = ∅ → ∃ (t : finset ι), (⋂ i ∈ t, Z i) = ∅) :
  compact_space α :=
{ compact_univ :=
  begin
    apply is_compact_of_finite_subfamily_closed,
    intros ι Z, specialize h Z,
    simpa using h
  end }

lemma is_closed.is_compact [compact_space α] {s : set α} (h : is_closed s) :
  is_compact s :=
compact_of_is_closed_subset compact_univ h (subset_univ _)

/-- `α` is a noncompact topological space if it not a compact space. -/
class noncompact_space (α : Type*) [topological_space α] : Prop :=
(noncompact_univ [] : ¬is_compact (univ : set α))

export noncompact_space (noncompact_univ)

lemma is_compact.ne_univ [noncompact_space α] {s : set α} (hs : is_compact s) : s ≠ univ :=
λ h, noncompact_univ α (h ▸ hs)

instance [noncompact_space α] : ne_bot (filter.cocompact α) :=
begin
  refine filter.has_basis_cocompact.ne_bot_iff.2 (λ s hs, _),
  contrapose hs, rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hs,
  rw hs, exact noncompact_univ α
end

instance [noncompact_space α] : ne_bot (filter.coclosed_compact α) :=
ne_bot_of_le filter.cocompact_le_coclosed_compact

lemma noncompact_space_of_ne_bot (h : ne_bot (filter.cocompact α)) : noncompact_space α :=
⟨λ h', (filter.nonempty_of_mem h'.compl_mem_cocompact).ne_empty compl_univ⟩

lemma filter.cocompact_ne_bot_iff : ne_bot (filter.cocompact α) ↔ noncompact_space α :=
⟨noncompact_space_of_ne_bot, @filter.cocompact.filter.ne_bot _ _⟩

lemma not_compact_space_iff : ¬compact_space α ↔ noncompact_space α :=
⟨λ h₁, ⟨λ h₂, h₁ ⟨h₂⟩⟩, λ ⟨h₁⟩ ⟨h₂⟩, h₁ h₂⟩

instance : noncompact_space ℤ :=
noncompact_space_of_ne_bot $ by simp only [filter.cocompact_eq_cofinite, filter.cofinite_ne_bot]

/-- A compact discrete space is finite. -/
noncomputable
def fintype_of_compact_of_discrete [compact_space α] [discrete_topology α] :
  fintype α :=
fintype_of_univ_finite $ compact_univ.finite_of_discrete

lemma finite_cover_nhds_interior [compact_space α] {U : α → set α} (hU : ∀ x, U x ∈ 𝓝 x) :
  ∃ t : finset α, (⋃ x ∈ t, interior (U x)) = univ :=
let ⟨t, ht⟩ := compact_univ.elim_finite_subcover (λ x, interior (U x)) (λ x, is_open_interior)
  (λ x _, mem_Union.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩)
in ⟨t, univ_subset_iff.1 ht⟩

lemma finite_cover_nhds [compact_space α] {U : α → set α} (hU : ∀ x, U x ∈ 𝓝 x) :
  ∃ t : finset α, (⋃ x ∈ t, U x) = univ :=
let ⟨t, ht⟩ := finite_cover_nhds_interior hU in ⟨t, univ_subset_iff.1 $ ht.symm.subset.trans $
  Union₂_mono $ λ x hx, interior_subset⟩

/-- If `α` is a compact space, then a locally finite family of sets of `α` can have only finitely
many nonempty elements. -/
lemma locally_finite.finite_nonempty_of_compact {ι : Type*} [compact_space α] {f : ι → set α}
  (hf : locally_finite f) :
  finite {i | (f i).nonempty} :=
by simpa only [inter_univ]  using hf.finite_nonempty_inter_compact compact_univ

/-- If `α` is a compact space, then a locally finite family of nonempty sets of `α` can have only
finitely many elements, `set.finite` version. -/
lemma locally_finite.finite_of_compact {ι : Type*} [compact_space α] {f : ι → set α}
  (hf : locally_finite f) (hne : ∀ i, (f i).nonempty) :
  finite (univ : set ι) :=
by simpa only [hne] using hf.finite_nonempty_of_compact

/-- If `α` is a compact space, then a locally finite family of nonempty sets of `α` can have only
finitely many elements, `fintype` version. -/
noncomputable def locally_finite.fintype_of_compact {ι : Type*} [compact_space α] {f : ι → set α}
  (hf : locally_finite f) (hne : ∀ i, (f i).nonempty) :
  fintype ι :=
fintype_of_univ_finite (hf.finite_of_compact hne)

/-- The comap of the cocompact filter on `β` by a continuous function `f : α → β` is less than or
equal to the cocompact filter on `α`.
This is a reformulation of the fact that images of compact sets are compact. -/
lemma filter.comap_cocompact {f : α → β} (hf : continuous f) :
  (filter.cocompact β).comap f ≤ filter.cocompact α :=
begin
  rw (filter.has_basis_cocompact.comap f).le_basis_iff filter.has_basis_cocompact,
  intros t ht,
  refine ⟨f '' t, ht.image hf, _⟩,
  simpa using t.subset_preimage_image f
end

lemma is_compact_range [compact_space α] {f : α → β} (hf : continuous f) :
  is_compact (range f) :=
by rw ← image_univ; exact compact_univ.image hf

/-- If X is is_compact then pr₂ : X × Y → Y is a closed map -/
theorem is_closed_proj_of_is_compact
  {X : Type*} [topological_space X] [compact_space X]
  {Y : Type*} [topological_space Y]  :
  is_closed_map (prod.snd : X × Y → Y) :=
begin
  set πX := (prod.fst : X × Y → X),
  set πY := (prod.snd : X × Y → Y),
  assume C (hC : is_closed C),
  rw is_closed_iff_cluster_pt at hC ⊢,
  assume y (y_closure : cluster_pt y $ 𝓟 (πY '' C)),
  have : ne_bot (map πX (comap πY (𝓝 y) ⊓ 𝓟 C)),
  { suffices : ne_bot (map πY (comap πY (𝓝 y) ⊓ 𝓟 C)),
      by simpa only [map_ne_bot_iff],
    convert y_closure,
    calc map πY (comap πY (𝓝 y) ⊓ 𝓟 C) =
       𝓝 y ⊓ map πY (𝓟 C) : filter.push_pull' _ _ _
      ... = 𝓝 y ⊓ 𝓟 (πY '' C) : by rw map_principal },
  resetI,
  obtain ⟨x, hx⟩ : ∃ x, cluster_pt x (map πX (comap πY (𝓝 y) ⊓ 𝓟 C)),
    from cluster_point_of_compact _,
  refine ⟨⟨x, y⟩, _, by simp [πY]⟩,
  apply hC,
  rw [cluster_pt, ← filter.map_ne_bot_iff πX],
  convert hx,
  calc map πX (𝓝 (x, y) ⊓ 𝓟 C)
      = map πX (comap πX (𝓝 x) ⊓ comap πY (𝓝 y) ⊓ 𝓟 C) : by rw [nhds_prod_eq, filter.prod]
  ... = map πX (comap πY (𝓝 y) ⊓ 𝓟 C ⊓ comap πX (𝓝 x)) : by ac_refl
  ... = map πX (comap πY (𝓝 y) ⊓ 𝓟 C) ⊓ 𝓝 x            : by rw filter.push_pull
  ... = 𝓝 x ⊓ map πX (comap πY (𝓝 y) ⊓ 𝓟 C)            : by rw inf_comm
end

lemma exists_subset_nhd_of_compact_space [compact_space α] {ι : Type*} [nonempty ι]
  {V : ι → set α} (hV : directed (⊇) V) (hV_closed : ∀ i, is_closed (V i))
  {U : set α} (hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x) : ∃ i, V i ⊆ U :=
exists_subset_nhd_of_compact' hV (λ i, (hV_closed i).is_compact) hV_closed hU

/-- If `f : α → β` is an `inducing` map, then the image `f '' s` of a set `s` is compact if and only
if the set `s` is closed. -/
lemma inducing.is_compact_iff {f : α → β} (hf : inducing f) {s : set α} :
  is_compact (f '' s) ↔ is_compact s :=
begin
  refine ⟨_, λ hs, hs.image hf.continuous⟩,
  introsI hs F F_ne_bot F_le,
  obtain ⟨_, ⟨x, x_in : x ∈ s, rfl⟩, hx : cluster_pt (f x) (map f F)⟩ :=
    hs (calc map f F ≤ map f (𝓟 s) : map_mono F_le
                ... = 𝓟 (f '' s) : map_principal),
  use [x, x_in],
  suffices : (map f (𝓝 x ⊓ F)).ne_bot, by simpa [filter.map_ne_bot_iff],
  rwa calc map f (𝓝 x ⊓ F) = map f ((comap f $ 𝓝 $ f x) ⊓ F) : by rw hf.nhds_eq_comap
                        ... = 𝓝 (f x) ⊓ map f F : filter.push_pull' _ _ _
end

/-- If `f : α → β` is an `embedding` (or more generally, an `inducing` map, see
`inducing.is_compact_iff`), then the image `f '' s` of a set `s` is compact if and only if the set
`s` is closed. -/
lemma embedding.is_compact_iff_is_compact_image {f : α → β} (hf : embedding f) :
  is_compact s ↔ is_compact (f '' s) :=
hf.to_inducing.is_compact_iff.symm

/-- The preimage of a compact set under a closed embedding is a compact set. -/
lemma closed_embedding.is_compact_preimage {f : α → β} (hf : closed_embedding f) {K : set β}
  (hK : is_compact K) : is_compact (f ⁻¹' K) :=
begin
  replace hK := hK.inter_right hf.closed_range,
  rwa [← hf.to_inducing.is_compact_iff, image_preimage_eq_inter_range]
end

/-- A closed embedding is proper, ie, inverse images of compact sets are contained in compacts.
Moreover, the preimage of a compact set is compact, see `closed_embedding.is_compact_preimage`. -/
lemma closed_embedding.tendsto_cocompact
  {f : α → β} (hf : closed_embedding f) : tendsto f (filter.cocompact α) (filter.cocompact β) :=
filter.has_basis_cocompact.tendsto_right_iff.mpr $ λ K hK,
  (hf.is_compact_preimage hK).compl_mem_cocompact

lemma compact_iff_compact_in_subtype {p : α → Prop} {s : set {a // p a}} :
  is_compact s ↔ is_compact ((coe : _ → α) '' s) :=
embedding_subtype_coe.is_compact_iff_is_compact_image

lemma is_compact_iff_is_compact_univ {s : set α} : is_compact s ↔ is_compact (univ : set s) :=
by rw [compact_iff_compact_in_subtype, image_univ, subtype.range_coe]; refl

lemma is_compact_iff_compact_space {s : set α} : is_compact s ↔ compact_space s :=
is_compact_iff_is_compact_univ.trans ⟨λ h, ⟨h⟩, @compact_space.compact_univ _ _⟩

protected lemma closed_embedding.noncompact_space [noncompact_space α] {f : α → β}
  (hf : closed_embedding f) : noncompact_space β :=
noncompact_space_of_ne_bot hf.tendsto_cocompact.ne_bot

protected lemma closed_embedding.compact_space [h : compact_space β] {f : α → β}
  (hf : closed_embedding f) : compact_space α :=
by { unfreezingI { contrapose! h, rw not_compact_space_iff at h ⊢ }, exact hf.noncompact_space }

lemma is_compact.prod {s : set α} {t : set β} (hs : is_compact s) (ht : is_compact t) :
  is_compact (s ×ˢ t) :=
begin
  rw is_compact_iff_ultrafilter_le_nhds at hs ht ⊢,
  intros f hfs,
  rw le_principal_iff at hfs,
  obtain ⟨a : α, sa : a ∈ s, ha : map prod.fst ↑f ≤ 𝓝 a⟩ :=
    hs (f.map prod.fst) (le_principal_iff.2 $ mem_map.2 $ mem_of_superset hfs (λ x, and.left)),
  obtain ⟨b : β, tb : b ∈ t, hb : map prod.snd ↑f ≤ 𝓝 b⟩ :=
    ht (f.map prod.snd) (le_principal_iff.2 $ mem_map.2 $
      mem_of_superset hfs (λ x, and.right)),
  rw map_le_iff_le_comap at ha hb,
  refine ⟨⟨a, b⟩, ⟨sa, tb⟩, _⟩,
  rw nhds_prod_eq, exact le_inf ha hb
end

/-- Finite topological spaces are compact. -/
@[priority 100] instance fintype.compact_space [fintype α] : compact_space α :=
{ compact_univ := finite_univ.is_compact }

/-- The product of two compact spaces is compact. -/
instance [compact_space α] [compact_space β] : compact_space (α × β) :=
⟨by { rw ← univ_prod_univ, exact compact_univ.prod compact_univ }⟩

/-- The disjoint union of two compact spaces is compact. -/
instance [compact_space α] [compact_space β] : compact_space (α ⊕ β) :=
⟨begin
  rw ← range_inl_union_range_inr,
  exact (is_compact_range continuous_inl).union (is_compact_range continuous_inr)
end⟩

instance [fintype ι] [Π i, topological_space (π i)] [∀ i, compact_space (π i)] :
  compact_space (Σ i, π i) :=
begin
  refine ⟨_⟩,
  rw sigma.univ,
  exact compact_Union (λ i, is_compact_range continuous_sigma_mk),
end

/-- The coproduct of the cocompact filters on two topological spaces is the cocompact filter on
their product. -/
lemma filter.coprod_cocompact :
  (filter.cocompact α).coprod (filter.cocompact β) = filter.cocompact (α × β) :=
begin
  ext S,
  simp only [mem_coprod_iff, exists_prop, mem_comap, filter.mem_cocompact],
  split,
  { rintro ⟨⟨A, ⟨t, ht, hAt⟩, hAS⟩, B, ⟨t', ht', hBt'⟩, hBS⟩,
    refine ⟨t ×ˢ t', ht.prod ht', _⟩,
    refine subset.trans _ (union_subset hAS hBS),
    rw compl_subset_comm at ⊢ hAt hBt',
    refine subset.trans _ (set.prod_mono hAt hBt'),
    intros x,
    simp only [compl_union, mem_inter_eq, mem_prod, mem_preimage, mem_compl_eq],
    tauto },
  { rintros ⟨t, ht, htS⟩,
    refine ⟨⟨(prod.fst '' t)ᶜ, _, _⟩, ⟨(prod.snd '' t)ᶜ, _, _⟩⟩,
    { exact ⟨prod.fst '' t, ht.image continuous_fst, subset.rfl⟩ },
    { rw preimage_compl,
      rw compl_subset_comm at ⊢ htS,
      exact subset.trans htS (subset_preimage_image prod.fst _) },
    { exact ⟨prod.snd '' t, ht.image continuous_snd, subset.rfl⟩ },
    { rw preimage_compl,
      rw compl_subset_comm at ⊢ htS,
      exact subset.trans htS (subset_preimage_image prod.snd _) } }
end

lemma prod.noncompact_space_iff :
  noncompact_space (α × β) ↔ noncompact_space α ∧ nonempty β ∨ nonempty α ∧ noncompact_space β :=
by simp [← filter.cocompact_ne_bot_iff, ← filter.coprod_cocompact, filter.coprod_ne_bot_iff]

@[priority 100] -- See Note [lower instance priority]
instance prod.noncompact_space_left [noncompact_space α] [nonempty β] : noncompact_space (α × β) :=
prod.noncompact_space_iff.2 (or.inl ⟨‹_›, ‹_›⟩)

@[priority 100] -- See Note [lower instance priority]
instance prod.noncompact_space_right [nonempty α] [noncompact_space β] : noncompact_space (α × β) :=
prod.noncompact_space_iff.2 (or.inr ⟨‹_›, ‹_›⟩)

section tychonoff
variables [Π i, topological_space (π i)]

/-- **Tychonoff's theorem** -/
lemma is_compact_pi_infinite {s : Π i, set (π i)} :
  (∀ i, is_compact (s i)) → is_compact {x : Π i, π i | ∀ i, x i ∈ s i} :=
begin
  simp only [is_compact_iff_ultrafilter_le_nhds, nhds_pi, filter.pi, exists_prop, mem_set_of_eq,
    le_infi_iff, le_principal_iff],
  intros h f hfs,
  have : ∀ i:ι, ∃ a, a ∈ s i ∧ tendsto (λx:Πi:ι, π i, x i) f (𝓝 a),
  { refine λ i, h i (f.map _) (mem_map.2 _),
    exact mem_of_superset hfs (λ x hx, hx i) },
  choose a ha,
  exact ⟨a, assume i, (ha i).left, assume i, (ha i).right.le_comap⟩
end

/-- A version of Tychonoff's theorem that uses `set.pi`. -/
lemma is_compact_univ_pi {s : Π i, set (π i)} (h : ∀ i, is_compact (s i)) :
  is_compact (pi univ s) :=
by { convert is_compact_pi_infinite h, simp only [← mem_univ_pi, set_of_mem_eq] }

instance pi.compact_space [∀ i, compact_space (π i)] : compact_space (Πi, π i) :=
⟨by { rw [← pi_univ univ], exact is_compact_univ_pi (λ i, compact_univ) }⟩

/-- Product of compact sets is compact -/
lemma filter.Coprod_cocompact {δ : Type*} {κ : δ → Type*} [Π d, topological_space (κ d)] :
  filter.Coprod (λ d, filter.cocompact (κ d)) = filter.cocompact (Π d, κ d) :=
begin
  ext S, rcases compl_surjective S with ⟨S, rfl⟩,
  simp_rw [compl_mem_Coprod_iff, filter.mem_cocompact, compl_subset_compl],
  split,
  { rintro ⟨t, H, hSt⟩, choose K hKc htK using H,
    exact ⟨set.pi univ K, is_compact_univ_pi hKc, hSt.trans $ pi_mono $ λ i _, htK i⟩ },
  { rintro ⟨K, hKc, hSK⟩,
    exact ⟨λ i, function.eval i '' K, λ i, ⟨_, hKc.image (continuous_apply i), subset.rfl⟩,
      hSK.trans $ subset_pi_eval_image _ _⟩ }
end

end tychonoff

instance quot.compact_space {r : α → α → Prop} [compact_space α] :
  compact_space (quot r) :=
⟨by { rw ← range_quot_mk, exact is_compact_range continuous_quot_mk }⟩

instance quotient.compact_space {s : setoid α} [compact_space α] :
  compact_space (quotient s) :=
quot.compact_space

/-- There are various definitions of "locally compact space" in the literature, which agree for
Hausdorff spaces but not in general. This one is the precise condition on X needed for the
evaluation `map C(X, Y) × X → Y` to be continuous for all `Y` when `C(X, Y)` is given the
compact-open topology. -/
class locally_compact_space (α : Type*) [topological_space α] : Prop :=
(local_compact_nhds : ∀ (x : α) (n ∈ 𝓝 x), ∃ s ∈ 𝓝 x, s ⊆ n ∧ is_compact s)

lemma compact_basis_nhds [locally_compact_space α] (x : α) :
  (𝓝 x).has_basis (λ s, s ∈ 𝓝 x ∧ is_compact s) (λ s, s) :=
has_basis_self.2 $ by simpa only [and_comm] using locally_compact_space.local_compact_nhds x

lemma local_compact_nhds [locally_compact_space α] {x : α} {n : set α} (h : n ∈ 𝓝 x) :
  ∃ s ∈ 𝓝 x, s ⊆ n ∧ is_compact s :=
locally_compact_space.local_compact_nhds _ _ h

lemma locally_compact_space_of_has_basis {ι : α → Type*} {p : Π x, ι x → Prop}
  {s : Π x, ι x → set α} (h : ∀ x, (𝓝 x).has_basis (p x) (s x))
  (hc : ∀ x i, p x i → is_compact (s x i)) :
  locally_compact_space α :=
⟨λ x t ht, let ⟨i, hp, ht⟩ := (h x).mem_iff.1 ht in ⟨s x i, (h x).mem_of_mem hp, ht, hc x i hp⟩⟩

instance locally_compact_space.prod (α : Type*) (β : Type*) [topological_space α]
  [topological_space β] [locally_compact_space α] [locally_compact_space β] :
  locally_compact_space (α × β) :=
have _ := λ x : α × β, (compact_basis_nhds x.1).prod_nhds' (compact_basis_nhds x.2),
locally_compact_space_of_has_basis this $ λ x s ⟨⟨_, h₁⟩, _, h₂⟩, h₁.prod h₂

/-- A reformulation of the definition of locally compact space: In a locally compact space,
  every open set containing `x` has a compact subset containing `x` in its interior. -/
lemma exists_compact_subset [locally_compact_space α] {x : α} {U : set α}
  (hU : is_open U) (hx : x ∈ U) : ∃ (K : set α), is_compact K ∧ x ∈ interior K ∧ K ⊆ U :=
begin
  rcases locally_compact_space.local_compact_nhds x U (hU.mem_nhds hx) with ⟨K, h1K, h2K, h3K⟩,
  exact ⟨K, h3K, mem_interior_iff_mem_nhds.2 h1K, h2K⟩,
end

/-- In a locally compact space every point has a compact neighborhood. -/
lemma exists_compact_mem_nhds [locally_compact_space α] (x : α) :
  ∃ K, is_compact K ∧ K ∈ 𝓝 x :=
let ⟨K, hKc, hx, H⟩ := exists_compact_subset is_open_univ (mem_univ x)
in ⟨K, hKc, mem_interior_iff_mem_nhds.1 hx⟩

/-- In a locally compact space, every compact set is contained in the interior of a compact set. -/
lemma exists_compact_superset [locally_compact_space α] {K : set α} (hK : is_compact K) :
  ∃ K', is_compact K' ∧ K ⊆ interior K' :=
begin
  choose U hUc hxU using λ x : K, exists_compact_mem_nhds (x : α),
  have : K ⊆ ⋃ x, interior (U x),
    from λ x hx, mem_Union.2 ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.2 (hxU _)⟩,
  rcases hK.elim_finite_subcover _ _ this with ⟨t, ht⟩,
  { refine ⟨_, t.compact_bUnion (λ x _, hUc x), λ x hx, _⟩,
    rcases mem_Union₂.1 (ht hx) with ⟨y, hyt, hy⟩,
    exact interior_mono (subset_bUnion_of_mem hyt) hy },
  { exact λ _, is_open_interior }
end

protected lemma closed_embedding.locally_compact_space [locally_compact_space β] {f : α → β}
  (hf : closed_embedding f) : locally_compact_space α :=
begin
  have : ∀ x : α, (𝓝 x).has_basis (λ s, s ∈ 𝓝 (f x) ∧ is_compact s) (λ s, f ⁻¹' s),
  { intro x,
    rw hf.to_embedding.to_inducing.nhds_eq_comap,
    exact (compact_basis_nhds _).comap _ },
  exact locally_compact_space_of_has_basis this (λ x s hs, hf.is_compact_preimage hs.2)
end

protected lemma is_closed.locally_compact_space [locally_compact_space α] {s : set α}
  (hs : is_closed s) : locally_compact_space s :=
(closed_embedding_subtype_coe hs).locally_compact_space

protected lemma open_embedding.locally_compact_space [locally_compact_space β] {f : α → β}
  (hf : open_embedding f) : locally_compact_space α :=
begin
  have : ∀ x : α, (𝓝 x).has_basis (λ s, (s ∈ 𝓝 (f x) ∧ is_compact s) ∧ s ⊆ range f) (λ s, f ⁻¹' s),
  { intro x,
    rw hf.to_embedding.to_inducing.nhds_eq_comap,
    exact ((compact_basis_nhds _).restrict_subset $
      hf.open_range.mem_nhds $ mem_range_self _).comap _ },
  refine locally_compact_space_of_has_basis this (λ x s hs, _),
  rw [← hf.to_inducing.is_compact_iff, image_preimage_eq_of_subset hs.2],
  exact hs.1.2
end

protected lemma is_open.locally_compact_space [locally_compact_space α] {s : set α}
  (hs : is_open s) : locally_compact_space s :=
hs.open_embedding_subtype_coe.locally_compact_space

lemma ultrafilter.le_nhds_Lim [compact_space α] (F : ultrafilter α) :
  ↑F ≤ 𝓝 (@Lim _ _ (F : filter α).nonempty_of_ne_bot F) :=
begin
  rcases compact_univ.ultrafilter_le_nhds F (by simp) with ⟨x, -, h⟩,
  exact le_nhds_Lim ⟨x,h⟩,
end

theorem is_closed.exists_minimal_nonempty_closed_subset [compact_space α]
  {S : set α} (hS : is_closed S) (hne : S.nonempty) :
  ∃ (V : set α),
    V ⊆ S ∧ V.nonempty ∧ is_closed V ∧
      (∀ (V' : set α), V' ⊆ V → V'.nonempty → is_closed V' → V' = V) :=
begin
  let opens := {U : set α | Sᶜ ⊆ U ∧ is_open U ∧ Uᶜ.nonempty},
  obtain ⟨U, ⟨Uc, Uo, Ucne⟩, h⟩ := zorn.zorn_subset opens (λ c hc hz, begin
    by_cases hcne : c.nonempty,
    { obtain ⟨U₀, hU₀⟩ := hcne,
      haveI : nonempty {U // U ∈ c} := ⟨⟨U₀, hU₀⟩⟩,
      obtain ⟨U₀compl, U₀opn, U₀ne⟩ := hc hU₀,
      use ⋃₀ c,
      refine ⟨⟨_, _, _⟩, λ U hU a ha, ⟨U, hU, ha⟩⟩,
      { exact λ a ha, ⟨U₀, hU₀, U₀compl ha⟩ },
      { exact is_open_sUnion (λ _ h, (hc h).2.1) },
      { convert_to (⋂(U : {U // U ∈ c}), U.1ᶜ).nonempty,
        { ext,
          simp only [not_exists, exists_prop, not_and, set.mem_Inter, subtype.forall,
            set.mem_set_of_eq, set.mem_compl_eq, subtype.val_eq_coe],
          refl, },
        apply is_compact.nonempty_Inter_of_directed_nonempty_compact_closed,
        { rintros ⟨U, hU⟩ ⟨U', hU'⟩,
          obtain ⟨V, hVc, hVU, hVU'⟩ := zorn.chain.directed_on hz U hU U' hU',
          exact ⟨⟨V, hVc⟩, set.compl_subset_compl.mpr hVU, set.compl_subset_compl.mpr hVU'⟩, },
        { exact λ U, (hc U.2).2.2, },
        { exact λ U, (is_closed_compl_iff.mpr (hc U.2).2.1).is_compact, },
        { exact λ U, (is_closed_compl_iff.mpr (hc U.2).2.1), } } },
    { use Sᶜ,
      refine ⟨⟨set.subset.refl _, is_open_compl_iff.mpr hS, _⟩, λ U Uc, (hcne ⟨U, Uc⟩).elim⟩,
      rw compl_compl,
      exact hne, }
  end),
  refine ⟨Uᶜ, set.compl_subset_comm.mp Uc, Ucne, is_closed_compl_iff.mpr Uo, _⟩,
  intros V' V'sub V'ne V'cls,
  have : V'ᶜ = U,
  { refine h V'ᶜ ⟨_, is_open_compl_iff.mpr V'cls, _⟩ (set.subset_compl_comm.mp V'sub),
    exact set.subset.trans Uc (set.subset_compl_comm.mp V'sub),
    simp only [compl_compl, V'ne], },
  rw [←this, compl_compl],
end

/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `topological_space.compact_covering`. -/
class sigma_compact_space (α : Type*) [topological_space α] : Prop :=
(exists_compact_covering : ∃ K : ℕ → set α, (∀ n, is_compact (K n)) ∧ (⋃ n, K n) = univ)

@[priority 200] -- see Note [lower instance priority]
instance compact_space.sigma_compact [compact_space α] : sigma_compact_space α :=
⟨⟨λ _, univ, λ _, compact_univ, Union_const _⟩⟩

lemma sigma_compact_space.of_countable (S : set (set α)) (Hc : countable S)
  (Hcomp : ∀ s ∈ S, is_compact s) (HU : ⋃₀ S = univ) : sigma_compact_space α :=
⟨(exists_seq_cover_iff_countable ⟨_, is_compact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩

@[priority 100] -- see Note [lower instance priority]
instance sigma_compact_space_of_locally_compact_second_countable [locally_compact_space α]
  [second_countable_topology α] : sigma_compact_space α :=
begin
  choose K hKc hxK using λ x : α, exists_compact_mem_nhds x,
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩,
  refine sigma_compact_space.of_countable _ (hsc.image K) (ball_image_iff.2 $ λ x _, hKc x) _,
  rwa sUnion_image
end

variables (α) [sigma_compact_space α]
open sigma_compact_space

/-- A choice of compact covering for a `σ`-compact space, chosen to be monotone. -/
def compact_covering : ℕ → set α :=
accumulate exists_compact_covering.some

lemma is_compact_compact_covering (n : ℕ) : is_compact (compact_covering α n) :=
compact_accumulate (classical.some_spec sigma_compact_space.exists_compact_covering).1 n

lemma Union_compact_covering : (⋃ n, compact_covering α n) = univ :=
begin
  rw [compact_covering, Union_accumulate],
  exact (classical.some_spec sigma_compact_space.exists_compact_covering).2
end

@[mono] lemma compact_covering_subset ⦃m n : ℕ⦄ (h : m ≤ n) :
  compact_covering α m ⊆ compact_covering α n :=
monotone_accumulate h

variable {α}

lemma exists_mem_compact_covering (x : α) : ∃ n, x ∈ compact_covering α n :=
Union_eq_univ_iff.mp (Union_compact_covering α) x

/-- If `α` is a `σ`-compact space, then a locally finite family of nonempty sets of `α` can have
only countably many elements, `set.countable` version. -/
protected lemma locally_finite.countable_univ {ι : Type*} {f : ι → set α} (hf : locally_finite f)
  (hne : ∀ i, (f i).nonempty) :
  countable (univ : set ι) :=
begin
  have := λ n, hf.finite_nonempty_inter_compact (is_compact_compact_covering α n),
  refine (countable_Union (λ n, (this n).countable)).mono (λ i hi, _),
  rcases hne i with ⟨x, hx⟩,
  rcases Union_eq_univ_iff.1 (Union_compact_covering α) x with ⟨n, hn⟩,
  exact mem_Union.2 ⟨n, x, hx, hn⟩
end

/-- If `f : ι → set α` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
protected noncomputable def locally_finite.encodable {ι : Type*} {f : ι → set α}
  (hf : locally_finite f) (hne : ∀ i, (f i).nonempty) : encodable ι :=
@encodable.of_equiv _ _ (hf.countable_univ hne).to_encodable (equiv.set.univ _).symm

/-- In a topological space with sigma compact topology, if `f` is a function that sends each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some countable set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`. -/
lemma countable_cover_nhds_within_of_sigma_compact {f : α → set α} {s : set α} (hs : is_closed s)
  (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ t ⊆ s, countable t ∧ s ⊆ ⋃ x ∈ t, f x :=
begin
  simp only [nhds_within, mem_inf_principal] at hf,
  choose t ht hsub using λ n, ((is_compact_compact_covering α n).inter_right hs).elim_nhds_subcover
    _ (λ x hx, hf x hx.right),
  refine ⟨⋃ n, (t n : set α), Union_subset $ λ n x hx, (ht n x hx).2,
    countable_Union $ λ n, (t n).countable_to_set, λ x hx, mem_Union₂.2 _⟩,
  rcases exists_mem_compact_covering x with ⟨n, hn⟩,
  rcases mem_Union₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y ∈ t n, hyf : x ∈ s → x ∈ f y⟩,
  exact ⟨y, mem_Union.2 ⟨n, hyt⟩, hyf hx⟩
end

/-- In a topological space with sigma compact topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
lemma countable_cover_nhds_of_sigma_compact {f : α → set α}
  (hf : ∀ x, f x ∈ 𝓝 x) : ∃ s : set α, countable s ∧ (⋃ x ∈ s, f x) = univ :=
begin
  simp only [← nhds_within_univ] at hf,
  rcases countable_cover_nhds_within_of_sigma_compact is_closed_univ (λ x _, hf x)
    with ⟨s, -, hsc, hsU⟩,
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩
end

end compact

/-- An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior (K (n + 1))` and
`(⋃ n, K n) = univ`.

If `X` is a locally compact sigma compact space, then `compact_exhaustion.choice X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : compact_exhaustion X)`. -/
structure compact_exhaustion (X : Type*) [topological_space X] :=
(to_fun : ℕ → set X)
(is_compact' : ∀ n, is_compact (to_fun n))
(subset_interior_succ' : ∀ n, to_fun n ⊆ interior (to_fun (n + 1)))
(Union_eq' : (⋃ n, to_fun n) = univ)

namespace compact_exhaustion

instance : has_coe_to_fun (compact_exhaustion α) (λ _, ℕ → set α) := ⟨to_fun⟩

variables {α} (K : compact_exhaustion α)

protected lemma is_compact (n : ℕ) : is_compact (K n) := K.is_compact' n

lemma subset_interior_succ (n : ℕ) : K n ⊆ interior (K (n + 1)) :=
K.subset_interior_succ' n

lemma subset_succ (n : ℕ) : K n ⊆ K (n + 1) :=
subset.trans (K.subset_interior_succ n) interior_subset

@[mono] protected lemma subset ⦃m n : ℕ⦄ (h : m ≤ n) : K m ⊆ K n :=
show K m ≤ K n, from monotone_nat_of_le_succ K.subset_succ h

lemma subset_interior ⦃m n : ℕ⦄ (h : m < n) : K m ⊆ interior (K n) :=
subset.trans (K.subset_interior_succ m) $ interior_mono $ K.subset h

lemma Union_eq : (⋃ n, K n) = univ := K.Union_eq'

lemma exists_mem (x : α) : ∃ n, x ∈ K n := Union_eq_univ_iff.1 K.Union_eq x

/-- The minimal `n` such that `x ∈ K n`. -/
protected noncomputable def find (x : α) : ℕ := nat.find (K.exists_mem x)

lemma mem_find (x : α) : x ∈ K (K.find x) := nat.find_spec (K.exists_mem x)

lemma mem_iff_find_le {x : α} {n : ℕ} : x ∈ K n ↔ K.find x ≤ n :=
⟨λ h, nat.find_min' (K.exists_mem x) h, λ h, K.subset h $ K.mem_find x⟩

/-- Prepend the empty set to a compact exhaustion `K n`. -/
def shiftr : compact_exhaustion α :=
{ to_fun := λ n, nat.cases_on n ∅ K,
  is_compact' := λ n, nat.cases_on n is_compact_empty K.is_compact,
  subset_interior_succ' := λ n, nat.cases_on n (empty_subset _) K.subset_interior_succ,
  Union_eq' := Union_eq_univ_iff.2 $ λ x, ⟨K.find x + 1, K.mem_find x⟩ }

@[simp] lemma find_shiftr (x : α) : K.shiftr.find x = K.find x + 1 :=
nat.find_comp_succ _ _ (not_mem_empty _)

lemma mem_diff_shiftr_find (x : α) : x ∈ K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
⟨K.mem_find _, mt K.shiftr.mem_iff_find_le.1 $
  by simp only [find_shiftr, not_le, nat.lt_succ_self]⟩

/-- A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets)
of a locally compact sigma compact space. -/
noncomputable def choice (X : Type*) [topological_space X] [locally_compact_space X]
  [sigma_compact_space X] : compact_exhaustion X :=
begin
  apply classical.choice,
  let K : ℕ → {s : set X // is_compact s} :=
    λ n, nat.rec_on n ⟨∅, is_compact_empty⟩
      (λ n s, ⟨(exists_compact_superset s.2).some ∪ compact_covering X n,
        (exists_compact_superset s.2).some_spec.1.union (is_compact_compact_covering _ _)⟩),
  refine ⟨⟨λ n, K n, λ n, (K n).2, λ n, _, _⟩⟩,
  { exact subset.trans (exists_compact_superset (K n).2).some_spec.2
      (interior_mono $ subset_union_left _ _) },
  { refine univ_subset_iff.1 (Union_compact_covering X ▸ _),
    exact Union_mono' (λ n, ⟨n + 1, subset_union_right _ _⟩) }
end

noncomputable instance [locally_compact_space α] [sigma_compact_space α] :
  inhabited (compact_exhaustion α) :=
⟨compact_exhaustion.choice α⟩

end compact_exhaustion

section clopen

/-- A set is clopen if it is both open and closed. -/
def is_clopen (s : set α) : Prop :=
is_open s ∧ is_closed s

protected lemma is_clopen.is_open (hs : is_clopen s) : is_open s := hs.1
protected lemma is_clopen.is_closed (hs : is_clopen s) : is_closed s := hs.2

theorem is_clopen.union {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∪ t) :=
⟨hs.1.union ht.1, hs.2.union ht.2⟩

theorem is_clopen.inter {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s ∩ t) :=
⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

@[simp] theorem is_clopen_empty : is_clopen (∅ : set α) :=
⟨is_open_empty, is_closed_empty⟩

@[simp] theorem is_clopen_univ : is_clopen (univ : set α) :=
⟨is_open_univ, is_closed_univ⟩

theorem is_clopen.compl {s : set α} (hs : is_clopen s) : is_clopen sᶜ :=
⟨hs.2.is_open_compl, hs.1.is_closed_compl⟩

@[simp] theorem is_clopen_compl_iff {s : set α} : is_clopen sᶜ ↔ is_clopen s :=
⟨λ h, compl_compl s ▸ is_clopen.compl h, is_clopen.compl⟩

theorem is_clopen.diff {s t : set α} (hs : is_clopen s) (ht : is_clopen t) : is_clopen (s \ t) :=
hs.inter ht.compl

lemma is_clopen_Union {β : Type*} [fintype β] {s : β → set α}
  (h : ∀ i, is_clopen (s i)) : is_clopen (⋃ i, s i) :=
⟨is_open_Union (forall_and_distrib.1 h).1, is_closed_Union (forall_and_distrib.1 h).2⟩

lemma is_clopen_bUnion {β : Type*} {s : finset β} {f : β → set α} (h : ∀ i ∈ s, is_clopen $ f i) :
  is_clopen (⋃ i ∈ s, f i) :=
begin
  refine ⟨is_open_bUnion (λ i hi, (h i hi).1), _⟩,
  show is_closed (⋃ (i : β) (H : i ∈ (s : set β)), f i),
  rw bUnion_eq_Union,
  exact is_closed_Union (λ ⟨i, hi⟩,(h i hi).2)
end

lemma is_clopen_Inter {β : Type*} [fintype β] {s : β → set α}
  (h : ∀ i, is_clopen (s i)) : is_clopen (⋂ i, s i) :=
⟨(is_open_Inter (forall_and_distrib.1 h).1), (is_closed_Inter (forall_and_distrib.1 h).2)⟩

lemma is_clopen_bInter {β : Type*} {s : finset β} {f : β → set α} (h : ∀ i ∈ s, is_clopen (f i)) :
  is_clopen (⋂ i ∈ s, f i) :=
⟨ is_open_bInter ⟨finset_coe.fintype s⟩ (λ i hi, (h i hi).1),
  by {show is_closed (⋂ (i : β) (H : i ∈ (↑s : set β)), f i), rw bInter_eq_Inter,
    apply is_closed_Inter, rintro ⟨i, hi⟩, exact (h i hi).2}⟩

lemma continuous_on.preimage_clopen_of_clopen
  {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_clopen s)
  (ht : is_clopen t) : is_clopen (s ∩ f⁻¹' t) :=
⟨continuous_on.preimage_open_of_open hf hs.1 ht.1,
  continuous_on.preimage_closed_of_closed hf hs.2 ht.2⟩

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem is_clopen_inter_of_disjoint_cover_clopen {Z a b : set α} (h : is_clopen Z)
  (cover : Z ⊆ a ∪ b) (ha : is_open a) (hb : is_open b) (hab : a ∩ b = ∅) : is_clopen (Z ∩ a) :=
begin
  refine ⟨is_open.inter h.1 ha, _⟩,
  have : is_closed (Z ∩ bᶜ) := is_closed.inter h.2 (is_closed_compl_iff.2 hb),
  convert this using 1,
  apply subset.antisymm,
  { exact inter_subset_inter_right Z (subset_compl_iff_disjoint.2 hab) },
  { rintros x ⟨hx₁, hx₂⟩,
    exact ⟨hx₁, by simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩ }
end

@[simp] lemma is_clopen_discrete [discrete_topology α] (x : set α) : is_clopen x :=
⟨is_open_discrete _, is_closed_discrete _⟩

lemma clopen_range_sigma_mk {ι : Type*} {σ : ι → Type*} [Π i, topological_space (σ i)] {i : ι} :
  is_clopen (set.range (@sigma.mk ι σ i)) :=
⟨open_embedding_sigma_mk.open_range, closed_embedding_sigma_mk.closed_range⟩

protected lemma quotient_map.is_clopen_preimage {f : α → β}
  (hf : quotient_map f) {s : set β} : is_clopen (f ⁻¹' s) ↔ is_clopen s :=
and_congr hf.is_open_preimage hf.is_closed_preimage

end clopen

section preirreducible

/-- A preirreducible set `s` is one where there is no non-trivial pair of disjoint opens on `s`. -/
def is_preirreducible (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v →
  (s ∩ u).nonempty → (s ∩ v).nonempty → (s ∩ (u ∩ v)).nonempty

/-- An irreducible set `s` is one that is nonempty and
where there is no non-trivial pair of disjoint opens on `s`. -/
def is_irreducible (s : set α) : Prop :=
s.nonempty ∧ is_preirreducible s

lemma is_irreducible.nonempty {s : set α} (h : is_irreducible s) :
  s.nonempty := h.1

lemma is_irreducible.is_preirreducible {s : set α} (h : is_irreducible s) :
  is_preirreducible s := h.2

theorem is_preirreducible_empty : is_preirreducible (∅ : set α) :=
λ _ _ _ _ _ ⟨x, h1, h2⟩, h1.elim

theorem is_irreducible_singleton {x} : is_irreducible ({x} : set α) :=
⟨singleton_nonempty x,
 λ u v _ _ ⟨y, h1, h2⟩ ⟨z, h3, h4⟩, by rw mem_singleton_iff at h1 h3;
 substs y z; exact ⟨x, rfl, h2, h4⟩⟩

theorem is_preirreducible.closure {s : set α} (H : is_preirreducible s) :
  is_preirreducible (closure s) :=
λ u v hu hv ⟨y, hycs, hyu⟩ ⟨z, hzcs, hzv⟩,
let ⟨p, hpu, hps⟩ := mem_closure_iff.1 hycs u hu hyu in
let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 hzcs v hv hzv in
let ⟨r, hrs, hruv⟩ := H u v hu hv ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩ in
⟨r, subset_closure hrs, hruv⟩

lemma is_irreducible.closure {s : set α} (h : is_irreducible s) :
  is_irreducible (closure s) :=
⟨h.nonempty.closure, h.is_preirreducible.closure⟩

lemma is_preirreducible_of_subsingleton (s : set α) [hs : subsingleton s] : is_preirreducible s :=
begin
  cases s.eq_empty_or_nonempty,
  { exact h.symm ▸ is_preirreducible_empty },
  { obtain ⟨x, e⟩ := exists_eq_singleton_iff_nonempty_unique_mem.mpr
      ⟨h, λ _ ha _ hb, by injection @@subsingleton.elim hs ⟨_, ha⟩ ⟨_, hb⟩⟩,
    exact e.symm ▸ is_irreducible_singleton.2 }
end

theorem exists_preirreducible (s : set α) (H : is_preirreducible s) :
  ∃ t : set α, is_preirreducible t ∧ s ⊆ t ∧ ∀ u, is_preirreducible u → t ⊆ u → u = t :=
let ⟨m, hm, hsm, hmm⟩ := zorn.zorn_subset_nonempty {t : set α | is_preirreducible t}
  (λ c hc hcc hcn, let ⟨t, htc⟩ := hcn in
    ⟨⋃₀ c, λ u v hu hv ⟨y, hy, hyu⟩ ⟨z, hz, hzv⟩,
      let ⟨p, hpc, hyp⟩ := mem_sUnion.1 hy,
          ⟨q, hqc, hzq⟩ := mem_sUnion.1 hz in
      or.cases_on (zorn.chain.total hcc hpc hqc)
        (assume hpq : p ⊆ q, let ⟨x, hxp, hxuv⟩ := hc hqc u v hu hv
            ⟨y, hpq hyp, hyu⟩ ⟨z, hzq, hzv⟩ in
          ⟨x, mem_sUnion_of_mem hxp hqc, hxuv⟩)
        (assume hqp : q ⊆ p, let ⟨x, hxp, hxuv⟩ := hc hpc u v hu hv
            ⟨y, hyp, hyu⟩ ⟨z, hqp hzq, hzv⟩ in
          ⟨x, mem_sUnion_of_mem hxp hpc, hxuv⟩),
    λ x hxc, subset_sUnion_of_mem hxc⟩) s H in
⟨m, hm, hsm, λ u hu hmu, hmm _ hu hmu⟩

/-- A maximal irreducible set that contains a given point. -/
def irreducible_component (x : α) : set α :=
classical.some (exists_preirreducible {x} is_irreducible_singleton.is_preirreducible)

lemma irreducible_component_property (x : α) :
  is_preirreducible (irreducible_component x) ∧ {x} ⊆ (irreducible_component x) ∧
  ∀ u, is_preirreducible u → (irreducible_component x) ⊆ u → u = (irreducible_component x) :=
classical.some_spec (exists_preirreducible {x} is_irreducible_singleton.is_preirreducible)

theorem mem_irreducible_component {x : α} : x ∈ irreducible_component x :=
singleton_subset_iff.1 (irreducible_component_property x).2.1

theorem is_irreducible_irreducible_component {x : α} : is_irreducible (irreducible_component x) :=
⟨⟨x, mem_irreducible_component⟩, (irreducible_component_property x).1⟩

theorem eq_irreducible_component {x : α} :
  ∀ {s : set α}, is_preirreducible s → irreducible_component x ⊆ s → s = irreducible_component x :=
(irreducible_component_property x).2.2

theorem is_closed_irreducible_component {x : α} :
  is_closed (irreducible_component x) :=
closure_eq_iff_is_closed.1 $ eq_irreducible_component
  is_irreducible_irreducible_component.is_preirreducible.closure
  subset_closure

/-- A preirreducible space is one where there is no non-trivial pair of disjoint opens. -/
class preirreducible_space (α : Type u) [topological_space α] : Prop :=
(is_preirreducible_univ [] : is_preirreducible (univ : set α))

/-- An irreducible space is one that is nonempty
and where there is no non-trivial pair of disjoint opens. -/
class irreducible_space (α : Type u) [topological_space α] extends preirreducible_space α : Prop :=
(to_nonempty [] : nonempty α)

-- see Note [lower instance priority]
attribute [instance, priority 50] irreducible_space.to_nonempty

lemma irreducible_space.is_irreducible_univ (α : Type u) [topological_space α]
  [irreducible_space α] : is_irreducible (⊤ : set α) :=
⟨by simp, preirreducible_space.is_preirreducible_univ α⟩

lemma irreducible_space_def (α : Type u) [topological_space α] :
  irreducible_space α ↔ is_irreducible (⊤ : set α) :=
⟨@@irreducible_space.is_irreducible_univ α _,
  λ h, by { haveI : preirreducible_space α := ⟨h.2⟩, exact ⟨⟨h.1.some⟩⟩ }⟩

theorem nonempty_preirreducible_inter [preirreducible_space α] {s t : set α} :
  is_open s → is_open t → s.nonempty → t.nonempty → (s ∩ t).nonempty :=
by simpa only [univ_inter, univ_subset_iff] using
  @preirreducible_space.is_preirreducible_univ α _ _ s t

theorem is_preirreducible.image {s : set α} (H : is_preirreducible s)
  (f : α → β) (hf : continuous_on f s) : is_preirreducible (f '' s) :=
begin
  rintros u v hu hv ⟨_, ⟨⟨x, hx, rfl⟩, hxu⟩⟩ ⟨_, ⟨⟨y, hy, rfl⟩, hyv⟩⟩,
  rw ← mem_preimage at hxu hyv,
  rcases continuous_on_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩,
  rcases continuous_on_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩,
  have := H u' v' hu' hv',
  rw [inter_comm s u', ← u'_eq] at this,
  rw [inter_comm s v', ← v'_eq] at this,
  rcases this ⟨x, hxu, hx⟩ ⟨y, hyv, hy⟩ with ⟨z, hzs, hzu', hzv'⟩,
  refine ⟨f z, mem_image_of_mem f hzs, _, _⟩,
  all_goals
  { rw ← mem_preimage,
    apply mem_of_mem_inter_left,
    show z ∈ _ ∩ s,
    simp [*] }
end

theorem is_irreducible.image {s : set α} (H : is_irreducible s)
  (f : α → β) (hf : continuous_on f s) : is_irreducible (f '' s) :=
⟨nonempty_image_iff.mpr H.nonempty, H.is_preirreducible.image f hf⟩

lemma subtype.preirreducible_space {s : set α} (h : is_preirreducible s) :
  preirreducible_space s :=
{ is_preirreducible_univ :=
  begin
    intros u v hu hv hsu hsv,
    rw is_open_induced_iff at hu hv,
    rcases hu with ⟨u, hu, rfl⟩,
    rcases hv with ⟨v, hv, rfl⟩,
    rcases hsu with ⟨⟨x, hxs⟩, hxs', hxu⟩,
    rcases hsv with ⟨⟨y, hys⟩, hys', hyv⟩,
    rcases h u v hu hv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩ with ⟨z, hzs, ⟨hzu, hzv⟩⟩,
    exact ⟨⟨z, hzs⟩, ⟨set.mem_univ _, ⟨hzu, hzv⟩⟩⟩
  end }

lemma subtype.irreducible_space {s : set α} (h : is_irreducible s) :
  irreducible_space s :=
{ is_preirreducible_univ :=
  (subtype.preirreducible_space h.is_preirreducible).is_preirreducible_univ,
  to_nonempty := h.nonempty.to_subtype }

/-- A set `s` is irreducible if and only if
for every finite collection of open sets all of whose members intersect `s`,
`s` also intersects the intersection of the entire collection
(i.e., there is an element of `s` contained in every member of the collection). -/
lemma is_irreducible_iff_sInter {s : set α} :
  is_irreducible s ↔
  ∀ (U : finset (set α)) (hU : ∀ u ∈ U, is_open u) (H : ∀ u ∈ U, (s ∩ u).nonempty),
  (s ∩ ⋂₀ ↑U).nonempty :=
begin
  split; intro h,
  { intro U, apply finset.induction_on U,
    { intros, simpa using h.nonempty },
    { intros u U hu IH hU H,
      rw [finset.coe_insert, sInter_insert],
      apply h.2,
      { solve_by_elim [finset.mem_insert_self] },
      { apply is_open_sInter (finset.finite_to_set U),
        intros, solve_by_elim [finset.mem_insert_of_mem] },
      { solve_by_elim [finset.mem_insert_self] },
      { apply IH,
        all_goals { intros, solve_by_elim [finset.mem_insert_of_mem] } } } },
  { split,
    { simpa using h ∅ _ _; intro u; simp },
    intros u v hu hv hu' hv',
    simpa using h {u,v} _ _,
    all_goals
    { intro t,
      rw [finset.mem_insert, finset.mem_singleton],
      rintro (rfl|rfl); assumption } }
end

/-- A set is preirreducible if and only if
for every cover by two closed sets, it is contained in one of the two covering sets. -/
lemma is_preirreducible_iff_closed_union_closed {s : set α} :
  is_preirreducible s ↔
  ∀ (z₁ z₂ : set α), is_closed z₁ → is_closed z₂ → s ⊆ z₁ ∪ z₂ → s ⊆ z₁ ∨ s ⊆ z₂ :=
begin
  split,
  all_goals
  { intros h t₁ t₂ ht₁ ht₂,
    specialize h t₁ᶜ t₂ᶜ,
    simp only [is_open_compl_iff, is_closed_compl_iff] at h,
    specialize h ht₁ ht₂ },
  { contrapose!, simp only [not_subset],
    rintro ⟨⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩,
    rcases h ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩ with ⟨z, hz, hz'⟩,
    rw ← compl_union at hz',
    exact ⟨z, hz, hz'⟩ },
  { rintro ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩,
    rw ← compl_inter at h,
    delta set.nonempty,
    rw imp_iff_not_or at h,
    contrapose! h,
    split,
    { intros z hz hz', exact h z ⟨hz, hz'⟩ },
    { split; intro H; refine H _ ‹_›; assumption } }
end

/-- A set is irreducible if and only if
for every cover by a finite collection of closed sets,
it is contained in one of the members of the collection. -/
lemma is_irreducible_iff_sUnion_closed {s : set α} :
  is_irreducible s ↔
  ∀ (Z : finset (set α)) (hZ : ∀ z ∈ Z, is_closed z) (H : s ⊆ ⋃₀ ↑Z),
  ∃ z ∈ Z, s ⊆ z :=
begin
  rw [is_irreducible, is_preirreducible_iff_closed_union_closed],
  split; intro h,
  { intro Z, apply finset.induction_on Z,
    { intros, rw [finset.coe_empty, sUnion_empty] at H,
      rcases h.1 with ⟨x, hx⟩,
      exfalso, tauto },
    { intros z Z hz IH hZ H,
      cases h.2 z (⋃₀ ↑Z) _ _ _
        with h' h',
      { exact ⟨z, finset.mem_insert_self _ _, h'⟩ },
      { rcases IH _ h' with ⟨z', hz', hsz'⟩,
        { exact ⟨z', finset.mem_insert_of_mem hz', hsz'⟩ },
        { intros, solve_by_elim [finset.mem_insert_of_mem] } },
      { solve_by_elim [finset.mem_insert_self] },
      { rw sUnion_eq_bUnion,
        apply is_closed_bUnion (finset.finite_to_set Z),
        { intros, solve_by_elim [finset.mem_insert_of_mem] } },
      { simpa using H } } },
  { split,
    { by_contradiction hs,
      simpa using h ∅ _ _,
      { intro z, simp },
      { simpa [set.nonempty] using hs } },
    intros z₁ z₂ hz₁ hz₂ H,
    have := h {z₁, z₂} _ _,
    simp only [exists_prop, finset.mem_insert, finset.mem_singleton] at this,
    { rcases this with ⟨z, rfl|rfl, hz⟩; tauto },
    { intro t,
      rw [finset.mem_insert, finset.mem_singleton],
      rintro (rfl|rfl); assumption },
    { simpa using H } }
end

/-- A nonemtpy open subset of a preirreducible subspace is dense in the subspace. -/
lemma subset_closure_inter_of_is_preirreducible_of_is_open {S U : set α}
  (hS : is_preirreducible S) (hU : is_open U) (h : (S ∩ U).nonempty) : S ⊆ closure (S ∩ U) :=
begin
  by_contra h',
  obtain ⟨x, h₁, h₂, h₃⟩ := hS _ (closure (S ∩ U))ᶜ hU (is_open_compl_iff.mpr is_closed_closure) h
    (set.inter_compl_nonempty_iff.mpr h'),
  exact h₃ (subset_closure ⟨h₁, h₂⟩)
end

/-- If `∅ ≠ U ⊆ S ⊆ Z` such that `U` is open and `Z` is preirreducible, then `S` is irreducible. -/
lemma is_preirreducible.subset_irreducible {S U Z : set α}
  (hZ : is_preirreducible Z) (hU : U.nonempty) (hU' : is_open U)
  (h₁ : U ⊆ S) (h₂ : S ⊆ Z) : is_irreducible S :=
begin
  classical,
  obtain ⟨z, hz⟩ := hU,
  replace hZ : is_irreducible Z := ⟨⟨z, h₂ (h₁ hz)⟩, hZ⟩,
  refine ⟨⟨z, h₁ hz⟩, _⟩,
  rintros u v hu hv ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩,
  obtain ⟨a, -, ha'⟩ := is_irreducible_iff_sInter.mp hZ {U, u, v} (by tidy) _,
  replace ha' : a ∈ U ∧ a ∈ u ∧ a ∈ v := by simpa using ha',
  exact ⟨a, h₁ ha'.1, ha'.2⟩,
  { intros U H,
    simp only [finset.mem_insert, finset.mem_singleton] at H,
    rcases H with (rfl|rfl|rfl),
    exacts [⟨z, h₂ (h₁ hz), hz⟩, ⟨x, h₂ hx, hx'⟩, ⟨y, h₂ hy, hy'⟩] }
end

lemma is_preirreducible.open_subset {Z U : set α} (hZ : is_preirreducible Z)
  (hU : is_open U) (hU' : U ⊆ Z) :
  is_preirreducible U :=
U.eq_empty_or_nonempty.elim (λ h, h.symm ▸ is_preirreducible_empty)
  (λ h, (hZ.subset_irreducible h hU (λ _, id) hU').2)

lemma is_preirreducible.interior {Z : set α} (hZ : is_preirreducible Z) :
  is_preirreducible (interior Z) :=
hZ.open_subset is_open_interior interior_subset

lemma is_preirreducible.preimage {Z : set α} (hZ : is_preirreducible Z)
  {f : β → α} (hf : open_embedding f) :
  is_preirreducible (f ⁻¹' Z) :=
begin
  rintros U V hU hV ⟨x, hx, hx'⟩ ⟨y, hy, hy'⟩,
  obtain ⟨_, h₁, ⟨z, h₂, rfl⟩, ⟨z', h₃, h₄⟩⟩ := hZ _ _ (hf.is_open_map _ hU) (hf.is_open_map _ hV)
    ⟨f x, hx, set.mem_image_of_mem f hx'⟩ ⟨f y, hy, set.mem_image_of_mem f hy'⟩,
  cases hf.inj h₄,
  exact ⟨z, h₁, h₂, h₃⟩
end

end preirreducible
