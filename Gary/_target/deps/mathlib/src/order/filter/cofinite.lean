/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad, Yury Kudryashov
-/
import order.filter.at_top_bot
import order.filter.pi

/-!
# The cofinite filter

In this file we define

`cofinite`: the filter of sets with finite complement

and prove its basic properties. In particular, we prove that for `ℕ` it is equal to `at_top`.

## TODO

Define filters for other cardinalities of the complement.
-/

open set
open_locale classical

variables {α : Type*}

namespace filter

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : filter α :=
{ sets             := {s | finite sᶜ},
  univ_sets        := by simp only [compl_univ, finite_empty, mem_set_of_eq],
  sets_of_superset := assume s t (hs : finite sᶜ) (st: s ⊆ t),
    hs.subset $ compl_subset_compl.2 st,
  inter_sets       := assume s t (hs : finite sᶜ) (ht : finite (tᶜ)),
    by simp only [compl_inter, finite.union, ht, hs, mem_set_of_eq] }

@[simp] lemma mem_cofinite {s : set α} : s ∈ (@cofinite α) ↔ finite sᶜ := iff.rfl

@[simp] lemma eventually_cofinite {p : α → Prop} :
  (∀ᶠ x in cofinite, p x) ↔ finite {x | ¬p x} := iff.rfl

lemma has_basis_cofinite : has_basis cofinite (λ s : set α, s.finite) compl :=
⟨λ s, ⟨λ h, ⟨sᶜ, h, (compl_compl s).subset⟩, λ ⟨t, htf, hts⟩, htf.subset $ compl_subset_comm.2 hts⟩⟩

instance cofinite_ne_bot [infinite α] : ne_bot (@cofinite α) :=
has_basis_cofinite.ne_bot_iff.2 $ λ s hs, hs.infinite_compl.nonempty

lemma frequently_cofinite_iff_infinite {p : α → Prop} :
  (∃ᶠ x in cofinite, p x) ↔ set.infinite {x | p x} :=
by simp only [filter.frequently, filter.eventually, mem_cofinite, compl_set_of, not_not,
  set.infinite]

/-- The coproduct of the cofinite filters on two types is the cofinite filter on their product. -/
lemma coprod_cofinite {β : Type*} :
  (cofinite : filter α).coprod (cofinite : filter β) = cofinite :=
begin
  ext S,
  simp only [mem_coprod_iff, exists_prop, mem_comap, mem_cofinite],
  split,
  { rintro ⟨⟨A, hAf, hAS⟩, B, hBf, hBS⟩,
    rw [← compl_subset_compl, ← preimage_compl] at hAS hBS,
    exact (hAf.prod hBf).subset (subset_inter hAS hBS) },
  { intro hS,
    refine ⟨⟨(prod.fst '' Sᶜ)ᶜ, _, _⟩, ⟨(prod.snd '' Sᶜ)ᶜ, _, _⟩⟩,
    { simpa using hS.image prod.fst },
    { simpa [compl_subset_comm] using subset_preimage_image prod.fst Sᶜ },
    { simpa using hS.image prod.snd },
    { simpa [compl_subset_comm] using subset_preimage_image prod.snd Sᶜ } },
end

/-- Finite product of finite sets is finite -/
lemma Coprod_cofinite {δ : Type*} {κ : δ → Type*} [fintype δ] :
  filter.Coprod (λ d, (cofinite : filter (κ d))) = cofinite :=
begin
  ext S,
  rcases compl_surjective S with ⟨S, rfl⟩,
  simp_rw [compl_mem_Coprod_iff, mem_cofinite, compl_compl],
  split,
  { rintro ⟨t, htf, hsub⟩,
    exact (finite.pi htf).subset hsub },
  { exact λ hS, ⟨λ i, function.eval i '' S, λ i, hS.image _, subset_pi_eval_image _ _⟩ }
end

end filter

open filter

lemma set.finite.compl_mem_cofinite {s : set α} (hs : s.finite) : sᶜ ∈ (@cofinite α) :=
mem_cofinite.2 $ (compl_compl s).symm ▸ hs

lemma set.finite.eventually_cofinite_nmem {s : set α} (hs : s.finite) : ∀ᶠ x in cofinite, x ∉ s :=
hs.compl_mem_cofinite

lemma finset.eventually_cofinite_nmem (s : finset α) : ∀ᶠ x in cofinite, x ∉ s :=
s.finite_to_set.eventually_cofinite_nmem

lemma set.infinite_iff_frequently_cofinite {s : set α} :
  set.infinite s ↔ (∃ᶠ x in cofinite, x ∈ s) :=
frequently_cofinite_iff_infinite.symm

lemma filter.eventually_cofinite_ne (x : α) : ∀ᶠ a in cofinite, a ≠ x :=
(set.finite_singleton x).eventually_cofinite_nmem

/-- For natural numbers the filters `cofinite` and `at_top` coincide. -/
lemma nat.cofinite_eq_at_top : @cofinite ℕ = at_top :=
begin
  ext s,
  simp only [mem_cofinite, mem_at_top_sets],
  split,
  { assume hs,
    use (hs.to_finset.sup id) + 1,
    assume b hb,
    by_contradiction hbs,
    have := hs.to_finset.subset_range_sup_succ (hs.mem_to_finset.2 hbs),
    exact not_lt_of_le hb (finset.mem_range.1 this) },
  { rintros ⟨N, hN⟩,
    apply (finite_lt_nat N).subset,
    assume n hn,
    change n < N,
    exact lt_of_not_ge (λ hn', hn $ hN n hn') }
end

lemma nat.frequently_at_top_iff_infinite {p : ℕ → Prop} :
  (∃ᶠ n in at_top, p n) ↔ set.infinite {n | p n} :=
by simp only [← nat.cofinite_eq_at_top, frequently_cofinite_iff_infinite]

lemma filter.tendsto.exists_within_forall_le {α β : Type*} [linear_order β] {s : set α}
  (hs : s.nonempty)
  {f : α → β} (hf : filter.tendsto f filter.cofinite filter.at_top) :
  ∃ a₀ ∈ s, ∀ a ∈ s, f a₀ ≤ f a :=
begin
  rcases em (∃ y ∈ s, ∃ x, f y < x) with ⟨y, hys, x, hx⟩|not_all_top,
  { -- the set of points `{y | f y < x}` is nonempty and finite, so we take `min` over this set
    have : finite {y | ¬x ≤ f y} := (filter.eventually_cofinite.mp (tendsto_at_top.1 hf x)),
    simp only [not_le] at this,
    obtain ⟨a₀, ⟨ha₀ : f a₀ < x, ha₀s⟩, others_bigger⟩ :=
      exists_min_image _ f (this.inter_of_left s) ⟨y, hx, hys⟩,
    refine ⟨a₀, ha₀s, λ a has, (lt_or_le (f a) x).elim _ (le_trans ha₀.le)⟩,
    exact λ h, others_bigger a ⟨h, has⟩ },
  { -- in this case, f is constant because all values are at top
    push_neg at not_all_top,
    obtain ⟨a₀, ha₀s⟩ := hs,
    exact ⟨a₀, ha₀s, λ a ha, not_all_top a ha (f a₀)⟩ }
end

lemma filter.tendsto.exists_forall_le {α β : Type*} [nonempty α] [linear_order β]
  {f : α → β} (hf : tendsto f cofinite at_top) :
  ∃ a₀, ∀ a, f a₀ ≤ f a :=
let ⟨a₀, _, ha₀⟩ := hf.exists_within_forall_le univ_nonempty in ⟨a₀, λ a, ha₀ a (mem_univ _)⟩

lemma filter.tendsto.exists_within_forall_ge {α β : Type*} [linear_order β] {s : set α}
  (hs : s.nonempty)
  {f : α → β} (hf : filter.tendsto f filter.cofinite filter.at_bot) :
  ∃ a₀ ∈ s, ∀ a ∈ s, f a ≤ f a₀ :=
@filter.tendsto.exists_within_forall_le _ (order_dual β) _ _ hs _ hf

lemma filter.tendsto.exists_forall_ge {α β : Type*} [nonempty α] [linear_order β]
  {f : α → β} (hf : tendsto f cofinite at_bot) :
  ∃ a₀, ∀ a, f a ≤ f a₀ :=
@filter.tendsto.exists_forall_le _ (order_dual β) _ _ _ hf

/-- For an injective function `f`, inverse images of finite sets are finite. -/
lemma function.injective.tendsto_cofinite {α β : Type*} {f : α → β} (hf : function.injective f) :
  tendsto f cofinite cofinite :=
λ s h, h.preimage (hf.inj_on _)
