/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
import control.traversable.instances
import data.set.finite
import order.copy
import tactic.monotonicity

/-!
# Theory of filters on sets

## Main definitions

* `filter` : filters on a set;
* `at_top`, `at_bot`, `cofinite`, `principal` : specific filters;
* `map`, `comap`, `prod` : operations on filters;
* `tendsto` : limit with respect to filters;
* `eventually` : `f.eventually p` means `{x | p x} ∈ f`;
* `frequently` : `f.frequently p` means `{x | ¬p x} ∉ f`;
* `filter_upwards [h₁, ..., hₙ]` : takes a list of proofs `hᵢ : sᵢ ∈ f`, and replaces a goal `s ∈ f`
  with `∀ x, x ∈ s₁ → ... → x ∈ sₙ → x ∈ s`;
* `ne_bot f` : an utility class stating that `f` is a non-trivial filter.

Filters on a type `X` are sets of sets of `X` satisfying three conditions. They are mostly used to
abstract two related kinds of ideas:
* *limits*, including finite or infinite limits of sequences, finite or infinite limits of functions
  at a point or at infinity, etc...
* *things happening eventually*, including things happening for large enough `n : ℕ`, or near enough
  a point `x`, or for close enough pairs of points, or things happening almost everywhere in the
  sense of measure theory. Dually, filters can also express the idea of *things happening often*:
  for arbitrarily large `n`, or at a point in any neighborhood of given a point etc...

In this file, we define the type `filter X` of filters on `X`, and endow it with a complete lattice
structure. This structure is lifted from the lattice structure on `set (set X)` using the Galois
insertion which maps a filter to its elements in one direction, and an arbitrary set of sets to
the smallest filter containing it in the other direction.
We also prove `filter` is a monadic functor, with a push-forward operation
`filter.map` and a pull-back operation `filter.comap` that form a Galois connections for the
order on filters.
Finally we describe a product operation `filter X → filter Y → filter (X × Y)`.

The examples of filters appearing in the description of the two motivating ideas are:
* `(at_top : filter ℕ)` : made of sets of `ℕ` containing `{n | n ≥ N}` for some `N`
* `𝓝 x` : made of neighborhoods of `x` in a topological space (defined in topology.basic)
* `𝓤 X` : made of entourages of a uniform space (those space are generalizations of metric spaces
  defined in topology.uniform_space.basic)
* `μ.ae` : made of sets whose complement has zero measure with respect to `μ` (defined in
  `measure_theory.measure_space`)

The general notion of limit of a map with respect to filters on the source and target types
is `filter.tendsto`. It is defined in terms of the order and the push-forward operation.
The predicate "happening eventually" is `filter.eventually`, and "happening often" is
`filter.frequently`, whose definitions are immediate after `filter` is defined (but they come
rather late in this file in order to immediately relate them to the lattice structure).

For instance, anticipating on topology.basic, the statement: "if a sequence `u` converges to
some `x` and `u n` belongs to a set `M` for `n` large enough then `x` is in the closure of
`M`" is formalized as: `tendsto u at_top (𝓝 x) → (∀ᶠ n in at_top, u n ∈ M) → x ∈ closure M`,
which is a special case of `mem_closure_of_tendsto` from topology.basic.

## Notations

* `∀ᶠ x in f, p x` : `f.eventually p`;
* `∃ᶠ x in f, p x` : `f.frequently p`;
* `f =ᶠ[l] g` : `∀ᶠ x in l, f x = g x`;
* `f ≤ᶠ[l] g` : `∀ᶠ x in l, f x ≤ g x`;
* `f ×ᶠ g` : `filter.prod f g`, localized in `filter`;
* `𝓟 s` : `principal s`, localized in `filter`.

## References

*  [N. Bourbaki, *General Topology*][bourbaki1966]

Important note: Bourbaki requires that a filter on `X` cannot contain all sets of `X`, which
we do *not* require. This gives `filter X` better formal properties, in particular a bottom element
`⊥` for its lattice structure, at the cost of including the assumption
`[ne_bot f]` in a number of lemmas and definitions.
-/

open set function

universes u v w x y

open_locale classical

/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)

/-- If `F` is a filter on `α`, and `U` a subset of `α` then we can write `U ∈ F` as on paper. -/
instance {α : Type*}: has_mem (set α) (filter α) := ⟨λ U F, U ∈ F.sets⟩

namespace filter
variables {α : Type u} {f g : filter α} {s t : set α}

@[simp] protected lemma mem_mk {t : set (set α)} {h₁ h₂ h₃} : s ∈ mk t h₁ h₂ h₃ ↔ s ∈ t := iff.rfl

@[simp] protected lemma mem_sets : s ∈ f.sets ↔ s ∈ f := iff.rfl

instance inhabited_mem : inhabited {s : set α // s ∈ f} := ⟨⟨univ, f.univ_sets⟩⟩

lemma filter_eq : ∀ {f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f ↔ s ∈ g :=
by simp only [filter_eq_iff, ext_iff, filter.mem_sets]

@[ext]
protected lemma ext : (∀ s, s ∈ f ↔ s ∈ g) → f = g :=
filter.ext_iff.2

@[simp] lemma univ_mem : univ ∈ f :=
f.univ_sets

lemma mem_of_superset {x y : set α} (hx : x ∈ f) (hxy : x ⊆ y) : y ∈ f :=
f.sets_of_superset hx hxy

lemma inter_mem {s t : set α} (hs : s ∈ f) (ht : t ∈ f) : s ∩ t ∈ f :=
f.inter_sets hs ht

@[simp] lemma inter_mem_iff {s t : set α} : s ∩ t ∈ f ↔ s ∈ f ∧ t ∈ f :=
⟨λ h, ⟨mem_of_superset h (inter_subset_left s t),
  mem_of_superset h (inter_subset_right s t)⟩, and_imp.2 inter_mem⟩

lemma diff_mem {s t : set α} (hs : s ∈ f) (ht : tᶜ ∈ f) : s \ t ∈ f :=
inter_mem hs ht

lemma univ_mem' (h : ∀ a, a ∈ s) : s ∈ f :=
mem_of_superset univ_mem (λ x _, h x)

lemma mp_mem (hs : s ∈ f) (h : {x | x ∈ s → x ∈ t} ∈ f) : t ∈ f :=
mem_of_superset (inter_mem hs h) $ λ x ⟨h₁, h₂⟩, h₂ h₁

lemma congr_sets (h : {x | x ∈ s ↔ x ∈ t} ∈ f) : s ∈ f ↔ t ∈ f :=
⟨λ hs, mp_mem hs (mem_of_superset h (λ x, iff.mp)),
 λ hs, mp_mem hs (mem_of_superset h (λ x, iff.mpr))⟩

@[simp] lemma bInter_mem {β : Type v} {s : β → set α} {is : set β} (hf : finite is) :
  (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
finite.induction_on hf (by simp) (λ i s hi _ hs, by simp [hs])

@[simp] lemma bInter_finset_mem {β : Type v} {s : β → set α} (is : finset β) :
  (⋂ i ∈ is, s i) ∈ f ↔ ∀ i ∈ is, s i ∈ f :=
bInter_mem is.finite_to_set

alias bInter_finset_mem ← finset.Inter_mem_sets
attribute [protected] finset.Inter_mem_sets

@[simp] lemma sInter_mem {s : set (set α)} (hfin : finite s) :
  ⋂₀ s ∈ f ↔ ∀ U ∈ s, U ∈ f :=
by rw [sInter_eq_bInter, bInter_mem hfin]

@[simp] lemma Inter_mem {β : Type v} {s : β → set α} [fintype β] :
  (⋂ i, s i) ∈ f ↔ ∀ i, s i ∈ f :=
by simpa using bInter_mem finite_univ

lemma exists_mem_subset_iff : (∃ t ∈ f, t ⊆ s) ↔ s ∈ f :=
⟨λ ⟨t, ht, ts⟩, mem_of_superset ht ts, λ hs, ⟨s, hs, subset.rfl⟩⟩

lemma monotone_mem {f : filter α} : monotone (λ s, s ∈ f) :=
λ s t hst h, mem_of_superset h hst

lemma exists_mem_and_iff {P : set α → Prop} {Q : set α → Prop} (hP : antitone P) (hQ : antitone Q) :
  (∃ u ∈ f, P u) ∧ (∃ u ∈ f, Q u) ↔ (∃ u ∈ f, P u ∧ Q u) :=
begin
  split,
  { rintro ⟨⟨u, huf, hPu⟩, v, hvf, hQv⟩, exact ⟨u ∩ v, inter_mem huf hvf,
    hP (inter_subset_left _ _) hPu, hQ (inter_subset_right _ _) hQv⟩ },
  { rintro ⟨u, huf, hPu, hQu⟩, exact ⟨⟨u, huf, hPu⟩, u, huf, hQu⟩ }
end

end filter

namespace tactic.interactive

open tactic
setup_tactic_parser

/--
`filter_upwards [h₁, ⋯, hₙ]` replaces a goal of the form `s ∈ f` and terms
`h₁ : t₁ ∈ f, ⋯, hₙ : tₙ ∈ f` with `∀ x, x ∈ t₁ → ⋯ → x ∈ tₙ → x ∈ s`.
The list is an optional parameter, `[]` being its default value.

`filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ` is a short form for
`{ filter_upwards [h₁, ⋯, hₙ], intros a₁ a₂ ⋯ aₖ }`.

`filter_upwards [h₁, ⋯, hₙ] using e` is a short form for
`{ filter_upwards [h1, ⋯, hn], exact e }`.

Combining both shortcuts is done by writing `filter_upwards [h₁, ⋯, hₙ] with a₁ a₂ ⋯ aₖ using e`.
Note that in this case, the `aᵢ` terms can be used in `e`.
-/
meta def filter_upwards
  (s : parse types.pexpr_list?)
  (wth : parse with_ident_list?)
  (tgt : parse (tk "using" *> texpr)?) : tactic unit :=
do
  (s.get_or_else []).reverse.mmap (λ e, eapplyc `filter.mp_mem >> eapply e),
  eapplyc `filter.univ_mem',
  `[dsimp only [set.mem_set_of_eq]],
  let wth := wth.get_or_else [],
  if ¬wth.empty then intros wth else skip,
  match tgt with
  | some e := exact e
  | none   := skip
  end

add_tactic_doc
{ name := "filter_upwards",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.filter_upwards],
  tags := ["goal management", "lemma application"] }

end tactic.interactive

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
  univ_sets        := subset_univ s,
  sets_of_superset := λ x y hx, subset.trans hx,
  inter_sets       := λ x y, subset_inter }

localized "notation `𝓟` := filter.principal" in filter

instance : inhabited (filter α) :=
⟨𝓟 ∅⟩

@[simp] lemma mem_principal {s t : set α} : s ∈ 𝓟 t ↔ t ⊆ s := iff.rfl

lemma mem_principal_self (s : set α) : s ∈ 𝓟 s := subset.rfl

end principal

open_locale filter

section join

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : filter (filter α)) : filter α :=
{ sets             := {s | {t : filter α | s ∈ t} ∈ f},
  univ_sets        := by simp only [mem_set_of_eq, univ_sets, ← filter.mem_sets, set_of_true],
  sets_of_superset := λ x y hx xy,
    mem_of_superset hx $ λ f h, mem_of_superset h xy,
  inter_sets       := λ x y hx hy,
    mem_of_superset (inter_mem hx hy) $ λ f ⟨h₁, h₂⟩, inter_mem h₁ h₂ }

@[simp] lemma mem_join {s : set α} {f : filter (filter α)} :
  s ∈ join f ↔ {t | s ∈ t} ∈ f := iff.rfl

end join

section lattice

instance : partial_order (filter α) :=
{ le            := λ f g, ∀ ⦃U : set α⦄, U ∈ g → U ∈ f,
  le_antisymm   := λ a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := λ a, subset.rfl,
  le_trans      := λ a b c h₁ h₂, subset.trans h₂ h₁ }

theorem le_def {f g : filter α} : f ≤ g ↔ ∀ x ∈ g, x ∈ f := iff.rfl

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive generate_sets (g : set (set α)) : set α → Prop
| basic {s : set α}      : s ∈ g → generate_sets s
| univ                   : generate_sets univ
| superset {s t : set α} : generate_sets s → s ⊆ t → generate_sets t
| inter {s t : set α}    : generate_sets s → generate_sets t → generate_sets (s ∩ t)

/-- `generate g` is the smallest filter containing the sets `g`. -/
def generate (g : set (set α)) : filter α :=
{ sets             := generate_sets g,
  univ_sets        := generate_sets.univ,
  sets_of_superset := λ x y, generate_sets.superset,
  inter_sets       := λ s t, generate_sets.inter }

lemma sets_iff_generate {s : set (set α)} {f : filter α} : f ≤ filter.generate s ↔ s ⊆ f.sets :=
iff.intro
  (λ h u hu, h $ generate_sets.basic $ hu)
  (λ h u hu, hu.rec_on h univ_mem
    (λ x y _ hxy hx, mem_of_superset hx hxy)
    (λ x y _ _ hx hy, inter_mem hx hy))

lemma mem_generate_iff {s : set $ set α} {U : set α} :
  U ∈ generate s ↔ ∃ t ⊆ s, finite t ∧ ⋂₀ t ⊆ U :=
begin
  split ; intro h,
  { induction h with V V_in V W V_in hVW hV V W V_in W_in hV hW,
    { use {V},
      simp [V_in] },
    { use ∅,
      simp [subset.refl, univ] },
    { rcases hV with ⟨t, hts, htfin, hinter⟩,
      exact ⟨t, hts, htfin, hinter.trans hVW⟩ },
    { rcases hV with ⟨t, hts, htfin, htinter⟩,
      rcases hW with ⟨z, hzs, hzfin, hzinter⟩,
      refine ⟨t ∪ z, union_subset hts hzs, htfin.union hzfin, _⟩,
      rw sInter_union,
      exact inter_subset_inter htinter hzinter } },
  { rcases h with ⟨t, ts, tfin, h⟩,
    apply generate_sets.superset _ h,
    revert ts,
    apply finite.induction_on tfin,
    { intro h,
      rw sInter_empty,
      exact generate_sets.univ },
    { intros V r hV rfin hinter h,
      cases insert_subset.mp h with V_in r_sub,
      rw [insert_eq V r, sInter_union],
      apply generate_sets.inter _ (hinter r_sub),
      rw sInter_singleton,
      exact generate_sets.basic V_in } },
end

/-- `mk_of_closure s hs` constructs a filter on `α` whose elements set is exactly
`s : set (set α)`, provided one gives the assumption `hs : (generate s).sets = s`. -/
protected def mk_of_closure (s : set (set α)) (hs : (generate s).sets = s) : filter α :=
{ sets             := s,
  univ_sets        := hs ▸ (univ_mem : univ ∈ generate s),
  sets_of_superset := λ x y, hs ▸ (mem_of_superset : x ∈ generate s → x ⊆ y → y ∈ generate s),
  inter_sets       := λ x y, hs ▸ (inter_mem : x ∈ generate s → y ∈ generate s →
                        x ∩ y ∈ generate s) }

lemma mk_of_closure_sets {s : set (set α)} {hs : (generate s).sets = s} :
  filter.mk_of_closure s hs = generate s :=
filter.ext $ λ u,
show u ∈ (filter.mk_of_closure s hs).sets ↔ u ∈ (generate s).sets, from hs.symm ▸ iff.rfl

/-- Galois insertion from sets of sets into filters. -/
def gi_generate (α : Type*) :
  @galois_insertion (set (set α)) (order_dual (filter α)) _ _ filter.generate filter.sets :=
{ gc        := λ s f, sets_iff_generate,
  le_l_u    := λ f u h, generate_sets.basic h,
  choice    := λ s hs, filter.mk_of_closure s (le_antisymm hs $ sets_iff_generate.1 $ le_rfl),
  choice_eq := λ s hs, mk_of_closure_sets }

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f) (b ∈ g), s = a ∩ b },
  univ_sets        := ⟨_, univ_mem, _, univ_mem, by simp⟩,
  sets_of_superset := begin
    rintro x y ⟨a, ha, b, hb, rfl⟩ xy,
    refine ⟨a ∪ y, mem_of_superset ha (subset_union_left a y),
            b ∪ y, mem_of_superset hb (subset_union_left b y), _⟩,
    rw [← inter_union_distrib_right, union_eq_self_of_subset_left xy]
  end,
  inter_sets       := begin
    rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩,
    refine ⟨a ∩ c, inter_mem ha hc, b ∩ d, inter_mem hb hd, _⟩,
    ac_refl
  end }⟩

lemma mem_inf_iff {f g : filter α} {s : set α} :
  s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, s = t₁ ∩ t₂ := iff.rfl

lemma mem_inf_of_left {f g : filter α} {s : set α} (h : s ∈ f) : s ∈ f ⊓ g :=
⟨s, h, univ, univ_mem, (inter_univ s).symm⟩

lemma mem_inf_of_right {f g : filter α} {s : set α} (h : s ∈ g) : s ∈ f ⊓ g :=
⟨univ, univ_mem, s, h, (univ_inter s).symm⟩

lemma inter_mem_inf {α : Type u} {f g : filter α} {s t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s ∩ t ∈ f ⊓ g :=
⟨s, hs, t, ht, rfl⟩

lemma mem_inf_of_inter {f g : filter α} {s t u : set α} (hs : s ∈ f) (ht : t ∈ g) (h : s ∩ t ⊆ u) :
  u ∈ f ⊓ g :=
mem_of_superset (inter_mem_inf hs ht) h

lemma mem_inf_iff_superset {f g : filter α} {s : set α} :
  s ∈ f ⊓ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ∩ t₂ ⊆ s :=
⟨λ ⟨t₁, h₁, t₂, h₂, eq⟩, ⟨t₁, h₁, t₂, h₂, eq ▸ subset.rfl⟩,
  λ ⟨t₁, h₁, t₂, h₂, sub⟩, mem_inf_of_inter h₁ h₂ sub⟩

instance : has_top (filter α) :=
⟨{ sets            := {s | ∀ x, x ∈ s},
  univ_sets        := λ x, mem_univ x,
  sets_of_superset := λ x y hx hxy a, hxy (hx a),
  inter_sets       := λ x y hx hy a, mem_inter (hx _) (hy _) }⟩

lemma mem_top_iff_forall {s : set α} : s ∈ (⊤ : filter α) ↔ (∀ x, x ∈ s) :=
iff.rfl

@[simp] lemma mem_top {s : set α} : s ∈ (⊤ : filter α) ↔ s = univ :=
by rw [mem_top_iff_forall, eq_univ_iff_forall]

section complete_lattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/

private def original_complete_lattice : complete_lattice (filter α) :=
@order_dual.complete_lattice _ (gi_generate α).lift_complete_lattice

local attribute [instance] original_complete_lattice

instance : complete_lattice (filter α) := original_complete_lattice.copy
  /- le  -/ filter.partial_order.le rfl
  /- top -/ (filter.has_top).1
  (top_unique $ λ s hs, by simp [mem_top.1 hs])
  /- bot -/ _ rfl
  /- sup -/ _ rfl
  /- inf -/ (filter.has_inf).1
  begin
    ext f g : 2,
    exact le_antisymm
      (le_inf (λ s, mem_inf_of_left) (λ s, mem_inf_of_right))
      (begin
        rintro s ⟨a, ha, b, hb, rfl⟩,
        exact inter_sets _ (@inf_le_left (filter α) _ _ _ _ ha)
                           (@inf_le_right (filter α) _ _ _ _ hb)
       end)
  end
  /- Sup -/ (join ∘ 𝓟) (by { ext s x, exact mem_Inter₂.symm.trans
    (set.ext_iff.1 (sInter_image _ _) x).symm})
  /- Inf -/ _ rfl

end complete_lattice

/-- A filter is `ne_bot` if it is not equal to `⊥`, or equivalently the empty set
does not belong to the filter. Bourbaki include this assumption in the definition
of a filter but we prefer to have a `complete_lattice` structure on filter, so
we use a typeclass argument in lemmas instead. -/
class ne_bot (f : filter α) : Prop := (ne' : f ≠ ⊥)

lemma ne_bot_iff {f : filter α} : ne_bot f ↔ f ≠ ⊥ := ⟨λ h, h.1, λ h, ⟨h⟩⟩

lemma ne_bot.ne {f : filter α} (hf : ne_bot f) : f ≠ ⊥ := ne_bot.ne'

@[simp] lemma not_ne_bot {α : Type*} {f : filter α} : ¬ f.ne_bot ↔ f = ⊥ :=
not_iff_comm.1 ne_bot_iff.symm

lemma ne_bot.mono {f g : filter α} (hf : ne_bot f) (hg : f ≤ g) : ne_bot g :=
⟨ne_bot_of_le_ne_bot hf.1 hg⟩

lemma ne_bot_of_le {f g : filter α} [hf : ne_bot f] (hg : f ≤ g) : ne_bot g :=
hf.mono hg

@[simp] lemma sup_ne_bot {f g : filter α} : ne_bot (f ⊔ g) ↔ ne_bot f ∨ ne_bot g :=
by simp [ne_bot_iff, not_and_distrib]

lemma bot_sets_eq : (⊥ : filter α).sets = univ := rfl

lemma sup_sets_eq {f g : filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
(gi_generate α).gc.u_inf

lemma Sup_sets_eq {s : set (filter α)} : (Sup s).sets = (⋂ f ∈ s, (f : filter α).sets) :=
(gi_generate α).gc.u_Inf

lemma supr_sets_eq {f : ι → filter α} : (supr f).sets = (⋂ i, (f i).sets) :=
(gi_generate α).gc.u_infi

lemma generate_empty : filter.generate ∅ = (⊤ : filter α) :=
(gi_generate α).gc.l_bot

lemma generate_univ : filter.generate univ = (⊥ : filter α) :=
mk_of_closure_sets.symm

lemma generate_union {s t : set (set α)} :
  filter.generate (s ∪ t) = filter.generate s ⊓ filter.generate t :=
(gi_generate α).gc.l_sup

lemma generate_Union {s : ι → set (set α)} :
  filter.generate (⋃ i, s i) = (⨅ i, filter.generate (s i)) :=
(gi_generate α).gc.l_supr

@[simp] lemma mem_bot {s : set α} : s ∈ (⊥ : filter α) :=
trivial

@[simp] lemma mem_sup {f g : filter α} {s : set α} :
  s ∈ f ⊔ g ↔ s ∈ f ∧ s ∈ g :=
iff.rfl

lemma union_mem_sup {f g : filter α} {s t : set α} (hs : s ∈ f) (ht : t ∈ g) :
  s ∪ t ∈ f ⊔ g :=
⟨mem_of_superset hs (subset_union_left s t), mem_of_superset ht (subset_union_right s t)⟩

@[simp] lemma mem_Sup {x : set α} {s : set (filter α)} :
  x ∈ Sup s ↔ (∀ f ∈ s, x ∈ (f : filter α)) :=
iff.rfl

@[simp] lemma mem_supr {x : set α} {f : ι → filter α} :
  x ∈ supr f ↔ (∀ i, x ∈ f i) :=
by simp only [← filter.mem_sets, supr_sets_eq, iff_self, mem_Inter]

@[simp] lemma supr_ne_bot {f : ι → filter α} : (⨆ i, f i).ne_bot ↔ ∃ i, (f i).ne_bot :=
by simp [ne_bot_iff]

lemma infi_eq_generate (s : ι → filter α) : infi s = generate (⋃ i, (s i).sets) :=
show generate _ = generate _, from congr_arg _ $ congr_arg Sup $ (range_comp _ _).symm

lemma mem_infi_of_mem {f : ι → filter α} (i : ι) : ∀ {s}, s ∈ f i → s ∈ ⨅ i, f i :=
show (⨅ i, f i) ≤ f i, from infi_le _ _

lemma mem_infi_of_Inter {ι} {s : ι → filter α} {U : set α} {I : set ι} (I_fin : finite I)
  {V : I → set α} (hV : ∀ i, V i ∈ s i) (hU : (⋂ i, V i) ⊆ U) : U ∈ ⨅ i, s i :=
begin
  haveI := I_fin.fintype,
  refine mem_of_superset (Inter_mem.2 $ λ i, _) hU,
  exact mem_infi_of_mem i (hV _)
end

lemma mem_infi {ι} {s : ι → filter α} {U : set α} : (U ∈ ⨅ i, s i) ↔
  ∃ I : set ι, finite I ∧ ∃ V : I → set α, (∀ i, V i ∈ s i) ∧ U = ⋂ i, V i :=
begin
  split,
  { rw [infi_eq_generate, mem_generate_iff],
    rintro ⟨t, tsub, tfin, tinter⟩,
    rcases eq_finite_Union_of_finite_subset_Union tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩,
    rw sInter_Union at tinter,
    set V := λ i, U ∪ ⋂₀ σ i with hV,
    have V_in : ∀ i, V i ∈ s i,
    { rintro i,
      have : (⋂₀ σ i) ∈ s i,
      { rw sInter_mem (σfin _),
        apply σsub },
      exact mem_of_superset this (subset_union_right _ _) },
    refine ⟨I, Ifin, V, V_in, _⟩,
    rwa [hV, ← union_Inter, union_eq_self_of_subset_right] },
  { rintro ⟨I, Ifin, V, V_in, rfl⟩,
    exact mem_infi_of_Inter Ifin V_in subset.rfl }
end

lemma mem_infi' {ι} {s : ι → filter α} {U : set α} : (U ∈ ⨅ i, s i) ↔
  ∃ I : set ι, finite I ∧ ∃ V : ι → set α, (∀ i, V i ∈ s i) ∧
    (∀ i ∉ I, V i = univ) ∧ (U = ⋂ i ∈ I, V i) ∧ U = ⋂ i, V i :=
begin
  simp only [mem_infi, set_coe.forall', bInter_eq_Inter],
  refine ⟨_, λ ⟨I, If, V, hVs, _, hVU, _⟩, ⟨I, If, λ i, V i, λ i, hVs i, hVU⟩⟩,
  rintro ⟨I, If, V, hV, rfl⟩,
  refine ⟨I, If, λ i, if hi : i ∈ I then V ⟨i, hi⟩ else univ, λ i, _, λ i hi, _, _⟩,
  { split_ifs, exacts [hV _, univ_mem] },
  { exact dif_neg hi },
  { simp only [Inter_dite, bInter_eq_Inter, dif_pos (subtype.coe_prop _), subtype.coe_eta,
      Inter_univ, inter_univ, eq_self_iff_true, true_and] }
end

lemma exists_Inter_of_mem_infi {ι : Type*} {α : Type*} {f : ι → filter α} {s}
  (hs : s ∈ ⨅ i, f i) : ∃ t : ι → set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
let ⟨I, If, V, hVs, hV', hVU, hVU'⟩ := mem_infi'.1 hs in ⟨V, hVs, hVU'⟩

lemma mem_infi_of_fintype {ι : Type*} [fintype ι] {α : Type*} {f : ι → filter α} (s) :
  s ∈ (⨅ i, f i) ↔ ∃ t : ι → set α, (∀ i, t i ∈ f i) ∧ s = ⋂ i, t i :=
begin
  refine ⟨exists_Inter_of_mem_infi, _⟩,
  rintro ⟨t, ht, rfl⟩,
  exact Inter_mem.2 (λ i, mem_infi_of_mem i (ht i))
end

@[simp] lemma le_principal_iff {s : set α} {f : filter α} : f ≤ 𝓟 s ↔ s ∈ f :=
show (∀ {t}, s ⊆ t → t ∈ f) ↔ s ∈ f,
  from ⟨λ h, h (subset.refl s), λ hs t ht, mem_of_superset hs ht⟩

lemma principal_mono {s t : set α} : 𝓟 s ≤ 𝓟 t ↔ s ⊆ t :=
by simp only [le_principal_iff, iff_self, mem_principal]

@[mono] lemma monotone_principal : monotone (𝓟 : set α → filter α) :=
λ _ _, principal_mono.2

@[simp] lemma principal_eq_iff_eq {s t : set α} : 𝓟 s = 𝓟 t ↔ s = t :=
by simp only [le_antisymm_iff, le_principal_iff, mem_principal]; refl

@[simp] lemma join_principal_eq_Sup {s : set (filter α)} : join (𝓟 s) = Sup s := rfl

@[simp] lemma principal_univ : 𝓟 (univ : set α) = ⊤ :=
top_unique $ by simp only [le_principal_iff, mem_top, eq_self_iff_true]

@[simp] lemma principal_empty : 𝓟 (∅ : set α) = ⊥ :=
bot_unique $ λ s _, empty_subset _

lemma generate_eq_binfi (S : set (set α)) : generate S = ⨅ s ∈ S, 𝓟 s :=
eq_of_forall_le_iff $ λ f, by simp [sets_iff_generate, le_principal_iff, subset_def]

/-! ### Lattice equations -/

lemma empty_mem_iff_bot {f : filter α} : ∅ ∈ f ↔ f = ⊥ :=
⟨λ h, bot_unique $ λ s _, mem_of_superset h (empty_subset s),
  λ h, h.symm ▸ mem_bot⟩

lemma nonempty_of_mem {f : filter α} [hf : ne_bot f] {s : set α} (hs : s ∈ f) :
  s.nonempty :=
s.eq_empty_or_nonempty.elim (λ h, absurd hs (h.symm ▸ mt empty_mem_iff_bot.mp hf.1)) id

lemma ne_bot.nonempty_of_mem {f : filter α} (hf : ne_bot f) {s : set α} (hs : s ∈ f) :
  s.nonempty :=
@nonempty_of_mem α f hf s hs

@[simp] lemma empty_not_mem (f : filter α) [ne_bot f] : ¬(∅ ∈ f) :=
λ h, (nonempty_of_mem h).ne_empty rfl

lemma nonempty_of_ne_bot (f : filter α) [ne_bot f] : nonempty α :=
nonempty_of_exists $ nonempty_of_mem (univ_mem : univ ∈ f)

lemma compl_not_mem {f : filter α} {s : set α} [ne_bot f] (h : s ∈ f) : sᶜ ∉ f :=
λ hsc, (nonempty_of_mem (inter_mem h hsc)).ne_empty $ inter_compl_self s

lemma filter_eq_bot_of_is_empty [is_empty α] (f : filter α) : f = ⊥ :=
empty_mem_iff_bot.mp $ univ_mem' is_empty_elim

protected lemma disjoint_iff {f g : filter α} :
  disjoint f g ↔ ∃ (s ∈ f) (t ∈ g), disjoint s t :=
by simp only [disjoint_iff, ← empty_mem_iff_bot, mem_inf_iff,
  inf_eq_inter, bot_eq_empty, @eq_comm _ ∅]

lemma disjoint_of_disjoint_of_mem {f g : filter α} {s t : set α} (h : disjoint s t)
  (hs : s ∈ f) (ht : t ∈ g) : disjoint f g :=
filter.disjoint_iff.mpr ⟨s, hs, t, ht, h⟩

lemma inf_eq_bot_iff {f g : filter α} :
  f ⊓ g = ⊥ ↔ ∃ (U ∈ f) (V ∈ g), U ∩ V = ∅ :=
by simpa only [disjoint_iff] using filter.disjoint_iff

/-- There is exactly one filter on an empty type. --/
-- TODO[gh-6025]: make this globally an instance once safe to do so
local attribute [instance]
protected def unique [is_empty α] : unique (filter α) :=
{ default := ⊥, uniq := filter_eq_bot_of_is_empty }

lemma forall_mem_nonempty_iff_ne_bot {f : filter α} :
  (∀ (s : set α), s ∈ f → s.nonempty) ↔ ne_bot f :=
⟨λ h, ⟨λ hf, empty_not_nonempty (h ∅ $ hf.symm ▸ mem_bot)⟩, @nonempty_of_mem _ _⟩

lemma nontrivial_iff_nonempty : nontrivial (filter α) ↔ nonempty α :=
⟨λ ⟨⟨f, g, hfg⟩⟩, by_contra $
  λ h, hfg $ by haveI : is_empty α := not_nonempty_iff.1 h; exact subsingleton.elim _ _,
  λ ⟨x⟩, ⟨⟨⊤, ⊥, ne_bot.ne $ forall_mem_nonempty_iff_ne_bot.1 $ λ s hs,
    by rwa [mem_top.1 hs, ← nonempty_iff_univ_nonempty]⟩⟩⟩

lemma eq_Inf_of_mem_iff_exists_mem {S : set (filter α)} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ f ∈ S, s ∈ f) : l = Inf S :=
le_antisymm (le_Inf $ λ f hf s hs, h.2 ⟨f, hf, hs⟩)
  (λ s hs, let ⟨f, hf, hs⟩ := h.1 hs in (Inf_le hf : Inf S ≤ f) hs)

lemma eq_infi_of_mem_iff_exists_mem {f : ι → filter α} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ i, s ∈ f i) :
  l = infi f :=
eq_Inf_of_mem_iff_exists_mem $ λ s, h.trans exists_range_iff.symm

lemma eq_binfi_of_mem_iff_exists_mem {f : ι → filter α} {p : ι  → Prop} {l : filter α}
  (h : ∀ {s}, s ∈ l ↔ ∃ i (_ : p i), s ∈ f i) :
  l = ⨅ i (_ : p i), f i :=
begin
  rw [infi_subtype'],
  apply eq_infi_of_mem_iff_exists_mem,
  intro s,
  exact h.trans ⟨λ ⟨i, pi, si⟩, ⟨⟨i, pi⟩, si⟩, λ ⟨⟨i, pi⟩, si⟩, ⟨i, pi, si⟩⟩
end

lemma infi_sets_eq {f : ι → filter α} (h : directed (≥) f) [ne : nonempty ι] :
  (infi f).sets = (⋃ i, (f i).sets) :=
let ⟨i⟩ := ne, u := { filter .
    sets             := (⋃ i, (f i).sets),
    univ_sets        := by simp only [mem_Union]; exact ⟨i, univ_mem⟩,
    sets_of_superset := by simp only [mem_Union, exists_imp_distrib];
                        intros x y i hx hxy; exact ⟨i, mem_of_superset hx hxy⟩,
    inter_sets       :=
    begin
      simp only [mem_Union, exists_imp_distrib],
      intros x y a hx b hy,
      rcases h a b with ⟨c, ha, hb⟩,
      exact ⟨c, inter_mem (ha hx) (hb hy)⟩
    end } in
have u = infi f, from eq_infi_of_mem_iff_exists_mem
  (λ s, by simp only [filter.mem_mk, mem_Union, filter.mem_sets]),
congr_arg filter.sets this.symm

lemma mem_infi_of_directed {f : ι → filter α} (h : directed (≥) f) [nonempty ι] (s) :
  s ∈ infi f ↔ ∃ i, s ∈ f i :=
by simp only [← filter.mem_sets, infi_sets_eq h, mem_Union]

lemma mem_binfi_of_directed {f : β → filter α} {s : set β}
  (h : directed_on (f ⁻¹'o (≥)) s) (ne : s.nonempty) {t : set α} :
  t ∈ (⨅ i ∈ s, f i) ↔ ∃ i ∈ s, t ∈ f i :=
by haveI : nonempty {x // x  ∈ s} := ne.to_subtype;
  erw [infi_subtype', mem_infi_of_directed h.directed_coe, subtype.exists]; refl

lemma binfi_sets_eq {f : β → filter α} {s : set β}
  (h : directed_on (f ⁻¹'o (≥)) s) (ne : s.nonempty) :
  (⨅ i ∈ s, f i).sets = ⋃ i ∈ s, (f i).sets :=
ext $ λ t, by simp [mem_binfi_of_directed h ne]

lemma infi_sets_eq_finite {ι : Type*} (f : ι → filter α) :
  (⨅ i, f i).sets = (⋃ t : finset ι, (⨅ i ∈ t, f i).sets) :=
begin
  rw [infi_eq_infi_finset, infi_sets_eq],
  exact (directed_of_sup $ λ s₁ s₂ hs, infi_le_infi $ λ i, infi_le_infi_const $ λ h, hs h),
end

lemma infi_sets_eq_finite' (f : ι → filter α) :
  (⨅ i, f i).sets = (⋃ t : finset (plift ι), (⨅ i ∈ t, f (plift.down i)).sets) :=
by { rw [← infi_sets_eq_finite, ← equiv.plift.surjective.infi_comp], refl }

lemma mem_infi_finite {ι : Type*} {f : ι → filter α} (s) :
  s ∈ infi f ↔ ∃ t : finset ι, s ∈ ⨅ i ∈ t, f i :=
(set.ext_iff.1 (infi_sets_eq_finite f) s).trans mem_Union

lemma mem_infi_finite' {f : ι → filter α} (s) :
  s ∈ infi f ↔ ∃ t : finset (plift ι), s ∈ ⨅ i ∈ t, f (plift.down i) :=
(set.ext_iff.1 (infi_sets_eq_finite' f) s).trans mem_Union

@[simp] lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter.ext $ λ x, by simp only [mem_sup, mem_join]

@[simp] lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} :
  (⨆ x, join (f x)) = join (⨆ x, f x) :=
filter.ext $ λ x, by simp only [mem_supr, mem_join]

instance : distrib_lattice (filter α) :=
{ le_sup_inf :=
  begin
    intros x y z s,
    simp only [and_assoc, mem_inf_iff, mem_sup, exists_prop, exists_imp_distrib, and_imp],
    rintro hs t₁ ht₁ t₂ ht₂ rfl,
    exact ⟨t₁, x.sets_of_superset hs (inter_subset_left t₁ t₂),
      ht₁,
      t₂,
      x.sets_of_superset hs (inter_subset_right t₁ t₂),
      ht₂,
      rfl⟩
  end,
  ..filter.complete_lattice }

/- the complementary version with ⨆ i, f ⊓ g i does not hold! -/
lemma infi_sup_left {f : filter α} {g : ι → filter α} : (⨅ x, f ⊔ g x) = f ⊔ infi g :=
begin
  refine le_antisymm _ (le_infi $ λ i, sup_le_sup_left (infi_le _ _) _),
  rintro t ⟨h₁, h₂⟩,
  rw [infi_sets_eq_finite'] at h₂,
  simp only [mem_Union, (finset.inf_eq_infi _ _).symm] at h₂,
  rcases h₂ with ⟨s, hs⟩,
  suffices : (⨅ i, f ⊔ g i) ≤ f ⊔ s.inf (λ i, g i.down), { exact this ⟨h₁, hs⟩ },
  refine finset.induction_on s _ _,
  { exact le_sup_of_le_right le_top },
  { rintro ⟨i⟩ s his ih,
    rw [finset.inf_insert, sup_inf_left],
    exact le_inf (infi_le _ _) ih }
end

lemma infi_sup_right {f : filter α} {g : ι → filter α} : (⨅ x, g x ⊔ f) = infi g ⊔ f :=
by simp [sup_comm, ← infi_sup_left]

lemma binfi_sup_right (p : ι → Prop) (f : ι → filter α) (g : filter α) :
  (⨅ i (h : p i), (f i ⊔ g)) = (⨅ i (h : p i), f i) ⊔ g :=
by rw [infi_subtype', infi_sup_right, infi_subtype']

lemma binfi_sup_left (p : ι → Prop) (f : ι → filter α) (g : filter α) :
  (⨅ i (h : p i), (g ⊔ f i)) = g ⊔ (⨅ i (h : p i), f i) :=
by rw [infi_subtype', infi_sup_left, infi_subtype']

lemma mem_infi_finset {s : finset α} {f : α → filter β} {t : set β} :
  t ∈ (⨅ a ∈ s, f a) ↔ (∃ p : α → set β, (∀ a ∈ s, p a ∈ f a) ∧ t = ⋂ a ∈ s, p a) :=
begin
  simp only [← finset.set_bInter_coe, bInter_eq_Inter, infi_subtype'],
  refine ⟨λ h, _, _⟩,
  { rcases (mem_infi_of_fintype _).1 h with ⟨p, hp, rfl⟩,
    refine ⟨λ a, if h : a ∈ s then p ⟨a, h⟩ else univ, λ a ha, by simpa [ha] using hp ⟨a, ha⟩, _⟩,
    refine Inter_congr_of_surjective id surjective_id _,
    rintro ⟨a, ha⟩, simp [ha] },
  { rintro ⟨p, hpf, rfl⟩,
    exact Inter_mem.2 (λ a, mem_infi_of_mem a (hpf a a.2)) }
end

/-- If `f : ι → filter α` is directed, `ι` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed` for a version assuming `nonempty α` instead of `nonempty ι`. -/
lemma infi_ne_bot_of_directed' {f : ι → filter α} [nonempty ι]
  (hd : directed (≥) f) (hb : ∀ i, ne_bot (f i)) : ne_bot (infi f) :=
⟨begin
  intro h,
  have he : ∅  ∈ (infi f), from h.symm ▸ (mem_bot : ∅ ∈ (⊥ : filter α)),
  obtain ⟨i, hi⟩ : ∃ i, ∅ ∈ f i,
    from (mem_infi_of_directed hd ∅).1 he,
  exact (hb i).ne (empty_mem_iff_bot.1 hi)
end⟩

/-- If `f : ι → filter α` is directed, `α` is not empty, and `∀ i, f i ≠ ⊥`, then `infi f ≠ ⊥`.
See also `infi_ne_bot_of_directed'` for a version assuming `nonempty ι` instead of `nonempty α`. -/
lemma infi_ne_bot_of_directed {f : ι → filter α}
  [hn : nonempty α] (hd : directed (≥) f) (hb : ∀ i, ne_bot (f i)) : ne_bot (infi f) :=
if hι : nonempty ι then @infi_ne_bot_of_directed' _ _ _ hι hd hb else
⟨λ h : infi f = ⊥,
  have univ ⊆ (∅ : set α),
  begin
    rw [←principal_mono, principal_univ, principal_empty, ←h],
    exact (le_infi $ λ i, false.elim $ hι ⟨i⟩)
  end,
  let ⟨x⟩ := hn in this (mem_univ x)⟩

lemma infi_ne_bot_iff_of_directed' {f : ι → filter α} [nonempty ι] (hd : directed (≥) f) :
  ne_bot (infi f) ↔ ∀ i, ne_bot (f i) :=
⟨λ H i, H.mono (infi_le _ i), infi_ne_bot_of_directed' hd⟩

lemma infi_ne_bot_iff_of_directed {f : ι → filter α} [nonempty α] (hd : directed (≥) f) :
  ne_bot (infi f) ↔ (∀ i, ne_bot (f i)) :=
⟨λ H i, H.mono (infi_le _ i), infi_ne_bot_of_directed hd⟩

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → filter α} {s : set α} (hs : s ∈ infi f) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀ {i s₁ s₂}, s₁ ∈ f i → p s₂ → p (s₁ ∩ s₂)) : p s :=
begin
  rw [mem_infi_finite'] at hs,
  simp only [← finset.inf_eq_infi] at hs,
  rcases hs with ⟨is, his⟩,
  revert s,
  refine finset.induction_on is _ _,
  { intros s hs, rwa [mem_top.1 hs] },
  { rintro ⟨i⟩ js his ih s hs,
    rw [finset.inf_insert, mem_inf_iff] at hs,
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, rfl⟩,
    exact ins hs₁ (ih hs₂) }
end

/-! #### `principal` equations -/

@[simp] lemma inf_principal {s t : set α} : 𝓟 s ⊓ 𝓟 t = 𝓟 (s ∩ t) :=
le_antisymm
  (by simp only [le_principal_iff, mem_inf_iff]; exact ⟨s, subset.rfl, t, subset.rfl, rfl⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp] lemma sup_principal {s t : set α} : 𝓟 s ⊔ 𝓟 t = 𝓟 (s ∪ t) :=
filter.ext $ λ u, by simp only [union_subset_iff, mem_sup, mem_principal]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆ x, 𝓟 (s x)) = 𝓟 (⋃ i, s i) :=
filter.ext $ λ x, by simp only [mem_supr, mem_principal, Union_subset_iff]

@[simp] lemma principal_eq_bot_iff {s : set α} : 𝓟 s = ⊥ ↔ s = ∅ :=
empty_mem_iff_bot.symm.trans $ mem_principal.trans subset_empty_iff

@[simp] lemma principal_ne_bot_iff {s : set α} : ne_bot (𝓟 s) ↔ s.nonempty :=
ne_bot_iff.trans $ (not_congr principal_eq_bot_iff).trans ne_empty_iff_nonempty

lemma is_compl_principal (s : set α) : is_compl (𝓟 s) (𝓟 sᶜ) :=
⟨by simp only [inf_principal, inter_compl_self, principal_empty, le_refl],
  by simp only [sup_principal, union_compl_self, principal_univ, le_refl]⟩

theorem mem_inf_principal' {f : filter α} {s t : set α} :
  s ∈ f ⊓ 𝓟 t ↔ tᶜ ∪ s ∈ f :=
by simp only [← le_principal_iff, (is_compl_principal s).le_left_iff, disjoint_assoc, inf_principal,
  ← (is_compl_principal (t ∩ sᶜ)).le_right_iff, compl_inter, compl_compl]

theorem mem_inf_principal {f : filter α} {s t : set α} :
  s ∈ f ⊓ 𝓟 t ↔ {x | x ∈ t → x ∈ s} ∈ f :=
by { simp only [mem_inf_principal', imp_iff_not_or], refl }

lemma supr_inf_principal (f : ι → filter α) (s : set α) :
  (⨆ i, f i ⊓ 𝓟 s) = (⨆ i, f i) ⊓ 𝓟 s :=
by { ext, simp only [mem_supr, mem_inf_principal] }

lemma inf_principal_eq_bot {f : filter α} {s : set α} : f ⊓ 𝓟 s = ⊥ ↔ sᶜ ∈ f :=
by { rw [← empty_mem_iff_bot, mem_inf_principal], refl }

lemma mem_of_eq_bot {f : filter α} {s : set α} (h : f ⊓ 𝓟 sᶜ = ⊥) : s ∈ f :=
by rwa [inf_principal_eq_bot, compl_compl] at h

lemma diff_mem_inf_principal_compl {f : filter α} {s : set α} (hs : s ∈ f) (t : set α) :
  s \ t ∈ f ⊓ 𝓟 tᶜ :=
inter_mem_inf hs $ mem_principal_self tᶜ

lemma principal_le_iff {s : set α} {f : filter α} :
  𝓟 s ≤ f ↔ ∀ V ∈ f, s ⊆ V :=
begin
  change (∀ V, V ∈ f → V ∈ _) ↔ _,
  simp_rw mem_principal,
end

@[simp] lemma infi_principal_finset {ι : Type w} (s : finset ι) (f : ι → set α) :
  (⨅ i ∈ s, 𝓟 (f i)) = 𝓟 (⋂ i ∈ s, f i) :=
begin
  induction s using finset.induction_on with i s hi hs,
  { simp },
  { rw [finset.infi_insert, finset.set_bInter_insert, hs, inf_principal] },
end

@[simp] lemma infi_principal_fintype {ι : Type w} [fintype ι] (f : ι → set α) :
  (⨅ i, 𝓟 (f i)) = 𝓟 (⋂ i, f i) :=
by simpa using infi_principal_finset finset.univ f

lemma infi_principal_finite {ι : Type w} {s : set ι} (hs : finite s) (f : ι → set α) :
  (⨅ i ∈ s, 𝓟 (f i)) = 𝓟 (⋂ i ∈ s, f i) :=
begin
  lift s to finset ι using hs,
  exact_mod_cast infi_principal_finset s f
end

end lattice

@[mono] lemma join_mono {f₁ f₂ : filter (filter α)} (h : f₁ ≤ f₂) :
  join f₁ ≤ join f₂ :=
λ s hs, h hs

/-! ### Eventually -/

/-- `f.eventually p` or `∀ᶠ x in f, p x` mean that `{x | p x} ∈ f`. E.g., `∀ᶠ x in at_top, p x`
means that `p` holds true for sufficiently large `x`. -/
protected def eventually (p : α → Prop) (f : filter α) : Prop := {x | p x} ∈ f

notation `∀ᶠ` binders ` in ` f `, ` r:(scoped p, filter.eventually p f) := r

lemma eventually_iff {f : filter α} {P : α → Prop} : (∀ᶠ x in f, P x) ↔ {x | P x} ∈ f :=
iff.rfl

@[simp] lemma eventually_mem_set {s : set α} {l : filter α} : (∀ᶠ x in l, x ∈ s) ↔ s ∈ l := iff.rfl

protected lemma ext' {f₁ f₂ : filter α}
  (h : ∀ p : α → Prop, (∀ᶠ x in f₁, p x) ↔ (∀ᶠ x in f₂, p x)) :
  f₁ = f₂ :=
filter.ext h

lemma eventually.filter_mono {f₁ f₂ : filter α} (h : f₁ ≤ f₂) {p : α → Prop}
  (hp : ∀ᶠ x in f₂, p x) :
  ∀ᶠ x in f₁, p x :=
h hp

lemma eventually_of_mem {f : filter α} {P : α → Prop} {U : set α} (hU : U ∈ f) (h : ∀ x ∈ U, P x) :
  ∀ᶠ x in f, P x :=
mem_of_superset hU h

protected lemma eventually.and {p q : α → Prop} {f : filter α} :
  f.eventually p → f.eventually q → ∀ᶠ x in f, p x ∧ q x :=
inter_mem

@[simp]
lemma eventually_true (f : filter α) : ∀ᶠ x in f, true := univ_mem

lemma eventually_of_forall {p : α → Prop} {f : filter α} (hp : ∀ x, p x) :
  ∀ᶠ x in f, p x :=
univ_mem' hp

@[simp] lemma eventually_false_iff_eq_bot {f : filter α} :
  (∀ᶠ x in f, false) ↔ f = ⊥ :=
empty_mem_iff_bot

@[simp] lemma eventually_const {f : filter α} [t : ne_bot f] {p : Prop} :
  (∀ᶠ x in f, p) ↔ p :=
classical.by_cases (λ h : p, by simp [h]) (λ h, by simpa [h] using t.ne)

lemma eventually_iff_exists_mem {p : α → Prop} {f : filter α} :
  (∀ᶠ x in f, p x) ↔ ∃ v ∈ f, ∀ y ∈ v, p y :=
exists_mem_subset_iff.symm

lemma eventually.exists_mem {p : α → Prop} {f : filter α} (hp : ∀ᶠ x in f, p x) :
  ∃ v ∈ f, ∀ y ∈ v, p y :=
eventually_iff_exists_mem.1 hp

lemma eventually.mp {p q : α → Prop} {f : filter α} (hp : ∀ᶠ x in f, p x)
  (hq : ∀ᶠ x in f, p x → q x) :
  ∀ᶠ x in f, q x :=
mp_mem hp hq

lemma eventually.mono {p q : α → Prop} {f : filter α} (hp : ∀ᶠ x in f, p x)
  (hq : ∀ x, p x → q x) :
  ∀ᶠ x in f, q x :=
hp.mp (eventually_of_forall hq)

@[simp] lemma eventually_and {p q : α → Prop} {f : filter α} :
  (∀ᶠ x in f, p x ∧ q x) ↔ (∀ᶠ x in f, p x) ∧ (∀ᶠ x in f, q x) :=
inter_mem_iff

lemma eventually.congr {f : filter α} {p q : α → Prop} (h' : ∀ᶠ x in f, p x)
  (h : ∀ᶠ x in f, p x ↔ q x) : ∀ᶠ x in f, q x :=
h'.mp (h.mono $ λ x hx, hx.mp)

lemma eventually_congr {f : filter α} {p q : α → Prop} (h : ∀ᶠ x in f, p x ↔ q x) :
  (∀ᶠ x in f, p x) ↔ (∀ᶠ x in f, q x) :=
⟨λ hp, hp.congr h, λ hq, hq.congr $ by simpa only [iff.comm] using h⟩

@[simp] lemma eventually_all {ι} [fintype ι] {l} {p : ι → α → Prop} :
  (∀ᶠ x in l, ∀ i, p i x) ↔ ∀ i, ∀ᶠ x in l, p i x :=
by simpa only [filter.eventually, set_of_forall] using Inter_mem

@[simp] lemma eventually_all_finite {ι} {I : set ι} (hI : I.finite) {l} {p : ι → α → Prop} :
  (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ (∀ i ∈ I, ∀ᶠ x in l, p i x) :=
by simpa only [filter.eventually, set_of_forall] using bInter_mem hI

alias eventually_all_finite ← set.finite.eventually_all
attribute [protected] set.finite.eventually_all

@[simp] lemma eventually_all_finset {ι} (I : finset ι) {l} {p : ι → α → Prop} :
  (∀ᶠ x in l, ∀ i ∈ I, p i x) ↔ ∀ i ∈ I, ∀ᶠ x in l, p i x :=
I.finite_to_set.eventually_all

alias eventually_all_finset ← finset.eventually_all
attribute [protected] finset.eventually_all

@[simp] lemma eventually_or_distrib_left {f : filter α} {p : Prop} {q : α → Prop} :
  (∀ᶠ x in f, p ∨ q x) ↔ (p ∨ ∀ᶠ x in f, q x) :=
classical.by_cases (λ h : p, by simp [h]) (λ h, by simp [h])

@[simp] lemma eventually_or_distrib_right {f : filter α} {p : α → Prop} {q : Prop} :
  (∀ᶠ x in f, p x ∨ q) ↔ ((∀ᶠ x in f, p x) ∨ q) :=
by simp only [or_comm _ q, eventually_or_distrib_left]

@[simp] lemma eventually_imp_distrib_left {f : filter α} {p : Prop} {q : α → Prop} :
  (∀ᶠ x in f, p → q x) ↔ (p → ∀ᶠ x in f, q x) :=
by simp only [imp_iff_not_or, eventually_or_distrib_left]

@[simp]
lemma eventually_bot {p : α → Prop} : ∀ᶠ x in ⊥, p x := ⟨⟩

@[simp]
lemma eventually_top {p : α → Prop} : (∀ᶠ x in ⊤, p x) ↔ (∀ x, p x) :=
iff.rfl

@[simp] lemma eventually_sup {p : α → Prop} {f g : filter α} :
  (∀ᶠ x in f ⊔ g, p x) ↔ (∀ᶠ x in f, p x) ∧ (∀ᶠ x in g, p x) :=
iff.rfl

@[simp]
lemma eventually_Sup {p : α → Prop} {fs : set (filter α)} :
  (∀ᶠ x in Sup fs, p x) ↔ (∀ f ∈ fs, ∀ᶠ x in f, p x) :=
iff.rfl

@[simp]
lemma eventually_supr {p : α → Prop} {fs : β → filter α} :
  (∀ᶠ x in (⨆ b, fs b), p x) ↔ (∀ b, ∀ᶠ x in fs b, p x) :=
mem_supr

@[simp]
lemma eventually_principal {a : set α} {p : α → Prop} :
  (∀ᶠ x in 𝓟 a, p x) ↔ (∀ x ∈ a, p x) :=
iff.rfl

lemma eventually_inf {f g : filter α} {p : α → Prop} :
  (∀ᶠ x in f ⊓ g, p x) ↔ ∃ (s ∈ f) (t ∈ g), ∀ x ∈ s ∩ t, p x :=
mem_inf_iff_superset

theorem eventually_inf_principal {f : filter α} {p : α → Prop} {s : set α} :
  (∀ᶠ x in f ⊓ 𝓟 s, p x) ↔ ∀ᶠ x in f, x ∈ s → p x :=
mem_inf_principal

/-! ### Frequently -/

/-- `f.frequently p` or `∃ᶠ x in f, p x` mean that `{x | ¬p x} ∉ f`. E.g., `∃ᶠ x in at_top, p x`
means that there exist arbitrarily large `x` for which `p` holds true. -/
protected def frequently (p : α → Prop) (f : filter α) : Prop := ¬∀ᶠ x in f, ¬p x

notation `∃ᶠ` binders ` in ` f `, ` r:(scoped p, filter.frequently p f) := r

lemma eventually.frequently {f : filter α} [ne_bot f] {p : α → Prop} (h : ∀ᶠ x in f, p x) :
  ∃ᶠ x in f, p x :=
compl_not_mem h

lemma frequently_of_forall {f : filter α} [ne_bot f] {p : α → Prop} (h : ∀ x, p x) :
  ∃ᶠ x in f, p x :=
eventually.frequently (eventually_of_forall h)

lemma frequently.mp {p q : α → Prop} {f : filter α} (h : ∃ᶠ x in f, p x)
  (hpq : ∀ᶠ x in f, p x → q x) :
  ∃ᶠ x in f, q x :=
mt (λ hq, hq.mp $ hpq.mono $ λ x, mt) h

lemma frequently.filter_mono {p : α → Prop} {f g : filter α} (h : ∃ᶠ x in f, p x) (hle : f ≤ g) :
  ∃ᶠ x in g, p x :=
mt (λ h', h'.filter_mono hle) h

lemma frequently.mono {p q : α → Prop} {f : filter α} (h : ∃ᶠ x in f, p x)
  (hpq : ∀ x, p x → q x) :
  ∃ᶠ x in f, q x :=
h.mp (eventually_of_forall hpq)

lemma frequently.and_eventually {p q : α → Prop} {f : filter α}
  (hp : ∃ᶠ x in f, p x) (hq : ∀ᶠ x in f, q x) :
  ∃ᶠ x in f, p x ∧ q x :=
begin
  refine mt (λ h, hq.mp $ h.mono _) hp,
  exact λ x hpq hq hp, hpq ⟨hp, hq⟩
end

lemma eventually.and_frequently {p q : α → Prop} {f : filter α}
  (hp : ∀ᶠ x in f, p x) (hq : ∃ᶠ x in f, q x) :
  ∃ᶠ x in f, p x ∧ q x :=
by simpa only [and.comm] using hq.and_eventually hp

lemma frequently.exists {p : α → Prop} {f : filter α} (hp : ∃ᶠ x in f, p x) : ∃ x, p x :=
begin
  by_contradiction H,
  replace H : ∀ᶠ x in f, ¬ p x, from eventually_of_forall (not_exists.1 H),
  exact hp H
end

lemma eventually.exists {p : α → Prop} {f : filter α} [ne_bot f] (hp : ∀ᶠ x in f, p x) :
  ∃ x, p x :=
hp.frequently.exists

lemma frequently_iff_forall_eventually_exists_and {p : α → Prop} {f : filter α} :
  (∃ᶠ x in f, p x) ↔ ∀ {q : α → Prop}, (∀ᶠ x in f, q x) → ∃ x, p x ∧ q x :=
⟨λ hp q hq, (hp.and_eventually hq).exists,
  λ H hp, by simpa only [and_not_self, exists_false] using H hp⟩

lemma frequently_iff {f : filter α} {P : α → Prop} :
  (∃ᶠ x in f, P x) ↔ ∀ {U}, U ∈ f → ∃ x ∈ U, P x :=
begin
  simp only [frequently_iff_forall_eventually_exists_and, exists_prop, and_comm (P _)],
  refl
end

@[simp] lemma not_eventually {p : α → Prop} {f : filter α} :
  (¬ ∀ᶠ x in f, p x) ↔ (∃ᶠ x in f, ¬ p x) :=
by simp [filter.frequently]

@[simp] lemma not_frequently {p : α → Prop} {f : filter α} :
  (¬ ∃ᶠ x in f, p x) ↔ (∀ᶠ x in f, ¬ p x) :=
by simp only [filter.frequently, not_not]

@[simp] lemma frequently_true_iff_ne_bot (f : filter α) : (∃ᶠ x in f, true) ↔ ne_bot f :=
by simp [filter.frequently, -not_eventually, eventually_false_iff_eq_bot, ne_bot_iff]

@[simp] lemma frequently_false (f : filter α) : ¬ ∃ᶠ x in f, false := by simp

@[simp] lemma frequently_const {f : filter α} [ne_bot f] {p : Prop} :
  (∃ᶠ x in f, p) ↔ p :=
classical.by_cases (λ h : p, by simpa [h]) (λ h, by simp [h])

@[simp] lemma frequently_or_distrib {f : filter α} {p q : α → Prop} :
  (∃ᶠ x in f, p x ∨ q x) ↔ (∃ᶠ x in f, p x) ∨ (∃ᶠ x in f, q x) :=
by simp only [filter.frequently, ← not_and_distrib, not_or_distrib, eventually_and]

lemma frequently_or_distrib_left {f : filter α} [ne_bot f] {p : Prop} {q : α → Prop} :
  (∃ᶠ x in f, p ∨ q x) ↔ (p ∨ ∃ᶠ x in f, q x) :=
by simp

lemma frequently_or_distrib_right {f : filter α} [ne_bot f] {p : α → Prop} {q : Prop} :
  (∃ᶠ x in f, p x ∨ q) ↔ (∃ᶠ x in f, p x) ∨ q :=
by simp

@[simp] lemma frequently_imp_distrib {f : filter α} {p q : α → Prop} :
  (∃ᶠ x in f, p x → q x) ↔ ((∀ᶠ x in f, p x) → ∃ᶠ x in f, q x) :=
by simp [imp_iff_not_or, not_eventually, frequently_or_distrib]

lemma frequently_imp_distrib_left {f : filter α} [ne_bot f] {p : Prop} {q : α → Prop} :
  (∃ᶠ x in f, p → q x) ↔ (p → ∃ᶠ x in f, q x) :=
by simp

lemma frequently_imp_distrib_right {f : filter α} [ne_bot f] {p : α → Prop} {q : Prop} :
  (∃ᶠ x in f, p x → q) ↔ ((∀ᶠ x in f, p x) → q) :=
by simp

@[simp] lemma eventually_imp_distrib_right {f : filter α} {p : α → Prop} {q : Prop} :
  (∀ᶠ x in f, p x → q) ↔ ((∃ᶠ x in f, p x) → q) :=
by simp only [imp_iff_not_or, eventually_or_distrib_right, not_frequently]

@[simp] lemma frequently_and_distrib_left {f : filter α} {p : Prop} {q : α → Prop} :
  (∃ᶠ x in f, p ∧ q x) ↔ (p ∧ ∃ᶠ x in f, q x) :=
by simp only [filter.frequently, not_and, eventually_imp_distrib_left, not_imp]

@[simp] lemma frequently_and_distrib_right {f : filter α} {p : α → Prop} {q : Prop} :
  (∃ᶠ x in f, p x ∧ q) ↔ ((∃ᶠ x in f, p x) ∧ q) :=
by simp only [and_comm _ q, frequently_and_distrib_left]

@[simp] lemma frequently_bot {p : α → Prop} : ¬ ∃ᶠ x in ⊥, p x := by simp

@[simp]
lemma frequently_top {p : α → Prop} : (∃ᶠ x in ⊤, p x) ↔ (∃ x, p x) :=
by simp [filter.frequently]

@[simp]
lemma frequently_principal {a : set α} {p : α → Prop} :
  (∃ᶠ x in 𝓟 a, p x) ↔ (∃ x ∈ a, p x) :=
by simp [filter.frequently, not_forall]

lemma frequently_sup {p : α → Prop} {f g : filter α} :
  (∃ᶠ x in f ⊔ g, p x) ↔ (∃ᶠ x in f, p x) ∨ (∃ᶠ x in g, p x) :=
by simp only [filter.frequently, eventually_sup, not_and_distrib]

@[simp]
lemma frequently_Sup {p : α → Prop} {fs : set (filter α)} :
  (∃ᶠ x in Sup fs, p x) ↔ (∃ f ∈ fs, ∃ᶠ x in f, p x) :=
by simp [filter.frequently, -not_eventually, not_forall]

@[simp]
lemma frequently_supr {p : α → Prop} {fs : β → filter α} :
  (∃ᶠ x in (⨆ b, fs b), p x) ↔ (∃ b, ∃ᶠ x in fs b, p x) :=
by simp [filter.frequently, -not_eventually, not_forall]

/-!
### Relation “eventually equal”
-/

/-- Two functions `f` and `g` are *eventually equal* along a filter `l` if the set of `x` such that
`f x = g x` belongs to `l`. -/
def eventually_eq (l : filter α) (f g : α → β) : Prop := ∀ᶠ x in l, f x = g x

notation f ` =ᶠ[`:50 l:50 `] `:0 g:50 := eventually_eq l f g

lemma eventually_eq.eventually {l : filter α} {f g : α → β} (h : f =ᶠ[l] g) :
  ∀ᶠ x in l, f x = g x :=
h

lemma eventually_eq.rw {l : filter α} {f g : α → β} (h : f =ᶠ[l] g) (p : α → β → Prop)
  (hf : ∀ᶠ x in l, p x (f x)) :
  ∀ᶠ x in l, p x (g x) :=
hf.congr $ h.mono $ λ x hx, hx ▸ iff.rfl

lemma eventually_eq_set {s t : set α} {l : filter α} :
   s =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ s ↔ x ∈ t :=
eventually_congr $ eventually_of_forall $ λ x, ⟨eq.to_iff, iff.to_eq⟩

alias eventually_eq_set ↔ filter.eventually_eq.mem_iff filter.eventually.set_eq

@[simp] lemma eventually_eq_univ {s : set α} {l : filter α} : s =ᶠ[l] univ ↔ s ∈ l :=
by simp [eventually_eq_set]

lemma eventually_eq.exists_mem {l : filter α} {f g : α → β} (h : f =ᶠ[l] g) :
  ∃ s ∈ l, eq_on f g s :=
h.exists_mem

lemma eventually_eq_of_mem {l : filter α} {f g : α → β} {s : set α}
  (hs : s ∈ l) (h : eq_on f g s) : f =ᶠ[l] g :=
eventually_of_mem hs h

lemma eventually_eq_iff_exists_mem {l : filter α} {f g : α → β} :
  (f =ᶠ[l] g) ↔ ∃ s ∈ l, eq_on f g s :=
eventually_iff_exists_mem

lemma eventually_eq.filter_mono {l l' : filter α} {f g : α → β} (h₁ : f =ᶠ[l] g) (h₂ : l' ≤ l) :
  f =ᶠ[l'] g :=
h₂ h₁

@[refl] lemma eventually_eq.refl (l : filter α) (f : α → β) :
  f =ᶠ[l] f :=
eventually_of_forall $ λ x, rfl

lemma eventually_eq.rfl {l : filter α} {f : α → β} : f =ᶠ[l] f := eventually_eq.refl l f

@[symm] lemma eventually_eq.symm {f g : α → β} {l : filter α} (H : f =ᶠ[l] g) :
  g =ᶠ[l] f :=
H.mono $ λ _, eq.symm

@[trans] lemma eventually_eq.trans {f g h : α → β} {l : filter α}
  (H₁ : f =ᶠ[l] g) (H₂ : g =ᶠ[l] h) :
  f =ᶠ[l] h :=
H₂.rw (λ x y, f x = y) H₁

lemma eventually_eq.prod_mk {l} {f f' : α → β} (hf : f =ᶠ[l] f') {g g' : α → γ} (hg : g =ᶠ[l] g') :
  (λ x, (f x, g x)) =ᶠ[l] (λ x, (f' x, g' x)) :=
hf.mp $ hg.mono $ by { intros, simp only * }

lemma eventually_eq.fun_comp {f g : α → β} {l : filter α} (H : f =ᶠ[l] g) (h : β → γ) :
  (h ∘ f) =ᶠ[l] (h ∘ g) :=
H.mono $ λ x hx, congr_arg h hx

lemma eventually_eq.comp₂ {δ} {f f' : α → β} {g g' : α → γ} {l} (Hf : f =ᶠ[l] f') (h : β → γ → δ)
  (Hg : g =ᶠ[l] g') :
  (λ x, h (f x) (g x)) =ᶠ[l] (λ x, h (f' x) (g' x)) :=
(Hf.prod_mk Hg).fun_comp (uncurry h)

@[to_additive]
lemma eventually_eq.mul [has_mul β] {f f' g g' : α → β} {l : filter α} (h : f =ᶠ[l] g)
  (h' : f' =ᶠ[l] g') :
  ((λ x, f x * f' x) =ᶠ[l] (λ x, g x * g' x)) :=
h.comp₂ (*) h'

@[to_additive]
lemma eventually_eq.inv [has_inv β] {f g : α → β} {l : filter α} (h : f =ᶠ[l] g) :
  ((λ x, (f x)⁻¹) =ᶠ[l] (λ x, (g x)⁻¹)) :=
h.fun_comp has_inv.inv

lemma eventually_eq.div [group_with_zero β] {f f' g g' : α → β} {l : filter α} (h : f =ᶠ[l] g)
  (h' : f' =ᶠ[l] g') :
  ((λ x, f x / f' x) =ᶠ[l] (λ x, g x / g' x)) :=
by simpa only [div_eq_mul_inv] using h.mul h'.inv

lemma eventually_eq.div' [group β] {f f' g g' : α → β} {l : filter α} (h : f =ᶠ[l] g)
  (h' : f' =ᶠ[l] g') :
  ((λ x, f x / f' x) =ᶠ[l] (λ x, g x / g' x)) :=
by simpa only [div_eq_mul_inv] using h.mul h'.inv

lemma eventually_eq.sub [add_group β] {f f' g g' : α → β} {l : filter α} (h : f =ᶠ[l] g)
  (h' : f' =ᶠ[l] g') :
  ((λ x, f x - f' x) =ᶠ[l] (λ x, g x - g' x)) :=
by simpa only [sub_eq_add_neg] using h.add h'.neg

lemma eventually_eq.inter {s t s' t' : set α} {l : filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
  (s ∩ s' : set α) =ᶠ[l] (t ∩ t' : set α) :=
h.comp₂ (∧) h'

lemma eventually_eq.union {s t s' t' : set α} {l : filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
  (s ∪ s' : set α) =ᶠ[l] (t ∪ t' : set α) :=
h.comp₂ (∨) h'

lemma eventually_eq.compl {s t : set α} {l : filter α} (h : s =ᶠ[l] t) :
  (sᶜ : set α) =ᶠ[l] (tᶜ : set α) :=
h.fun_comp not

lemma eventually_eq.diff {s t s' t' : set α} {l : filter α} (h : s =ᶠ[l] t) (h' : s' =ᶠ[l] t') :
  (s \ s' : set α) =ᶠ[l] (t \ t' : set α) :=
h.inter h'.compl

lemma eventually_eq_empty {s : set α} {l : filter α} :
  s =ᶠ[l] (∅ : set α) ↔ ∀ᶠ x in l, x ∉ s :=
eventually_eq_set.trans $ by simp

lemma inter_eventually_eq_left {s t : set α} {l : filter α} :
  (s ∩ t : set α) =ᶠ[l] s ↔ ∀ᶠ x in l, x ∈ s → x ∈ t :=
by simp only [eventually_eq_set, mem_inter_eq, and_iff_left_iff_imp]

lemma inter_eventually_eq_right {s t : set α} {l : filter α} :
  (s ∩ t : set α) =ᶠ[l] t ↔ ∀ᶠ x in l, x ∈ t → x ∈ s :=
by rw [inter_comm, inter_eventually_eq_left]

@[simp] lemma eventually_eq_principal {s : set α} {f g : α → β} :
  f =ᶠ[𝓟 s] g ↔ eq_on f g s :=
iff.rfl

lemma eventually_eq_inf_principal_iff {F : filter α} {s : set α} {f g : α → β} :
  (f =ᶠ[F ⊓ 𝓟 s] g) ↔ ∀ᶠ x in F, x ∈ s → f x = g x :=
eventually_inf_principal

lemma eventually_eq.sub_eq [add_group β] {f g : α → β} {l : filter α} (h : f =ᶠ[l] g) :
  f - g =ᶠ[l] 0 :=
by simpa using (eventually_eq.sub (eventually_eq.refl l f) h).symm

lemma eventually_eq_iff_sub [add_group β] {f g : α → β} {l : filter α} :
  f =ᶠ[l] g ↔ f - g =ᶠ[l] 0 :=
⟨λ h, h.sub_eq, λ h, by simpa using h.add (eventually_eq.refl l g)⟩

section has_le

variables [has_le β] {l : filter α}

/-- A function `f` is eventually less than or equal to a function `g` at a filter `l`. -/
def eventually_le (l : filter α) (f g : α → β) : Prop := ∀ᶠ x in l, f x ≤ g x

notation f ` ≤ᶠ[`:50 l:50 `] `:0 g:50 := eventually_le l f g

lemma eventually_le.congr {f f' g g' : α → β} (H : f ≤ᶠ[l] g) (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
  f' ≤ᶠ[l] g' :=
H.mp $ hg.mp $ hf.mono $ λ x hf hg H, by rwa [hf, hg] at H

lemma eventually_le_congr {f f' g g' : α → β} (hf : f =ᶠ[l] f') (hg : g =ᶠ[l] g') :
  f ≤ᶠ[l] g ↔ f' ≤ᶠ[l] g' :=
⟨λ H, H.congr hf hg, λ H, H.congr hf.symm hg.symm⟩

end has_le

section preorder

variables [preorder β] {l : filter α} {f g h : α → β}

lemma eventually_eq.le (h : f =ᶠ[l] g) : f ≤ᶠ[l] g := h.mono $ λ x, le_of_eq

@[refl] lemma eventually_le.refl (l : filter α) (f : α → β) :
  f ≤ᶠ[l] f :=
eventually_eq.rfl.le

lemma eventually_le.rfl : f ≤ᶠ[l] f := eventually_le.refl l f

@[trans] lemma eventually_le.trans (H₁ : f ≤ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
H₂.mp $ H₁.mono $ λ x, le_trans

@[trans] lemma eventually_eq.trans_le (H₁ : f =ᶠ[l] g) (H₂ : g ≤ᶠ[l] h) : f ≤ᶠ[l] h :=
H₁.le.trans H₂

@[trans] lemma eventually_le.trans_eq (H₁ : f ≤ᶠ[l] g) (H₂ : g =ᶠ[l] h) : f ≤ᶠ[l] h :=
H₁.trans H₂.le

end preorder

lemma eventually_le.antisymm [partial_order β] {l : filter α} {f g : α → β}
  (h₁ : f ≤ᶠ[l] g) (h₂ : g ≤ᶠ[l] f) :
  f =ᶠ[l] g :=
h₂.mp $ h₁.mono $ λ x, le_antisymm

lemma eventually_le_antisymm_iff [partial_order β] {l : filter α} {f g : α → β} :
  f =ᶠ[l] g ↔ f ≤ᶠ[l] g ∧ g ≤ᶠ[l] f :=
by simp only [eventually_eq, eventually_le, le_antisymm_iff, eventually_and]

lemma eventually_le.le_iff_eq [partial_order β] {l : filter α} {f g : α → β} (h : f ≤ᶠ[l] g) :
  g ≤ᶠ[l] f ↔ g =ᶠ[l] f :=
⟨λ h', h'.antisymm h, eventually_eq.le⟩

lemma eventually.ne_of_lt [preorder β] {l : filter α} {f g : α → β}
  (h : ∀ᶠ x in l, f x < g x) : ∀ᶠ x in l, f x ≠ g x :=
h.mono (λ x hx, hx.ne)

lemma eventually.ne_top_of_lt [partial_order β] [order_top β] {l : filter α} {f g : α → β}
  (h : ∀ᶠ x in l, f x < g x) : ∀ᶠ x in l, f x ≠ ⊤ :=
h.mono (λ x hx, hx.ne_top)

lemma eventually.lt_top_of_ne [partial_order β] [order_top β] {l : filter α} {f : α → β}
  (h : ∀ᶠ x in l, f x ≠ ⊤) : ∀ᶠ x in l, f x < ⊤ :=
h.mono (λ x hx, hx.lt_top)

lemma eventually.lt_top_iff_ne_top [partial_order β] [order_top β] {l : filter α} {f : α → β} :
  (∀ᶠ x in l, f x < ⊤) ↔ ∀ᶠ x in l, f x ≠ ⊤ :=
⟨eventually.ne_of_lt, eventually.lt_top_of_ne⟩

@[mono] lemma eventually_le.inter {s t s' t' : set α} {l : filter α} (h : s ≤ᶠ[l] t)
  (h' : s' ≤ᶠ[l] t') :
  (s ∩ s' : set α) ≤ᶠ[l] (t ∩ t' : set α) :=
h'.mp $ h.mono $ λ x, and.imp

@[mono] lemma eventually_le.union {s t s' t' : set α} {l : filter α} (h : s ≤ᶠ[l] t)
  (h' : s' ≤ᶠ[l] t') :
  (s ∪ s' : set α) ≤ᶠ[l] (t ∪ t' : set α) :=
h'.mp $ h.mono $ λ x, or.imp

@[mono] lemma eventually_le.compl {s t : set α} {l : filter α} (h : s ≤ᶠ[l] t) :
  (tᶜ : set α) ≤ᶠ[l] (sᶜ : set α) :=
h.mono $ λ x, mt

@[mono] lemma eventually_le.diff {s t s' t' : set α} {l : filter α} (h : s ≤ᶠ[l] t)
  (h' : t' ≤ᶠ[l] s') :
  (s \ s' : set α) ≤ᶠ[l] (t \ t' : set α) :=
h.inter h'.compl

lemma join_le {f : filter (filter α)} {l : filter α} (h : ∀ᶠ m in f, m ≤ l) : join f ≤ l :=
λ s hs, h.mono $ λ m hm, hm hs

/-! ### Push-forwards, pull-backs, and the monad structure -/

section map

/-- The forward map of a filter -/
def map (m : α → β) (f : filter α) : filter β :=
{ sets             := preimage m ⁻¹' f.sets,
  univ_sets        := univ_mem,
  sets_of_superset := λ s t hs st, mem_of_superset hs $ preimage_mono st,
  inter_sets       := λ s t hs ht, inter_mem hs ht }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (𝓟 s) = 𝓟 (set.image f s) :=
filter.ext $ λ a, image_subset_iff.symm

variables {f : filter α} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] lemma eventually_map {P : β → Prop} :
  (∀ᶠ b in map m f, P b) ↔ ∀ᶠ a in f, P (m a) :=
iff.rfl

@[simp] lemma frequently_map {P : β → Prop} :
  (∃ᶠ b in map m f, P b) ↔ ∃ᶠ a in f, P (m a) :=
iff.rfl

@[simp] lemma mem_map : t ∈ map m f ↔ m ⁻¹' t ∈ f := iff.rfl

lemma mem_map' : t ∈ map m f ↔ {x | m x ∈ t} ∈ f := iff.rfl

lemma image_mem_map (hs : s ∈ f) : m '' s ∈ map m f :=
f.sets_of_superset hs $ subset_preimage_image m s

lemma image_mem_map_iff (hf : injective m) : m '' s ∈ map m f ↔ s ∈ f :=
⟨λ h, by rwa [← preimage_image_eq s hf], image_mem_map⟩

lemma range_mem_map : range m ∈ map m f :=
by { rw ←image_univ, exact image_mem_map univ_mem }

lemma mem_map_iff_exists_image : t ∈ map m f ↔ (∃ s ∈ f, m '' s ⊆ t) :=
⟨λ ht, ⟨m ⁻¹' t, ht, image_preimage_subset _ _⟩,
  λ ⟨s, hs, ht⟩, mem_of_superset (image_mem_map hs) ht⟩

@[simp] lemma map_id : filter.map id f = f :=
filter_eq $ rfl

@[simp] lemma map_id' : filter.map (λ x, x) f = f := map_id

@[simp] lemma map_compose : filter.map m' ∘ filter.map m = filter.map (m' ∘ m) :=
funext $ λ _, filter_eq $ rfl

@[simp] lemma map_map : filter.map m' (filter.map m f) = filter.map (m' ∘ m) f :=
congr_fun (@@filter.map_compose m m') f

/-- If functions `m₁` and `m₂` are eventually equal at a filter `f`, then
they map this filter to the same filter. -/
lemma map_congr {m₁ m₂ : α → β} {f : filter α} (h : m₁ =ᶠ[f] m₂) :
  map m₁ f = map m₂ f :=
filter.ext' $ λ p,
by { simp only [eventually_map], exact eventually_congr (h.mono $ λ x hx, hx ▸ iff.rfl) }

end map

section comap

/-- The inverse map of a filter -/
def comap (m : α → β) (f : filter β) : filter α :=
{ sets             := { s | ∃ t ∈ f, m ⁻¹' t ⊆ s },
  univ_sets        := ⟨univ, univ_mem, by simp only [subset_univ, preimage_univ]⟩,
  sets_of_superset := λ a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', ma'a.trans ab⟩,
  inter_sets       := λ a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
    ⟨a' ∩ b', inter_mem ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩ }

lemma eventually_comap' {f : filter β} {φ : α → β} {p : β → Prop} (hf : ∀ᶠ b in f, p b) :
  ∀ᶠ a in comap φ f, p (φ a) :=
⟨_, hf, (λ a h, h)⟩

@[simp] lemma eventually_comap {f : filter β} {φ : α → β} {P : α → Prop} :
  (∀ᶠ a in comap φ f, P a) ↔ ∀ᶠ b in f, ∀ a, φ a = b → P a :=
begin
  split ; intro h,
  { rcases h with ⟨t, t_in, ht⟩,
    apply mem_of_superset t_in,
    rintro y y_in _ rfl,
    apply ht y_in },
  { exact ⟨_, h, λ _ x_in, x_in _ rfl⟩ }
end

@[simp] lemma frequently_comap {f : filter β} {φ : α → β} {P : α → Prop} :
  (∃ᶠ a in comap φ f, P a) ↔ ∃ᶠ b in f, ∃ a, φ a = b ∧ P a :=
by simp only [filter.frequently, eventually_comap, not_exists, not_and]

end comap

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`.

Unfortunately, this `bind` does not result in the expected applicative. See `filter.seq` for the
applicative instance. -/
def bind (f : filter α) (m : α → filter β) : filter β := join (map m f)

/-- The applicative sequentiation operation. This is not induced by the bind operation. -/
def seq (f : filter (α → β)) (g : filter α) : filter β :=
⟨{ s | ∃ u ∈ f, ∃ t ∈ g, (∀ m ∈ u, ∀ x ∈ t, (m : α → β) x ∈ s) },
  ⟨univ, univ_mem, univ, univ_mem,
    by simp only [forall_prop_of_true, mem_univ, forall_true_iff]⟩,
  λ s₀ s₁ ⟨t₀, t₁, h₀, h₁, h⟩ hst, ⟨t₀, t₁, h₀, h₁, λ x hx y hy, hst $ h _ hx _ hy⟩,
  λ s₀ s₁ ⟨t₀, ht₀, t₁, ht₁, ht⟩ ⟨u₀, hu₀, u₁, hu₁, hu⟩,
    ⟨t₀ ∩ u₀, inter_mem ht₀ hu₀, t₁ ∩ u₁, inter_mem ht₁ hu₁,
      λ x ⟨hx₀, hx₁⟩ x ⟨hy₀, hy₁⟩, ⟨ht _ hx₀ _ hy₀, hu _ hx₁ _ hy₁⟩⟩⟩

/-- `pure x` is the set of sets that contain `x`. It is equal to `𝓟 {x}` but
with this definition we have `s ∈ pure a` defeq `a ∈ s`. -/
instance : has_pure filter :=
⟨λ (α : Type u) x,
  { sets := {s | x ∈ s},
    inter_sets := λ s t, and.intro,
    sets_of_superset := λ s t hs hst, hst hs,
    univ_sets := trivial }⟩

instance : has_bind filter := ⟨@filter.bind⟩

instance : has_seq filter := ⟨@filter.seq⟩

instance : functor filter := { map := @filter.map }

lemma pure_sets (a : α) : (pure a : filter α).sets = {s | a ∈ s} := rfl

@[simp] lemma mem_pure {a : α} {s : set α} : s ∈ (pure a : filter α) ↔ a ∈ s := iff.rfl

@[simp] lemma eventually_pure {a : α} {p : α → Prop} :
  (∀ᶠ x in pure a, p x) ↔ p a :=
iff.rfl

@[simp] lemma principal_singleton (a : α) : 𝓟 {a} = pure a :=
filter.ext $ λ s, by simp only [mem_pure, mem_principal, singleton_subset_iff]

@[simp] lemma map_pure (f : α → β) (a : α) : map f (pure a) = pure (f a) :=
rfl

@[simp] lemma join_pure (f : filter α) : join (pure f) = f := filter.ext $ λ s, iff.rfl

@[simp] lemma pure_bind (a : α) (m : α → filter β) :
  bind (pure a) m = m a :=
by simp only [has_bind.bind, bind, map_pure, join_pure]

section
-- this section needs to be before applicative, otherwise the wrong instance will be chosen
/-- The monad structure on filters. -/
protected def monad : monad filter := { map := @filter.map }

local attribute [instance] filter.monad
protected lemma is_lawful_monad : is_lawful_monad filter :=
{ id_map     := λ α f, filter_eq rfl,
  pure_bind  := λ α β, pure_bind,
  bind_assoc := λ α β γ f m₁ m₂, filter_eq rfl,
  bind_pure_comp_eq_map := λ α β f x, filter.ext $ λ s,
    by simp only [has_bind.bind, bind, functor.map, mem_map', mem_join, mem_set_of_eq,
      comp, mem_pure] }
end

instance : applicative filter := { map := @filter.map, seq := @filter.seq }

instance : alternative filter :=
{ failure := λ α, ⊥,
  orelse  := λ α x y, x ⊔ y }

@[simp] lemma map_def {α β} (m : α → β) (f : filter α) : m <$> f = map m f := rfl

@[simp] lemma bind_def {α β} (f : filter α) (m : α → filter β) : f >>= m = bind f m := rfl

/-! #### `map` and `comap` equations -/
section map
variables {f f₁ f₂ : filter α} {g g₁ g₂ : filter β} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] theorem mem_comap : s ∈ comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s := iff.rfl

theorem preimage_mem_comap (ht : t ∈ g) : m ⁻¹' t ∈ comap m g :=
⟨t, ht, subset.rfl⟩

lemma comap_id : comap id f = f :=
le_antisymm (λ s, preimage_mem_comap) (λ s ⟨t, ht, hst⟩, mem_of_superset ht hst)

lemma comap_const_of_not_mem {x : α} {f : filter α} {V : set α} (hV : V ∈ f) (hx : x ∉ V) :
  comap (λ y : α, x) f = ⊥ :=
begin
  ext W,
  suffices : ∃ t ∈ f, (λ (y : α), x) ⁻¹' t ⊆ W, by simpa,
  use [V, hV],
  simp [preimage_const_of_not_mem hx],
end

lemma comap_const_of_mem {x : α} {f : filter α} (h : ∀ V ∈ f, x ∈ V) : comap (λ y : α, x) f = ⊤ :=
begin
  ext W,
  suffices : (∃ (t : set α), t ∈ f ∧ (λ (y : α), x) ⁻¹' t ⊆ W) ↔ W = univ,
  by simpa,
  split,
  { rintro ⟨V, V_in, hW⟩,
    simpa [preimage_const_of_mem (h V V_in),  univ_subset_iff] using hW },
  { rintro rfl,
    use univ,
    simp [univ_mem] },
end

lemma comap_comap {m : γ → β} {n : β → α} : comap m (comap n f) = comap (n ∘ m) f :=
le_antisymm
  (λ c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_comap hb, h⟩)
  (λ c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from (preimage_mono h₁).trans h₂⟩)

section comm
variables  {δ : Type*}

/-!
The variables in the following lemmas are used as in this diagram:
```
    φ
  α → β
θ ↓   ↓ ψ
  γ → δ
    ρ
```
-/
variables {φ : α → β} {θ : α → γ} {ψ : β → δ} {ρ : γ → δ} (H : ψ ∘ φ = ρ ∘ θ)
include H

lemma map_comm (F : filter α) : map ψ (map φ F) = map ρ (map θ F) :=
by rw [filter.map_map, H, ← filter.map_map]

lemma comap_comm (G : filter δ) : comap φ (comap ψ G) = comap θ (comap ρ G) :=
by rw [filter.comap_comap, H, ← filter.comap_comap]
end comm

@[simp] theorem comap_principal {t : set β} : comap m (𝓟 t) = 𝓟 (m ⁻¹' t) :=
filter.ext $ λ s,
  ⟨λ ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩, (preimage_mono hu).trans b,
    λ h, ⟨t, subset.refl t, h⟩⟩

@[simp] theorem comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b}) :=
by rw [← principal_singleton, comap_principal]

lemma map_le_iff_le_comap : map m f ≤ g ↔ f ≤ comap m g :=
⟨λ h s ⟨t, ht, hts⟩, mem_of_superset (h ht) hts, λ h s ht, h ⟨_, ht, subset.rfl⟩⟩

lemma gc_map_comap (m : α → β) : galois_connection (map m) (comap m) :=
λ f g, map_le_iff_le_comap

@[mono] lemma map_mono : monotone (map m) := (gc_map_comap m).monotone_l
@[mono] lemma comap_mono : monotone (comap m) := (gc_map_comap m).monotone_u

@[simp] lemma map_bot : map m ⊥ = ⊥ := (gc_map_comap m).l_bot
@[simp] lemma map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_comap m).l_sup
@[simp] lemma map_supr {f : ι → filter α} : map m (⨆ i, f i) = (⨆ i, map m (f i)) :=
(gc_map_comap m).l_supr

@[simp] lemma comap_top : comap m ⊤ = ⊤ := (gc_map_comap m).u_top
@[simp] lemma comap_inf : comap m (g₁ ⊓ g₂) = comap m g₁ ⊓ comap m g₂ := (gc_map_comap m).u_inf
@[simp] lemma comap_infi {f : ι → filter β} : comap m (⨅ i, f i) = (⨅ i, comap m (f i)) :=
(gc_map_comap m).u_infi

lemma le_comap_top (f : α → β) (l : filter α) : l ≤ comap f ⊤ :=
by { rw [comap_top], exact le_top }

lemma map_comap_le : map m (comap m g) ≤ g := (gc_map_comap m).l_u_le _
lemma le_comap_map : f ≤ comap m (map m f) := (gc_map_comap m).le_u_l _

@[simp] lemma comap_bot : comap m ⊥ = ⊥ :=
bot_unique $ λ s _, ⟨∅, by simp only [mem_bot], by simp only [empty_subset, preimage_empty]⟩

lemma disjoint_comap (h : disjoint g₁ g₂) : disjoint (comap m g₁) (comap m g₂) :=
by simp only [disjoint_iff, ← comap_inf, h.eq_bot, comap_bot]

lemma comap_supr {ι} {f : ι → filter β} {m : α → β} :
  comap m (supr f) = (⨆ i, comap m (f i)) :=
le_antisymm
  (λ s hs,
    have ∀ i, ∃ t, t ∈ f i ∧ m ⁻¹' t ⊆ s,
      by simpa only [mem_comap, exists_prop, mem_supr] using mem_supr.1 hs,
    let ⟨t, ht⟩ := classical.axiom_of_choice this in
    ⟨⋃ i, t i, mem_supr.2 $ λ i, (f i).sets_of_superset (ht i).1 (subset_Union _ _),
      begin
        rw [preimage_Union, Union_subset_iff],
        exact λ i, (ht i).2
      end⟩)
  (supr_le $ λ i, comap_mono $ le_supr _ _)

lemma comap_Sup {s : set (filter β)} {m : α → β} : comap m (Sup s) = (⨆ f ∈ s, comap m f) :=
by simp only [Sup_eq_supr, comap_supr, eq_self_iff_true]

lemma comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g₂ :=
by rw [sup_eq_supr, comap_supr, supr_bool_eq, bool.cond_tt, bool.cond_ff]

lemma map_comap (f : filter β) (m : α → β) : (f.comap m).map m = f ⊓ 𝓟 (range m) :=
begin
  refine le_antisymm (le_inf map_comap_le $ le_principal_iff.2 range_mem_map) _,
  rintro t' ⟨t, ht, sub⟩,
  refine mem_inf_principal.2 (mem_of_superset ht _),
  rintro _ hxt ⟨x, rfl⟩,
  exact sub hxt
end

lemma map_comap_of_mem {f : filter β} {m : α → β} (hf : range m ∈ f) : (f.comap m).map m = f :=
by rw [map_comap, inf_eq_left.2 (le_principal_iff.2 hf)]

instance [can_lift α β] : can_lift (filter α) (filter β) :=
{ coe := map can_lift.coe,
  cond := λ f, ∀ᶠ x : α in f, can_lift.cond β x,
  prf := λ f hf, ⟨comap can_lift.coe f, map_comap_of_mem $ hf.mono can_lift.prf⟩ }

lemma comap_le_comap_iff {f g : filter β} {m : α → β} (hf : range m ∈ f) :
  comap m f ≤ comap m g ↔ f ≤ g :=
⟨λ h, map_comap_of_mem hf ▸ (map_mono h).trans map_comap_le, λ h, comap_mono h⟩

theorem map_comap_of_surjective {f : α → β} (hf : surjective f) (l : filter β) :
  map f (comap f l) = l :=
map_comap_of_mem $ by simp only [hf.range_eq, univ_mem]

lemma _root_.function.surjective.filter_map_top {f : α → β} (hf : surjective f) : map f ⊤ = ⊤ :=
(congr_arg _ comap_top).symm.trans $ map_comap_of_surjective hf ⊤

lemma subtype_coe_map_comap (s : set α) (f : filter α) :
  map (coe : s → α) (comap (coe : s → α) f) = f ⊓ 𝓟 s :=
by rw [map_comap, subtype.range_coe]

lemma subtype_coe_map_comap_prod (s : set α) (f : filter (α × α)) :
  map (coe : s × s → α × α) (comap (coe : s × s → α × α) f) = f ⊓ 𝓟 (s ×ˢ s) :=
have (coe : s × s → α × α) = (λ x, (x.1, x.2)), by ext ⟨x, y⟩; refl,
by simp [this, map_comap, ← prod_range_range_eq]

lemma image_mem_of_mem_comap {f : filter α} {c : β → α} (h : range c ∈ f) {W : set β}
  (W_in : W ∈ comap c f) : c '' W ∈ f :=
begin
  rw ← map_comap_of_mem h,
  exact image_mem_map W_in
end

lemma image_coe_mem_of_mem_comap {f : filter α} {U : set α} (h : U ∈ f) {W : set U}
  (W_in : W ∈ comap (coe : U → α) f) : coe '' W ∈ f :=
image_mem_of_mem_comap (by simp [h]) W_in

lemma comap_map {f : filter α} {m : α → β} (h : injective m) :
  comap m (map m f) = f :=
le_antisymm
  (λ s hs, mem_of_superset (preimage_mem_comap $ image_mem_map hs) $
    by simp only [preimage_image_eq s h])
  le_comap_map

lemma mem_comap_iff {f : filter β} {m : α → β} (inj : injective m)
  (large : set.range m ∈ f) {S : set α} : S ∈ comap m f ↔ m '' S ∈ f :=
by rw [← image_mem_map_iff inj, map_comap_of_mem large]

lemma le_of_map_le_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀ x ∈ s, ∀ y ∈ s, m x = m y → x = y)
  (h : map m f ≤ map m g) : f ≤ g :=
λ t ht, by filter_upwards [hsf, h $ image_mem_map (inter_mem hsg ht)]
using λ _ has ⟨_, ⟨hbs, hb⟩, h⟩, hm _ hbs _ has h ▸ hb

lemma le_of_map_le_map_inj_iff {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀ x ∈ s, ∀ y ∈ s, m x = m y → x = y) :
  map m f ≤ map m g ↔ f ≤ g :=
iff.intro (le_of_map_le_map_inj' hsf hsg hm) (λ h, map_mono h)

lemma eq_of_map_eq_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f) (hsg : s ∈ g) (hm : ∀ x ∈ s, ∀ y ∈ s, m x = m y → x = y)
  (h : map m f = map m g) : f = g :=
le_antisymm
  (le_of_map_le_map_inj' hsf hsg hm $ le_of_eq h)
  (le_of_map_le_map_inj' hsg hsf hm $ le_of_eq h.symm)

lemma map_inj {f g : filter α} {m : α → β} (hm : injective m) (h : map m f = map m g) :
  f = g :=
have comap m (map m f) = comap m (map m g), by rw h,
by rwa [comap_map hm, comap_map hm] at this

lemma comap_ne_bot_iff {f : filter β} {m : α → β} : ne_bot (comap m f) ↔ ∀ t ∈ f, ∃ a, m a ∈ t :=
begin
  rw ← forall_mem_nonempty_iff_ne_bot,
  exact ⟨λ h t t_in, h (m ⁻¹' t) ⟨t, t_in, subset.rfl⟩,
         λ h s ⟨u, u_in, hu⟩, let ⟨x, hx⟩ := h u u_in in ⟨x, hu hx⟩⟩,
end

lemma comap_ne_bot {f : filter β} {m : α → β} (hm : ∀ t ∈ f, ∃ a, m a ∈ t) : ne_bot (comap m f) :=
comap_ne_bot_iff.mpr hm

lemma comap_ne_bot_iff_frequently {f : filter β} {m : α → β} :
  ne_bot (comap m f) ↔ ∃ᶠ y in f, y ∈ range m :=
by simp [comap_ne_bot_iff, frequently_iff, ← exists_and_distrib_left, and.comm]

lemma comap_ne_bot_iff_compl_range {f : filter β} {m : α → β} :
  ne_bot (comap m f) ↔ (range m)ᶜ ∉ f :=
comap_ne_bot_iff_frequently

lemma ne_bot.comap_of_range_mem {f : filter β} {m : α → β}
  (hf : ne_bot f) (hm : range m ∈ f) : ne_bot (comap m f) :=
comap_ne_bot_iff_frequently.2 $ eventually.frequently hm

@[simp] lemma comap_fst_ne_bot_iff {f : filter α} :
  (f.comap (prod.fst : α × β → α)).ne_bot ↔ f.ne_bot ∧ nonempty β :=
begin
  casesI is_empty_or_nonempty β,
  { rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not]; [simp *, apply_instance] },
  { simp [comap_ne_bot_iff_frequently, h] }
end

@[instance] lemma comap_fst_ne_bot [nonempty β] {f : filter α} [ne_bot f] :
  (f.comap (prod.fst : α × β → α)).ne_bot :=
comap_fst_ne_bot_iff.2 ⟨‹_›, ‹_›⟩

@[simp] lemma comap_snd_ne_bot_iff {f : filter β} :
  (f.comap (prod.snd : α × β → β)).ne_bot ↔ nonempty α ∧ f.ne_bot :=
begin
  casesI is_empty_or_nonempty α with hα hα,
  { rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not];
      [simpa using hα.elim, apply_instance] },
  { simp [comap_ne_bot_iff_frequently, hα] }
end

@[instance] lemma comap_snd_ne_bot [nonempty α] {f : filter β} [ne_bot f] :
  (f.comap (prod.snd : α × β → β)).ne_bot :=
comap_snd_ne_bot_iff.2 ⟨‹_›, ‹_›⟩

lemma comap_eval_ne_bot_iff' {ι : Type*} {α : ι → Type*} {i : ι} {f : filter (α i)} :
  (comap (eval i) f).ne_bot ↔ (∀ j, nonempty (α j)) ∧ ne_bot f :=
begin
  casesI is_empty_or_nonempty (Π j, α j) with H H,
  { rw [filter_eq_bot_of_is_empty (f.comap _), ← not_iff_not]; [skip, assumption],
    simpa [← classical.nonempty_pi] using H.elim },
  { haveI : ∀ j, nonempty (α j), from classical.nonempty_pi.1 H,
    simp [comap_ne_bot_iff_frequently, *] }
end

@[simp] lemma comap_eval_ne_bot_iff {ι : Type*} {α : ι → Type*} [∀ j, nonempty (α j)]
  {i : ι} {f : filter (α i)} :
  (comap (eval i) f).ne_bot ↔ ne_bot f :=
by simp [comap_eval_ne_bot_iff', *]

@[instance] lemma comap_eval_ne_bot {ι : Type*} {α : ι → Type*} [∀ j, nonempty (α j)]
  (i : ι) (f : filter (α i)) [ne_bot f] :
  (comap (eval i) f).ne_bot :=
comap_eval_ne_bot_iff.2 ‹_›

lemma comap_inf_principal_ne_bot_of_image_mem {f : filter β} {m : α → β}
  (hf : ne_bot f) {s : set α} (hs : m '' s ∈ f) :
  ne_bot (comap m f ⊓ 𝓟 s) :=
begin
  refine ⟨compl_compl s ▸ mt mem_of_eq_bot _⟩,
  rintro ⟨t, ht, hts⟩,
  rcases hf.nonempty_of_mem (inter_mem hs ht) with ⟨_, ⟨x, hxs, rfl⟩, hxt⟩,
  exact absurd hxs (hts hxt)
end

lemma comap_coe_ne_bot_of_le_principal {s : set γ} {l : filter γ} [h : ne_bot l] (h' : l ≤ 𝓟 s) :
  ne_bot (comap (coe : s → γ) l) :=
h.comap_of_range_mem $ (@subtype.range_coe γ s).symm ▸ h' (mem_principal_self s)

lemma ne_bot.comap_of_surj {f : filter β} {m : α → β}
  (hf : ne_bot f) (hm : surjective m) :
  ne_bot (comap m f) :=
hf.comap_of_range_mem $ univ_mem' hm

lemma ne_bot.comap_of_image_mem {f : filter β} {m : α → β} (hf : ne_bot f)
  {s : set α} (hs : m '' s ∈ f) :
  ne_bot (comap m f) :=
hf.comap_of_range_mem $ mem_of_superset hs (image_subset_range _ _)

@[simp] lemma map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
⟨by { rw [←empty_mem_iff_bot, ←empty_mem_iff_bot], exact id },
  λ h, by simp only [h, map_bot]⟩

lemma map_ne_bot_iff (f : α → β) {F : filter α} : ne_bot (map f F) ↔ ne_bot F :=
by simp only [ne_bot_iff, ne, map_eq_bot_iff]

lemma ne_bot.map (hf : ne_bot f) (m : α → β) : ne_bot (map m f) :=
(map_ne_bot_iff m).2 hf

instance map_ne_bot [hf : ne_bot f] : ne_bot (f.map m) := hf.map m

lemma sInter_comap_sets (f : α → β) (F : filter β) :
  ⋂₀ (comap f F).sets = ⋂ U ∈ F, f ⁻¹' U :=
begin
  ext x,
  suffices : (∀ (A : set α) (B : set β), B ∈ F → f ⁻¹' B ⊆ A → x ∈ A) ↔
    ∀ (B : set β), B ∈ F → f x ∈ B,
  by simp only [mem_sInter, mem_Inter, filter.mem_sets, mem_comap, this, and_imp,
                exists_prop, mem_preimage, exists_imp_distrib],
  split,
  { intros h U U_in,
    simpa only [subset.refl, forall_prop_of_true, mem_preimage] using h (f ⁻¹' U) U U_in },
  { intros h V U U_in f_U_V,
    exact f_U_V (h U U_in) },
end
end map

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ λ i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → filter α} {m : α → β} (hf : directed (≥) f) [nonempty ι] :
  map m (infi f) = (⨅ i, map m (f i)) :=
map_infi_le.antisymm
  (λ s (hs : preimage m s ∈ infi f),
    let ⟨i, hi⟩ := (mem_infi_of_directed hf _).1 hs in
    have (⨅ i, map m (f i)) ≤ 𝓟 s, from
      infi_le_of_le i $ by { simp only [le_principal_iff, mem_map], assumption },
    filter.le_principal_iff.1 this)

lemma map_binfi_eq {ι : Type w} {f : ι → filter α} {m : α → β} {p : ι → Prop}
  (h : directed_on (f ⁻¹'o (≥)) {x | p x}) (ne : ∃ i, p i) :
  map m (⨅ i (h : p i), f i) = (⨅ i (h : p i), map m (f i)) :=
begin
  haveI := nonempty_subtype.2 ne,
  simp only [infi_subtype'],
  exact map_infi_eq h.directed_coe
end

lemma map_inf_le {f g : filter α} {m : α → β} : map m (f ⊓ g) ≤ map m f ⊓ map m g :=
(@map_mono _ _ m).map_inf_le f g

lemma map_inf {f g : filter α} {m : α → β} (h : injective m) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
begin
  refine map_inf_le.antisymm _,
  rintro t ⟨s₁, hs₁, s₂, hs₂, ht : m ⁻¹' t = s₁ ∩ s₂⟩,
  refine mem_inf_of_inter (image_mem_map hs₁) (image_mem_map hs₂) _,
  rw [image_inter h, image_subset_iff, ht]
end

lemma map_inf' {f g : filter α} {m : α → β} {t : set α} (htf : t ∈ f) (htg : t ∈ g)
  (h : inj_on m t) : map m (f ⊓ g) = map m f ⊓ map m g :=
begin
  lift f to filter t using htf, lift g to filter t using htg,
  replace h : injective (m ∘ coe) := h.injective,
  simp only [map_map, ← map_inf subtype.coe_injective, map_inf h],
end

lemma disjoint_map {m : α → β} (hm : injective m) {f₁ f₂ : filter α} :
  disjoint (map m f₁) (map m f₂) ↔ disjoint f₁ f₂ :=
by simp only [disjoint_iff, ← map_inf hm, map_eq_bot_iff]

lemma map_eq_comap_of_inverse {f : filter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = comap n f :=
le_antisymm
  (λ b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f.sets_of_superset ha $
    calc a = preimage (n ∘ m) a : by simp only [h₂, preimage_id, eq_self_iff_true]
      ... ⊆ preimage m b : preimage_mono h)
  (λ b (hb : preimage m b ∈ f),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp only [h₁]; apply subset.refl⟩)

lemma map_swap_eq_comap_swap {f : filter (α × β)} : prod.swap <$> f = comap prod.swap f :=
map_eq_comap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

lemma le_map {f : filter α} {m : α → β} {g : filter β} (h : ∀ s ∈ f, m '' s ∈ g) :
  g ≤ f.map m :=
λ s hs, mem_of_superset (h _ hs) $ image_preimage_subset _ _

protected lemma push_pull (f : α → β) (F : filter α) (G : filter β) :
  map f (F ⊓ comap f G) = map f F ⊓ G :=
begin
  apply le_antisymm,
  { calc map f (F ⊓ comap f G) ≤ map f F ⊓ (map f $ comap f G) : map_inf_le
      ... ≤ map f F ⊓ G : inf_le_inf_left (map f F) map_comap_le },
  { rintro U ⟨V, V_in, W, ⟨Z, Z_in, hZ⟩, h⟩,
    apply mem_inf_of_inter (image_mem_map V_in) Z_in,
    calc
      f '' V ∩ Z = f '' (V ∩ f ⁻¹' Z) : by rw image_inter_preimage
             ... ⊆ f '' (V ∩ W) :  image_subset _ (inter_subset_inter_right _ ‹_›)
             ... = f '' (f ⁻¹' U) : by rw h
             ... ⊆ U : image_preimage_subset f U }
end

protected lemma push_pull' (f : α → β) (F : filter α) (G : filter β) :
  map f (comap f G ⊓ F) = G ⊓ map f F :=
by simp only [filter.push_pull, inf_comm]

section applicative

lemma singleton_mem_pure {a : α} : {a} ∈ (pure a : filter α) :=
mem_singleton a

lemma pure_injective : injective (pure : α → filter α) :=
λ a b hab, (filter.ext_iff.1 hab {x | a = x}).1 rfl

instance pure_ne_bot {α : Type u} {a : α} : ne_bot (pure a) :=
⟨mt empty_mem_iff_bot.2 $ not_mem_empty a⟩

@[simp] lemma le_pure_iff {f : filter α} {a : α} : f ≤ pure a ↔ {a} ∈ f :=
⟨λ h, h singleton_mem_pure,
  λ h s hs, mem_of_superset h $ singleton_subset_iff.2 hs⟩

lemma mem_seq_def {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ f.seq g ↔ (∃ u ∈ f, ∃ t ∈ g, ∀ x ∈ u, ∀ y ∈ t, (x : α → β) y ∈ s) :=
iff.rfl

lemma mem_seq_iff {f : filter (α → β)} {g : filter α} {s : set β} :
  s ∈ f.seq g ↔ (∃ u ∈ f, ∃ t ∈ g, set.seq u t ⊆ s) :=
by simp only [mem_seq_def, seq_subset, exists_prop, iff_self]

lemma mem_map_seq_iff {f : filter α} {g : filter β} {m : α → β → γ} {s : set γ} :
  s ∈ (f.map m).seq g ↔ (∃ t u, t ∈ g ∧ u ∈ f ∧ ∀ x ∈ u, ∀ y ∈ t, m x y ∈ s) :=
iff.intro
  (λ ⟨t, ht, s, hs, hts⟩, ⟨s, m ⁻¹' t, hs, ht, λ a, hts _⟩)
  (λ ⟨t, s, ht, hs, hts⟩, ⟨m '' s, image_mem_map hs, t, ht, λ f ⟨a, has, eq⟩, eq ▸ hts _ has⟩)

lemma seq_mem_seq {f : filter (α → β)} {g : filter α} {s : set (α → β)} {t : set α}
  (hs : s ∈ f) (ht : t ∈ g) : s.seq t ∈ f.seq g :=
⟨s, hs, t, ht, λ f hf a ha, ⟨f, hf, a, ha, rfl⟩⟩

lemma le_seq {f : filter (α → β)} {g : filter α} {h : filter β}
  (hh : ∀ t ∈ f, ∀ u ∈ g, set.seq t u ∈ h) : h ≤ seq f g :=
λ s ⟨t, ht, u, hu, hs⟩, mem_of_superset (hh _ ht _ hu) $
  λ b ⟨m, hm, a, ha, eq⟩, eq ▸ hs _ hm _ ha

@[mono] lemma seq_mono {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.seq g₁ ≤ f₂.seq g₂ :=
le_seq $ λ s hs t ht, seq_mem_seq (hf hs) (hg ht)

@[simp] lemma pure_seq_eq_map (g : α → β) (f : filter α) : seq (pure g) f = f.map g :=
begin
  refine le_antisymm (le_map $ λ s hs, _) (le_seq $ λ s hs t ht, _),
  { rw ← singleton_seq, apply seq_mem_seq _ hs,
    exact singleton_mem_pure },
  { refine sets_of_superset (map g f) (image_mem_map ht) _,
    rintro b ⟨a, ha, rfl⟩, exact ⟨g, hs, a, ha, rfl⟩ }
end

@[simp] lemma seq_pure (f : filter (α → β)) (a : α) : seq f (pure a) = map (λ g : α → β, g a) f :=
begin
  refine le_antisymm (le_map $ λ s hs, _) (le_seq $ λ s hs t ht, _),
  { rw ← seq_singleton,
    exact seq_mem_seq hs singleton_mem_pure },
  { refine sets_of_superset (map (λg:α→β, g a) f) (image_mem_map hs) _,
    rintro b ⟨g, hg, rfl⟩, exact ⟨g, hg, a, ht, rfl⟩ }
end

@[simp] lemma seq_assoc (x : filter α) (g : filter (α → β)) (h : filter (β → γ)) :
  seq h (seq g x) = seq (seq (map (∘) h) g) x :=
begin
  refine le_antisymm (le_seq $ λ s hs t ht, _) (le_seq $ λ s hs t ht, _),
  { rcases mem_seq_iff.1 hs with ⟨u, hu, v, hv, hs⟩,
    rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hu⟩,
    refine mem_of_superset _
      (set.seq_mono ((set.seq_mono hu subset.rfl).trans hs) subset.rfl),
    rw ← set.seq_seq,
    exact seq_mem_seq hw (seq_mem_seq hv ht) },
  { rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
    refine mem_of_superset _ (set.seq_mono subset.rfl ht),
    rw set.seq_seq,
    exact seq_mem_seq (seq_mem_seq (image_mem_map hs) hu) hv }
end

lemma prod_map_seq_comm (f : filter α) (g : filter β) :
  (map prod.mk f).seq g = seq (map (λ b a, (a, b)) g) f :=
begin
  refine le_antisymm (le_seq $ λ s hs t ht, _) (le_seq $ λ s hs t ht, _),
  { rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩,
    refine mem_of_superset _ (set.seq_mono hs subset.rfl),
    rw ← set.prod_image_seq_comm,
    exact seq_mem_seq (image_mem_map ht) hu },
  { rcases mem_map_iff_exists_image.1 hs with ⟨u, hu, hs⟩,
    refine mem_of_superset _ (set.seq_mono hs subset.rfl),
    rw set.prod_image_seq_comm,
    exact seq_mem_seq (image_mem_map ht) hu }
end

instance : is_lawful_functor (filter : Type u → Type u) :=
{ id_map   := λ α f, map_id,
  comp_map := λ α β γ f g a, map_map.symm }

instance : is_lawful_applicative (filter : Type u → Type u) :=
{ pure_seq_eq_map := λ α β, pure_seq_eq_map,
  map_pure        := λ α β, map_pure,
  seq_pure        := λ α β, seq_pure,
  seq_assoc       := λ α β γ, seq_assoc }

instance : is_comm_applicative (filter : Type u → Type u) :=
⟨λ α β f g, prod_map_seq_comm f g⟩

lemma {l} seq_eq_filter_seq {α β : Type l} (f : filter (α → β)) (g : filter α) :
  f <*> g = seq f g := rfl

end applicative

/-! #### `bind` equations -/
section bind

@[simp] lemma eventually_bind {f : filter α} {m : α → filter β} {p : β → Prop} :
  (∀ᶠ y in bind f m, p y) ↔ ∀ᶠ x in f, ∀ᶠ y in m x, p y :=
iff.rfl

@[simp] lemma eventually_eq_bind {f : filter α} {m : α → filter β} {g₁ g₂ : β → γ} :
  (g₁ =ᶠ[bind f m] g₂) ↔ ∀ᶠ x in f, g₁ =ᶠ[m x] g₂ :=
iff.rfl

@[simp] lemma eventually_le_bind [has_le γ] {f : filter α} {m : α → filter β} {g₁ g₂ : β → γ} :
  (g₁ ≤ᶠ[bind f m] g₂) ↔ ∀ᶠ x in f, g₁ ≤ᶠ[m x] g₂ :=
iff.rfl

lemma mem_bind' {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ bind f m ↔ {a | s ∈ m a} ∈ f :=
iff.rfl

@[simp] lemma mem_bind {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ bind f m ↔ ∃ t ∈ f, ∀ x ∈ t, s ∈ m x :=
calc s ∈ bind f m ↔ {a | s ∈ m a} ∈ f           : iff.rfl
              ... ↔ (∃ t ∈ f, t ⊆ {a | s ∈ m a}) : exists_mem_subset_iff.symm
              ... ↔ (∃ t ∈ f, ∀ x ∈ t, s ∈ m x)   : iff.rfl

lemma bind_le {f : filter α} {g : α → filter β} {l : filter β} (h : ∀ᶠ x in f, g x ≤ l) :
  f.bind g ≤ l :=
join_le $ eventually_map.2 h

@[mono] lemma bind_mono {f₁ f₂ : filter α} {g₁ g₂ : α → filter β} (hf : f₁ ≤ f₂)
  (hg : g₁ ≤ᶠ[f₁] g₂) :
  bind f₁ g₁ ≤ bind f₂ g₂ :=
begin
  refine le_trans (λ s hs, _) (join_mono $ map_mono hf),
  simp only [mem_join, mem_bind', mem_map] at hs ⊢,
  filter_upwards [hg, hs] with _ hx hs using hx hs,
end

lemma bind_inf_principal {f : filter α} {g : α → filter β} {s : set β} :
  f.bind (λ x, g x ⊓ 𝓟 s) = (f.bind g) ⊓ 𝓟 s :=
filter.ext $ λ s, by simp only [mem_bind, mem_inf_principal]

lemma sup_bind {f g : filter α} {h : α → filter β} :
  bind (f ⊔ g) h = bind f h ⊔ bind g h :=
by simp only [bind, sup_join, map_sup, eq_self_iff_true]

lemma principal_bind {s : set α} {f : α → filter β} :
  (bind (𝓟 s) f) = (⨆ x ∈ s, f x) :=
show join (map f (𝓟 s)) = (⨆ x ∈ s, f x),
  by simp only [Sup_image, join_principal_eq_Sup, map_principal, eq_self_iff_true]

end bind

section list_traverse
/- This is a separate section in order to open `list`, but mostly because of universe
   equality requirements in `traverse` -/

open list

lemma sequence_mono :
  ∀ (as bs : list (filter α)), forall₂ (≤) as bs → sequence as ≤ sequence bs
| []        []        forall₂.nil         := le_rfl
| (a :: as) (b :: bs) (forall₂.cons h hs) := seq_mono (map_mono h) (sequence_mono as bs hs)

variables {α' β' γ' : Type u} {f : β' → filter α'} {s : γ' → set α'}

lemma mem_traverse :
  ∀ (fs : list β') (us : list γ'),
    forall₂ (λ b c, s c ∈ f b) fs us → traverse s us ∈ traverse f fs
| []        []        forall₂.nil         := mem_pure.2 $ mem_singleton _
| (f :: fs) (u :: us) (forall₂.cons h hs) := seq_mem_seq (image_mem_map h) (mem_traverse fs us hs)

lemma mem_traverse_iff (fs : list β') (t : set (list α')) :
  t ∈ traverse f fs ↔
    (∃ us : list (set α'), forall₂ (λ b (s : set α'), s ∈ f b) fs us ∧ sequence us ⊆ t) :=
begin
  split,
  { induction fs generalizing t,
    case nil { simp only [sequence, mem_pure, imp_self, forall₂_nil_left_iff,
      exists_eq_left, set.pure_def, singleton_subset_iff, traverse_nil] },
    case cons : b fs ih t
    { intro ht,
      rcases mem_seq_iff.1 ht with ⟨u, hu, v, hv, ht⟩,
      rcases mem_map_iff_exists_image.1 hu with ⟨w, hw, hwu⟩,
      rcases ih v hv with ⟨us, hus, hu⟩,
      exact ⟨w :: us, forall₂.cons hw hus, (set.seq_mono hwu hu).trans ht⟩ } },
  { rintro ⟨us, hus, hs⟩,
    exact mem_of_superset (mem_traverse _ _ hus) hs }
end

end list_traverse

/-! ### Limits -/

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto (f : α → β) (l₁ : filter α) (l₂ : filter β) := l₁.map f ≤ l₂

lemma tendsto_def {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ ∀ s ∈ l₂, f ⁻¹' s ∈ l₁ := iff.rfl

lemma tendsto_iff_eventually {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ ∀ ⦃p : β → Prop⦄, (∀ᶠ y in l₂, p y) → ∀ᶠ x in l₁, p (f x) :=
iff.rfl

lemma tendsto.eventually {f : α → β} {l₁ : filter α} {l₂ : filter β} {p : β → Prop}
  (hf : tendsto f l₁ l₂) (h : ∀ᶠ y in l₂, p y) :
  ∀ᶠ x in l₁, p (f x) :=
hf h

lemma tendsto.frequently {f : α → β} {l₁ : filter α} {l₂ : filter β} {p : β → Prop}
  (hf : tendsto f l₁ l₂) (h : ∃ᶠ x in l₁, p (f x)) :
  ∃ᶠ y in l₂, p y :=
mt hf.eventually h

lemma tendsto.frequently_map {l₁ : filter α} {l₂ : filter β} {p : α → Prop} {q : β → Prop}
  (f : α → β) (c : filter.tendsto f l₁ l₂) (w : ∀ x, p x → q (f x)) (h : ∃ᶠ x in l₁, p x) :
  ∃ᶠ y in l₂, q y :=
c.frequently (h.mono w)

@[simp] lemma tendsto_bot {f : α → β} {l : filter β} : tendsto f ⊥ l := by simp [tendsto]
@[simp] lemma tendsto_top {f : α → β} {l : filter α} : tendsto f l ⊤ := le_top

lemma le_map_of_right_inverse {mab : α → β} {mba : β → α} {f : filter α} {g : filter β}
  (h₁ : mab ∘ mba =ᶠ[g] id) (h₂ : tendsto mba g f) :
  g ≤ map mab f :=
by { rw [← @map_id _ g, ← map_congr h₁, ← map_map], exact map_mono h₂ }

lemma tendsto_of_is_empty [is_empty α] {f : α → β} {la : filter α} {lb : filter β} :
  tendsto f la lb :=
by simp only [filter_eq_bot_of_is_empty la, tendsto_bot]

lemma eventually_eq_of_left_inv_of_right_inv {f : α → β} {g₁ g₂ : β → α} {fa : filter α}
  {fb : filter β} (hleft : ∀ᶠ x in fa, g₁ (f x) = x) (hright : ∀ᶠ y in fb, f (g₂ y) = y)
  (htendsto : tendsto g₂ fb fa) :
  g₁ =ᶠ[fb] g₂ :=
(htendsto.eventually hleft).mp $ hright.mono $ λ y hr hl, (congr_arg g₁ hr.symm).trans hl

lemma tendsto_iff_comap {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ l₁ ≤ l₂.comap f :=
map_le_iff_le_comap

alias tendsto_iff_comap ↔ filter.tendsto.le_comap _

protected lemma tendsto.disjoint {f : α → β} {la₁ la₂ : filter α} {lb₁ lb₂ : filter β}
  (h₁ : tendsto f la₁ lb₁) (hd : disjoint lb₁ lb₂) (h₂ : tendsto f la₂ lb₂) :
  disjoint la₁ la₂ :=
(disjoint_comap hd).mono h₁.le_comap h₂.le_comap

lemma tendsto_congr' {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β} (hl : f₁ =ᶠ[l₁] f₂) :
  tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂ :=
by rw [tendsto, tendsto, map_congr hl]

lemma tendsto.congr' {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (hl : f₁ =ᶠ[l₁] f₂) (h : tendsto f₁ l₁ l₂) : tendsto f₂ l₁ l₂ :=
(tendsto_congr' hl).1 h

theorem tendsto_congr {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : ∀ x, f₁ x = f₂ x) : tendsto f₁ l₁ l₂ ↔ tendsto f₂ l₁ l₂ :=
tendsto_congr' (univ_mem' h)

theorem tendsto.congr {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : ∀ x, f₁ x = f₂ x) : tendsto f₁ l₁ l₂ → tendsto f₂ l₁ l₂ :=
(tendsto_congr h).1

lemma tendsto_id' {x y : filter α} : x ≤ y → tendsto id x y :=
by simp only [tendsto, map_id, forall_true_iff] {contextual := tt}

lemma tendsto_id {x : filter α} : tendsto id x x := tendsto_id' $ le_refl x

lemma tendsto.comp {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ}
  (hg : tendsto g y z) (hf : tendsto f x y) : tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma tendsto.mono_left {f : α → β} {x y : filter α} {z : filter β}
  (hx : tendsto f x z) (h : y ≤ x) : tendsto f y z :=
(map_mono h).trans hx

lemma tendsto.mono_right {f : α → β} {x : filter α} {y z : filter β}
  (hy : tendsto f x y) (hz : y ≤ z) : tendsto f x z :=
le_trans hy hz

lemma tendsto.ne_bot {f : α → β} {x : filter α} {y : filter β} (h : tendsto f x y) [hx : ne_bot x] :
  ne_bot y :=
(hx.map _).mono h

lemma tendsto_map {f : α → β} {x : filter α} : tendsto f x (map f x) := le_refl (map f x)

lemma tendsto_map' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
by rwa [tendsto, map_map]

@[simp] lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by { rw [tendsto, map_map], refl }

lemma tendsto_comap {f : α → β} {x : filter β} : tendsto f (comap f x) x :=
map_comap_le

@[simp] lemma tendsto_comap_iff {f : α → β} {g : β → γ} {a : filter α} {c : filter γ} :
  tendsto f a (c.comap g) ↔ tendsto (g ∘ f) a c :=
⟨λ h, tendsto_comap.comp h, λ h, map_le_iff_le_comap.mp $ by rwa [map_map]⟩

lemma tendsto_comap'_iff {m : α → β} {f : filter α} {g : filter β} {i : γ → α}
  (h : range i ∈ f) : tendsto (m ∘ i) (comap i f) g ↔ tendsto m f g :=
by { rw [tendsto, ← map_compose], simp only [(∘), map_comap_of_mem h, tendsto] }

lemma tendsto.of_tendsto_comp {f : α → β} {g : β → γ} {a : filter α} {b : filter β} {c : filter γ}
  (hfg : tendsto (g ∘ f) a c) (hg : comap g c ≤ b) :
  tendsto f a b :=
begin
  rw tendsto_iff_comap at hfg ⊢,
  calc a ≤ comap (g ∘ f) c : hfg
  ... ≤ comap f b : by simpa [comap_comap] using comap_mono hg
end

lemma comap_eq_of_inverse {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α)
  (eq : ψ ∘ φ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : comap φ g = f :=
begin
  refine ((comap_mono $ map_le_iff_le_comap.1 hψ).trans _).antisymm (map_le_iff_le_comap.1 hφ),
  rw [comap_comap, eq, comap_id],
  exact le_rfl
end

lemma map_eq_of_inverse {f : filter α} {g : filter β} {φ : α → β} (ψ : β → α)
  (eq : φ ∘ ψ = id) (hφ : tendsto φ f g) (hψ : tendsto ψ g f) : map φ f = g :=
begin
  refine le_antisymm hφ (le_trans _ (map_mono hψ)),
  rw [map_map, eq, map_id],
  exact le_rfl
end

lemma tendsto_inf {f : α → β} {x : filter α} {y₁ y₂ : filter β} :
  tendsto f x (y₁ ⊓ y₂) ↔ tendsto f x y₁ ∧ tendsto f x y₂ :=
by simp only [tendsto, le_inf_iff, iff_self]

lemma tendsto_inf_left {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_left) h

lemma tendsto_inf_right {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₂ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_right) h

lemma tendsto.inf {f : α → β} {x₁ x₂ : filter α} {y₁ y₂ : filter β}
  (h₁ : tendsto f x₁ y₁) (h₂ : tendsto f x₂ y₂) : tendsto f (x₁ ⊓ x₂) (y₁ ⊓ y₂) :=
tendsto_inf.2 ⟨tendsto_inf_left h₁, tendsto_inf_right h₂⟩

@[simp] lemma tendsto_infi {f : α → β} {x : filter α} {y : ι → filter β} :
  tendsto f x (⨅ i, y i) ↔ ∀ i, tendsto f x (y i) :=
by simp only [tendsto, iff_self, le_infi_iff]

lemma tendsto_infi' {f : α → β} {x : ι → filter α} {y : filter β} (i : ι) (hi : tendsto f (x i) y) :
  tendsto f (⨅ i, x i) y :=
hi.mono_left $ infi_le _ _

@[simp] lemma tendsto_sup {f : α → β} {x₁ x₂ : filter α} {y : filter β} :
  tendsto f (x₁ ⊔ x₂) y ↔ tendsto f x₁ y ∧ tendsto f x₂ y :=
by simp only [tendsto, map_sup, sup_le_iff]

lemma tendsto.sup {f : α → β} {x₁ x₂ : filter α} {y : filter β} :
  tendsto f x₁ y → tendsto f x₂ y → tendsto f (x₁ ⊔ x₂) y :=
λ h₁ h₂, tendsto_sup.mpr ⟨ h₁, h₂ ⟩

@[simp] lemma tendsto_supr {f : α → β} {x : ι → filter α} {y : filter β} :
  tendsto f (⨆ i, x i) y ↔ ∀ i, tendsto f (x i) y :=
by simp only [tendsto, map_supr, supr_le_iff]

@[simp] lemma tendsto_principal {f : α → β} {l : filter α} {s : set β} :
  tendsto f l (𝓟 s) ↔ ∀ᶠ a in l, f a ∈ s :=
by simp only [tendsto, le_principal_iff, mem_map', filter.eventually]

@[simp] lemma tendsto_principal_principal {f : α → β} {s : set α} {t : set β} :
  tendsto f (𝓟 s) (𝓟 t) ↔ ∀ a ∈ s, f a ∈ t :=
by simp only [tendsto_principal, eventually_principal]

@[simp] lemma tendsto_pure {f : α → β} {a : filter α} {b : β} :
  tendsto f a (pure b) ↔ ∀ᶠ x in a, f x = b :=
by simp only [tendsto, le_pure_iff, mem_map', mem_singleton_iff, filter.eventually]

lemma tendsto_pure_pure (f : α → β) (a : α) :
  tendsto f (pure a) (pure (f a)) :=
tendsto_pure.2 rfl

lemma tendsto_const_pure {a : filter α} {b : β} : tendsto (λ x, b) a (pure b) :=
tendsto_pure.2 $ univ_mem' $ λ _, rfl

lemma pure_le_iff {a : α} {l : filter α} : pure a ≤ l ↔ ∀ s ∈ l, a ∈ s :=
iff.rfl

lemma tendsto_pure_left {f : α → β} {a : α} {l : filter β} :
  tendsto f (pure a) l ↔ ∀ s ∈ l, f a ∈ s :=
iff.rfl

@[simp] lemma map_inf_principal_preimage {f : α → β} {s : set β} {l : filter α} :
  map f (l ⊓ 𝓟 (f ⁻¹' s)) = map f l ⊓ 𝓟 s :=
filter.ext $ λ t, by simp only [mem_map', mem_inf_principal, mem_set_of_eq, mem_preimage]

/-- If two filters are disjoint, then a function cannot tend to both of them along a non-trivial
filter. -/
lemma tendsto.not_tendsto {f : α → β} {a : filter α} {b₁ b₂ : filter β} (hf : tendsto f a b₁)
  [ne_bot a] (hb : disjoint b₁ b₂) :
  ¬ tendsto f a b₂ :=
λ hf', (tendsto_inf.2 ⟨hf, hf'⟩).ne_bot.ne hb.eq_bot

lemma tendsto.if {l₁ : filter α} {l₂ : filter β} {f g : α → β} {p : α → Prop} [∀ x, decidable (p x)]
  (h₀ : tendsto f (l₁ ⊓ 𝓟 {x | p x}) l₂) (h₁ : tendsto g (l₁ ⊓ 𝓟 { x | ¬ p x }) l₂) :
  tendsto (λ x, if p x then f x else g x) l₁ l₂ :=
begin
  simp only [tendsto_def, mem_inf_principal] at *,
  intros s hs,
  filter_upwards [h₀ s hs, h₁ s hs],
  simp only [mem_preimage],
  intros x hp₀ hp₁,
  split_ifs,
  exacts [hp₀ h, hp₁ h],
end

lemma tendsto.piecewise {l₁ : filter α} {l₂ : filter β} {f g : α → β}
  {s : set α} [∀ x, decidable (x ∈ s)]
  (h₀ : tendsto f (l₁ ⊓ 𝓟 s) l₂) (h₁ : tendsto g (l₁ ⊓ 𝓟 sᶜ) l₂) :
  tendsto (piecewise s f g) l₁ l₂ :=
h₀.if h₁

/-! ### Products of filters -/

section prod
variables {s : set α} {t : set β} {f : filter α} {g : filter β}
/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x ← seq, y ← top, return (x, y)}
  hence:
    s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s

  G := do {y ← top, x ← seq, return (x, y)}
  hence:
    s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s

  Now ⋃ i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/

/-- Product of filters. This is the filter generated by cartesian products
  of elements of the component filters. -/
protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊓ g.comap prod.snd

localized "infix ` ×ᶠ `:60 := filter.prod" in filter

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f) (ht : t ∈ g) : s ×ˢ t ∈ f ×ᶠ g :=
inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ f ×ᶠ g ↔ (∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s) :=
begin
  simp only [filter.prod],
  split,
  { rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩,
    exact  ⟨s₁, hs₁, s₂, hs₂, λ p ⟨h, h'⟩, ⟨hts₁ h, hts₂ h'⟩⟩ },
  { rintro ⟨t₁, ht₁, t₂, ht₂, h⟩,
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h }
end

@[simp] lemma prod_mem_prod_iff {s : set α} {t : set β} {f : filter α} {g : filter β}
  [f.ne_bot] [g.ne_bot] :
  s ×ˢ t ∈ f ×ᶠ g ↔ s ∈ f ∧ t ∈ g :=
⟨λ h, let ⟨s', hs', t', ht', H⟩ := mem_prod_iff.1 h in (prod_subset_prod_iff.1 H).elim
  (λ ⟨hs's, ht't⟩, ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩)
  (λ h, h.elim
    (λ hs'e, absurd hs'e (nonempty_of_mem hs').ne_empty)
    (λ ht'e, absurd ht'e (nonempty_of_mem ht').ne_empty)),
  λ h, prod_mem_prod h.1 h.2⟩

lemma mem_prod_principal {f : filter α} {s : set (α × β)} {t : set β}:
  s ∈ f ×ᶠ 𝓟 t ↔ {a | ∀ b ∈ t, (a, b) ∈ s} ∈ f :=
begin
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff],
  refine exists₂_congr (λ u u_in, ⟨_, λ h, ⟨t, mem_principal_self t, _⟩⟩),
  { rintros ⟨v, v_in, hv⟩ a a_in b b_in,
    exact hv (mk_mem_prod a_in $ v_in b_in) },
  { rintro ⟨x, y⟩ ⟨hx, hy⟩,
    exact h hx y hy }
end

lemma mem_prod_top {f : filter α} {s : set (α × β)} :
  s ∈ f ×ᶠ (⊤ : filter β) ↔ {a | ∀ b, (a, b) ∈ s} ∈ f :=
begin
  rw [← principal_univ, mem_prod_principal],
  simp only [mem_univ, forall_true_left]
end

lemma comap_prod (f : α → β × γ) (b : filter β) (c : filter γ) :
  comap f (b ×ᶠ c) = (comap (prod.fst ∘ f) b) ⊓ (comap (prod.snd ∘ f) c) :=
by erw [comap_inf, filter.comap_comap, filter.comap_comap]

lemma prod_top {f : filter α} : f ×ᶠ (⊤ : filter β) = f.comap prod.fst :=
by rw [filter.prod, comap_top, inf_top_eq]

lemma sup_prod (f₁ f₂ : filter α) (g : filter β) : (f₁ ⊔ f₂) ×ᶠ g = (f₁ ×ᶠ g) ⊔ (f₂ ×ᶠ g) :=
by rw [filter.prod, comap_sup, inf_sup_right, ← filter.prod, ← filter.prod]

lemma prod_sup (f : filter α) (g₁ g₂ : filter β) : f ×ᶠ (g₁ ⊔ g₂) = (f ×ᶠ g₁) ⊔ (f ×ᶠ g₂) :=
by rw [filter.prod, comap_sup, inf_sup_left, ← filter.prod, ← filter.prod]

lemma eventually_prod_iff {p : α × β → Prop} {f : filter α} {g : filter β} :
  (∀ᶠ x in f ×ᶠ g, p x) ↔ ∃ (pa : α → Prop) (ha : ∀ᶠ x in f, pa x)
    (pb : β → Prop) (hb : ∀ᶠ y in g, pb y), ∀ {x}, pa x → ∀ {y}, pb y → p (x, y) :=
by simpa only [set.prod_subset_iff] using @mem_prod_iff α β p f g

lemma tendsto_fst {f : filter α} {g : filter β} : tendsto prod.fst (f ×ᶠ g) f :=
tendsto_inf_left tendsto_comap

lemma tendsto_snd {f : filter α} {g : filter β} : tendsto prod.snd (f ×ᶠ g) g :=
tendsto_inf_right tendsto_comap

lemma tendsto.prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λ x, (m₁ x, m₂ x)) f (g ×ᶠ h) :=
tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

lemma eventually.prod_inl {la : filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : filter β) :
  ∀ᶠ x in la ×ᶠ lb, p (x : α × β).1 :=
tendsto_fst.eventually h

lemma eventually.prod_inr {lb : filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : filter α) :
  ∀ᶠ x in la ×ᶠ lb, p (x : α × β).2 :=
tendsto_snd.eventually h

lemma eventually.prod_mk {la : filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x)
  {lb : filter β} {pb : β → Prop} (hb : ∀ᶠ y in lb, pb y) :
  ∀ᶠ p in la ×ᶠ lb, pa (p : α × β).1 ∧ pb p.2 :=
(ha.prod_inl lb).and (hb.prod_inr la)

lemma eventually.curry {la : filter α} {lb : filter β} {p : α × β → Prop}
  (h : ∀ᶠ x in la ×ᶠ lb, p x) :
  ∀ᶠ x in la, ∀ᶠ y in lb, p (x, y) :=
begin
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩,
  exact ha.mono (λ a ha, hb.mono $ λ b hb, h ha hb)
end

lemma prod_infi_left [nonempty ι] {f : ι → filter α} {g : filter β}:
  (⨅ i, f i) ×ᶠ g = (⨅ i, (f i) ×ᶠ g) :=
by { rw [filter.prod, comap_infi, infi_inf], simp only [filter.prod, eq_self_iff_true] }

lemma prod_infi_right [nonempty ι] {f : filter α} {g : ι → filter β} :
  f ×ᶠ (⨅ i, g i) = (⨅ i, f ×ᶠ (g i)) :=
by { rw [filter.prod, comap_infi, inf_infi], simp only [filter.prod, eq_self_iff_true] }

@[mono] lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁ ×ᶠ g₁ ≤ f₂ ×ᶠ g₂ :=
inf_le_inf (comap_mono hf) (comap_mono hg)

lemma prod_comap_comap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  (comap m₁ f₁) ×ᶠ (comap m₂ f₂) = comap (λ p : β₁×β₂, (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
by simp only [filter.prod, comap_comap, eq_self_iff_true, comap_inf]

lemma prod_comm' : f ×ᶠ g = comap (prod.swap) (g ×ᶠ f) :=
by simp only [filter.prod, comap_comap, (∘), inf_comm, prod.fst_swap,
  eq_self_iff_true, prod.snd_swap, comap_inf]

lemma prod_comm : f ×ᶠ g = map (λ p : β×α, (p.2, p.1)) (g ×ᶠ f) :=
by { rw [prod_comm', ← map_swap_eq_comap_swap], refl }

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  (map m₁ f₁) ×ᶠ (map m₂ f₂) = map (λ p : α₁×α₂, (m₁ p.1, m₂ p.2)) (f₁ ×ᶠ f₂) :=
le_antisymm
  (λ s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc m₁ '' s₁ ×ˢ m₂ '' s₂ = (λ p : α₁×α₂, (m₁ p.1, m₂ p.2)) '' (s₁ ×ˢ s₂) :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  ((tendsto.comp le_rfl tendsto_fst).prod_mk (tendsto.comp le_rfl tendsto_snd))

lemma prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) (F : filter α₁) (G : filter β₁) :
  (map f F) ×ᶠ (map g G) = map (prod.map f g) (F ×ᶠ G) :=
prod_map_map_eq

lemma le_prod_map_fst_snd {f : filter (α × β)} : f ≤ map prod.fst f ×ᶠ map prod.snd f :=
le_inf le_comap_map le_comap_map

lemma tendsto.prod_map {δ : Type*} {f : α → γ} {g : β → δ} {a : filter α} {b : filter β}
  {c : filter γ} {d : filter δ} (hf : tendsto f a c) (hg : tendsto g b d) :
  tendsto (prod.map f g) (a ×ᶠ b) (c ×ᶠ d) :=
begin
  erw [tendsto, ← prod_map_map_eq],
  exact filter.prod_mono hf hg,
end

lemma map_prod (m : α × β → γ) (f : filter α) (g : filter β) :
  map m (f ×ᶠ g) = (f.map (λ a b, m (a, b))).seq g :=
begin
  simp [filter.ext_iff, mem_prod_iff, mem_map_seq_iff],
  intro s,
  split,
  exact λ ⟨t, ht, s, hs, h⟩, ⟨s, hs, t, ht, λ x hx y hy, @h ⟨x, y⟩ ⟨hx, hy⟩⟩,
  exact λ ⟨s, hs, t, ht, h⟩, ⟨t, ht, s, hs, λ ⟨x, y⟩ ⟨hx, hy⟩, h x hx y hy⟩
end

lemma prod_eq {f : filter α} {g : filter β} : f ×ᶠ g = (f.map prod.mk).seq g  :=
have h : _ := map_prod id f g, by rwa [map_id] at h

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  (f₁ ×ᶠ g₁) ⊓ (f₂ ×ᶠ g₂) = (f₁ ⊓ f₂) ×ᶠ (g₁ ⊓ g₂) :=
by simp only [filter.prod, comap_inf, inf_comm, inf_assoc, inf_left_comm]

@[simp] lemma prod_bot {f : filter α} : f ×ᶠ (⊥ : filter β) = ⊥ := by simp [filter.prod]
@[simp] lemma bot_prod {g : filter β} : (⊥ : filter α) ×ᶠ g = ⊥ := by simp [filter.prod]

@[simp] lemma prod_principal_principal {s : set α} {t : set β} :
  (𝓟 s) ×ᶠ (𝓟 t) = 𝓟 (s ×ˢ t) :=
by simp only [filter.prod, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal];
  refl

@[simp] lemma pure_prod {a : α} {f : filter β} : pure a ×ᶠ f = map (prod.mk a) f :=
by rw [prod_eq, map_pure, pure_seq_eq_map]

@[simp] lemma prod_pure {f : filter α} {b : β} : f ×ᶠ pure b = map (λ a, (a, b)) f :=
by rw [prod_eq, seq_pure, map_map]

lemma prod_pure_pure {a : α} {b : β} : (pure a) ×ᶠ (pure b) = pure (a, b) :=
by simp

lemma prod_eq_bot {f : filter α} {g : filter β} : f ×ᶠ g = ⊥ ↔ (f = ⊥ ∨ g = ⊥) :=
begin
  split,
  { intro h,
    rcases mem_prod_iff.1 (empty_mem_iff_bot.2 h) with ⟨s, hs, t, ht, hst⟩,
    rw [subset_empty_iff, set.prod_eq_empty_iff] at hst,
    cases hst with s_eq t_eq,
    { left, exact empty_mem_iff_bot.1 (s_eq ▸ hs) },
    { right, exact empty_mem_iff_bot.1 (t_eq ▸ ht) } },
  { rintro (rfl | rfl),
    exact bot_prod,
    exact prod_bot }
end

lemma prod_ne_bot {f : filter α} {g : filter β} : ne_bot (f ×ᶠ g) ↔ (ne_bot f ∧ ne_bot g) :=
by simp only [ne_bot_iff, ne, prod_eq_bot, not_or_distrib]

lemma ne_bot.prod {f : filter α} {g : filter β} (hf : ne_bot f) (hg : ne_bot g) :
  ne_bot (f ×ᶠ g) :=
prod_ne_bot.2 ⟨hf, hg⟩

instance prod_ne_bot' {f : filter α} {g : filter β} [hf : ne_bot f] [hg : ne_bot g] :
  ne_bot (f ×ᶠ g) :=
hf.prod hg

lemma tendsto_prod_iff {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} :
  filter.tendsto f (x ×ᶠ y) z ↔
  ∀ W ∈ z, ∃ U ∈ x,  ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff, exists_prop, iff_self]

end prod

/-! ### Coproducts of filters -/

section coprod
variables {f : filter α} {g : filter β}

/-- Coproduct of filters. -/
protected def coprod (f : filter α) (g : filter β) : filter (α × β) :=
f.comap prod.fst ⊔ g.comap prod.snd

lemma mem_coprod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ f.coprod g ↔ ((∃ t₁ ∈ f, prod.fst ⁻¹' t₁ ⊆ s) ∧ (∃ t₂ ∈ g, prod.snd ⁻¹' t₂ ⊆ s)) :=
by simp [filter.coprod]

@[mono] lemma coprod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  f₁.coprod g₁ ≤ f₂.coprod g₂ :=
sup_le_sup (comap_mono hf) (comap_mono hg)

lemma coprod_ne_bot_iff : (f.coprod g).ne_bot ↔ f.ne_bot ∧ nonempty β ∨ nonempty α ∧ g.ne_bot :=
by simp [filter.coprod]

@[instance] lemma coprod_ne_bot_left [ne_bot f] [nonempty β] : (f.coprod g).ne_bot :=
coprod_ne_bot_iff.2 (or.inl ⟨‹_›, ‹_›⟩)

@[instance] lemma coprod_ne_bot_right [ne_bot g] [nonempty α] : (f.coprod g).ne_bot :=
coprod_ne_bot_iff.2 (or.inr ⟨‹_›, ‹_›⟩)

lemma principal_coprod_principal (s : set α) (t : set β) :
  (𝓟 s).coprod (𝓟 t) = 𝓟 (sᶜ ×ˢ tᶜ)ᶜ :=
begin
  rw [filter.coprod, comap_principal, comap_principal, sup_principal],
  congr,
  ext x,
  simp ; tauto,
end

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prod_map_const_id_principal_coprod_principal` below.
lemma map_prod_map_coprod_le {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  map (prod.map m₁ m₂) (f₁.coprod f₂) ≤ (map m₁ f₁).coprod (map m₂ f₂) :=
begin
  intros s,
  simp only [mem_map, mem_coprod_iff],
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩,
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, λ _ hx, h₁ _⟩, ⟨m₂ ⁻¹' u₂, hu₂, λ _ hx, h₂ _⟩⟩; convert hx
end

/-- Characterization of the coproduct of the `filter.map`s of two principal filters `𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `λ a, b` and the second under the identity function.
Together with the next lemma, `map_prod_map_const_id_principal_coprod_principal`, this provides an
example showing that the inequality in the lemma `map_prod_map_coprod_le` can be strict. -/
lemma map_const_principal_coprod_map_id_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
  (map (λ _ : α, b) (𝓟 {a})).coprod (map id (𝓟 {i}))
  = 𝓟 (({b} : set β) ×ˢ (univ : set ι) ∪ (univ : set β) ×ˢ ({i} : set ι)) :=
begin
  rw [map_principal, map_principal, principal_coprod_principal],
  congr,
  ext ⟨b', i'⟩,
  simp,
  tauto,
end

/-- Characterization of the `filter.map` of the coproduct of two principal filters `𝓟 {a}` and
`𝓟 {i}`, under the `prod.map` of two functions, respectively the constant function `λ a, b` and the
identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing that the inequality
in the lemma `map_prod_map_coprod_le` can be strict. -/
lemma map_prod_map_const_id_principal_coprod_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
  map (prod.map (λ _ : α, b) id) ((𝓟 {a}).coprod (𝓟 {i}))
  = 𝓟 (({b} : set β) ×ˢ (univ : set ι)) :=
begin
  rw [principal_coprod_principal, map_principal],
  congr,
  ext ⟨b', i'⟩,
  split,
  { rintro ⟨⟨a'', i''⟩, h₁, h₂, h₃⟩,
    simp },
  { rintro ⟨h₁, h₂⟩,
    use (a, i'),
    simpa using h₁.symm }
end

lemma tendsto.prod_map_coprod {δ : Type*} {f : α → γ} {g : β → δ} {a : filter α} {b : filter β}
  {c : filter γ} {d : filter δ} (hf : tendsto f a c) (hg : tendsto g b d) :
  tendsto (prod.map f g) (a.coprod b) (c.coprod d) :=
map_prod_map_coprod_le.trans (coprod_mono hf hg)

end coprod

end filter

open_locale filter

lemma set.eq_on.eventually_eq {α β} {s : set α} {f g : α → β} (h : eq_on f g s) :
  f =ᶠ[𝓟 s] g :=
h

lemma set.eq_on.eventually_eq_of_mem {α β} {s : set α} {l : filter α} {f g : α → β}
  (h : eq_on f g s) (hl : s ∈ l) :
  f =ᶠ[l] g :=
h.eventually_eq.filter_mono $ filter.le_principal_iff.2 hl

lemma set.subset.eventually_le {α} {l : filter α} {s t : set α} (h : s ⊆ t) : s ≤ᶠ[l] t :=
filter.eventually_of_forall h

lemma set.maps_to.tendsto {α β} {s : set α} {t : set β} {f : α → β} (h : maps_to f s t) :
  filter.tendsto f (𝓟 s) (𝓟 t) :=
filter.tendsto_principal_principal.2 h
