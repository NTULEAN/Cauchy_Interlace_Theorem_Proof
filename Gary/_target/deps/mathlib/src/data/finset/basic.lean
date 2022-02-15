/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import data.int.basic
import data.multiset.finset_ops
import tactic.apply
import tactic.monotonicity
import tactic.nth_rewrite

/-!
# Finite sets

Terms of type `finset α` are one way of talking about finite subsets of `α` in mathlib.
Below, `finset α` is defined as a structure with 2 fields:

  1. `val` is a `multiset α` of elements;
  2. `nodup` is a proof that `val` has no duplicates.

Finsets in Lean are constructive in that they have an underlying `list` that enumerates their
elements. In particular, any function that uses the data of the underlying list cannot depend on its
ordering. This is handled on the `multiset` level by multiset API, so in most cases one needn't
worry about it explicitly.

Finsets give a basic foundation for defining finite sums and products over types:

  1. `∑ i in (s : finset α), f i`;
  2. `∏ i in (s : finset α), f i`.

Lean refers to these operations as `big_operator`s.
More information can be found in `algebra.big_operators.basic`.

Finsets are directly used to define fintypes in Lean.
A `fintype α` instance for a type `α` consists of
a universal `finset α` containing every term of `α`, called `univ`. See `data.fintype.basic`.
There is also `univ'`, the noncomputable partner to `univ`,
which is defined to be `α` as a finset if `α` is finite,
and the empty finset otherwise. See `data.fintype.basic`.

`finset.card`, the size of a finset is defined in `data.finset.card`. This is then used to define
`fintype.card`, the size of a type.

## Main declarations

### Main definitions

* `finset`: Defines a type for the finite subsets of `α`.
  Constructing a `finset` requires two pieces of data: `val`, a `multiset α` of elements,
  and `nodup`, a proof that `val` has no duplicates.
* `finset.has_mem`: Defines membership `a ∈ (s : finset α)`.
* `finset.has_coe`: Provides a coercion `s : finset α` to `s : set α`.
* `finset.has_coe_to_sort`: Coerce `s : finset α` to the type of all `x ∈ s`.
* `finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `finset α`,
  then it holds for the finset obtained by inserting a new element.
* `finset.choose`: Given a proof `h` of existence and uniqueness of a certain element
  satisfying a predicate, `choose s h` returns the element of `s` satisfying that predicate.

### Finset constructions

* `singleton`: Denoted by `{a}`; the finset consisting of one element.
* `finset.empty`: Denoted by `∅`. The finset associated to any type consisting of no elements.
* `finset.range`: For any `n : ℕ`, `range n` is equal to `{0, 1, ... , n - 1} ⊆ ℕ`.
  This convention is consistent with other languages and normalizes `card (range n) = n`.
  Beware, `n` is not in `range n`.
* `finset.attach`: Given `s : finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

### Finsets from functions

* `finset.image`: Given a function `f : α → β`, `s.image f` is the image finset in `β`.
* `finset.map`: Given an embedding `f : α ↪ β`, `s.map f` is the image finset in `β`.
* `finset.filter`: Given a predicate `p : α → Prop`, `s.filter p` is
  the finset consisting of those elements in `s` satisfying the predicate `p`.

### The lattice structure on subsets of finsets

There is a natural lattice structure on the subsets of a set.
In Lean, we use lattice notation to talk about things involving unions and intersections. See
`order.lattice`. For the lattice structure on finsets, `⊥` is called `bot` with `⊥ = ∅` and `⊤` is
called `top` with `⊤ = univ`.

* `finset.has_subset`: Lots of API about lattices, otherwise behaves exactly as one would expect.
* `finset.has_union`: Defines `s ∪ t` (or `s ⊔ t`) as the union of `s` and `t`.
  See `finset.sup`/`finset.bUnion` for finite unions.
* `finset.has_inter`: Defines `s ∩ t` (or `s ⊓ t`) as the intersection of `s` and `t`.
  See `finset.inf` for finite intersections.
* `finset.disj_union`: Given a hypothesis `h` which states that finsets `s` and `t` are disjoint,
  `s.disj_union t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`; this does
  not require decidable equality on the type `α`.

### Operations on two or more finsets

* `insert` and `finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.
* `finset.has_union`: see "The lattice structure on subsets of finsets"
* `finset.has_inter`: see "The lattice structure on subsets of finsets"
* `finset.erase`: For any `a : α`, `erase s a` returns `s` with the element `a` removed.
* `finset.has_sdiff`: Defines the set difference `s \ t` for finsets `s` and `t`.
* `finset.product`: Given finsets of `α` and `β`, defines finsets of `α × β`.
  For arbitrary dependent products, see `data.finset.pi`.
* `finset.bUnion`: Finite unions of finsets; given an indexing function `f : α → finset β` and a
  `s : finset α`, `s.bUnion f` is the union of all finsets of the form `f a` for `a ∈ s`.
* `finset.bInter`: TODO: Implemement finite intersections.

### Maps constructed using finsets

* `finset.piecewise`: Given two functions `f`, `g`, `s.piecewise f g` is a function which is equal
  to `f` on `s` and `g` on the complement.

### Predicates on finsets

* `disjoint`: defined via the lattice structure on finsets; two sets are disjoint if their
  intersection is empty.
* `finset.nonempty`: A finset is nonempty if it has elements.
  This is equivalent to saying `s ≠ ∅`. TODO: Decide on the simp normal form.

### Equivalences between finsets

* The `data.equiv` files describe a general type of equivalence, so look in there for any lemmas.
  There is some API for rewriting sums and products from `s` to `t` given that `s ≃ t`.
  TODO: examples

## Tags

finite sets, finset

-/

open multiset subtype nat function

universes u

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `finset α` is the type of finite sets of elements of `α`. It is implemented
  as a multiset (a list up to permutation) which has no duplicate elements. -/
structure finset (α : Type*) :=
(val : multiset α)
(nodup : nodup val)

namespace finset

theorem eq_of_veq : ∀ {s t : finset α}, s.1 = t.1 → s = t
| ⟨s, _⟩ ⟨t, _⟩ rfl := rfl

@[simp] theorem val_inj {s t : finset α} : s.1 = t.1 ↔ s = t :=
⟨eq_of_veq, congr_arg _⟩

@[simp] theorem erase_dup_eq_self [decidable_eq α] (s : finset α) : erase_dup s.1 = s.1 :=
s.2.erase_dup

instance has_decidable_eq [decidable_eq α] : decidable_eq (finset α)
| s₁ s₂ := decidable_of_iff _ val_inj

/-! ### membership -/

instance : has_mem α (finset α) := ⟨λ a s, a ∈ s.1⟩

theorem mem_def {a : α} {s : finset α} : a ∈ s ↔ a ∈ s.1 := iff.rfl

@[simp] theorem mem_mk {a : α} {s nd} : a ∈ @finset.mk α s nd ↔ a ∈ s := iff.rfl

instance decidable_mem [h : decidable_eq α] (a : α) (s : finset α) : decidable (a ∈ s) :=
multiset.decidable_mem _ _

/-! ### set coercion -/

/-- Convert a finset to a set in the natural way. -/
instance : has_coe_t (finset α) (set α) := ⟨λ s, {x | x ∈ s}⟩

@[simp, norm_cast] lemma mem_coe {a : α} {s : finset α} : a ∈ (s : set α) ↔ a ∈ s := iff.rfl

@[simp] lemma set_of_mem {α} {s : finset α} : {a | a ∈ s} = s := rfl

@[simp] lemma coe_mem {s : finset α} (x : (s : set α)) : ↑x ∈ s := x.2

@[simp] lemma mk_coe {s : finset α} (x : (s : set α)) {h} :
  (⟨x, h⟩ : (s : set α)) = x :=
subtype.coe_eta _ _

instance decidable_mem' [decidable_eq α] (a : α) (s : finset α) :
  decidable (a ∈ (s : set α)) := s.decidable_mem _

/-! ### extensionality -/
theorem ext_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
val_inj.symm.trans $ nodup_ext s₁.2 s₂.2

@[ext]
theorem ext {s₁ s₂ : finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
ext_iff.2

@[simp, norm_cast] theorem coe_inj {s₁ s₂ : finset α} : (s₁ : set α) = s₂ ↔ s₁ = s₂ :=
set.ext_iff.trans ext_iff.symm

lemma coe_injective {α} : injective (coe : finset α → set α) :=
λ s t, coe_inj.1

/-! ### type coercion -/

/-- Coercion from a finset to the corresponding subtype. -/
instance {α : Type u} : has_coe_to_sort (finset α) (Type u) := ⟨λ s, {x // x ∈ s}⟩

instance pi_finset_coe.can_lift (ι : Type*) (α : Π i : ι, Type*) [ne : Π i, nonempty (α i)]
  (s : finset ι) :
can_lift (Π i : s, α i) (Π i, α i) :=
{ coe := λ f i, f i,
  .. pi_subtype.can_lift ι α (∈ s) }

instance pi_finset_coe.can_lift' (ι α : Type*) [ne : nonempty α] (s : finset ι) :
  can_lift (s → α) (ι → α) :=
pi_finset_coe.can_lift ι (λ _, α) s

instance finset_coe.can_lift (s : finset α) : can_lift α s :=
{ coe := coe,
  cond := λ a, a ∈ s,
  prf := λ a ha, ⟨⟨a, ha⟩, rfl⟩ }

@[simp, norm_cast] lemma coe_sort_coe (s : finset α) :
  ((s : set α) : Sort*) = s := rfl

/-! ### Subset and strict subset relations -/

section subset
variables {s t : finset α}

instance : has_subset (finset α) := ⟨λ s t, ∀ ⦃a⦄, a ∈ s → a ∈ t⟩
instance : has_ssubset (finset α) := ⟨λ s t, s ⊆ t ∧ ¬ t ⊆ s⟩

instance : partial_order (finset α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := λ s a, id,
  le_trans := λ s t u hst htu a ha, htu $ hst ha,
  le_antisymm := λ s t hst hts, ext $ λ a, ⟨@hst _, @hts _⟩ }

instance : is_refl (finset α) (⊆) := has_le.le.is_refl
instance : is_trans (finset α) (⊆) := has_le.le.is_trans
instance : is_antisymm (finset α) (⊆) := has_le.le.is_antisymm
instance : is_irrefl (finset α) (⊂) := has_lt.lt.is_irrefl
instance : is_trans (finset α) (⊂) := has_lt.lt.is_trans
instance : is_asymm (finset α) (⊂) := has_lt.lt.is_asymm
instance : is_nonstrict_strict_order (finset α) (⊆) (⊂) := ⟨λ _ _, iff.rfl⟩

lemma subset_def : s ⊆ t ↔ s.1 ⊆ t.1 := iff.rfl
lemma ssubset_def : s ⊂ t ↔ s ⊆ t ∧ ¬ t ⊆ s := iff.rfl

@[simp] theorem subset.refl (s : finset α) : s ⊆ s := subset.refl _
protected lemma subset.rfl {s :finset α} : s ⊆ s := subset.refl _

protected theorem subset_of_eq {s t : finset α} (h : s = t) : s ⊆ t := h ▸ subset.refl _

theorem subset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ := subset.trans

theorem superset.trans {s₁ s₂ s₃ : finset α} : s₁ ⊇ s₂ → s₂ ⊇ s₃ → s₁ ⊇ s₃ :=
λ h' h, subset.trans h h'

theorem mem_of_subset {s₁ s₂ : finset α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ := mem_of_subset

lemma not_mem_mono {s t : finset α} (h : s ⊆ t) {a : α} : a ∉ t → a ∉ s := mt $ @h _

theorem subset.antisymm {s₁ s₂ : finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
ext $ λ a, ⟨@H₁ a, @H₂ a⟩

theorem subset_iff {s₁ s₂ : finset α} : s₁ ⊆ s₂ ↔ ∀ ⦃x⦄, x ∈ s₁ → x ∈ s₂ := iff.rfl

@[simp, norm_cast] theorem coe_subset {s₁ s₂ : finset α} :
  (s₁ : set α) ⊆ s₂ ↔ s₁ ⊆ s₂ := iff.rfl

@[simp] theorem val_le_iff {s₁ s₂ : finset α} : s₁.1 ≤ s₂.1 ↔ s₁ ⊆ s₂ := le_iff_subset s₁.2

theorem subset.antisymm_iff {s₁ s₂ : finset α} : s₁ = s₂ ↔ s₁ ⊆ s₂ ∧ s₂ ⊆ s₁ :=
le_antisymm_iff

theorem not_subset (s t : finset α) : ¬(s ⊆ t) ↔ ∃ x ∈ s, ¬(x ∈ t) :=
by simp only [←finset.coe_subset, set.not_subset, exists_prop, finset.mem_coe]

@[simp] theorem le_eq_subset : ((≤) : finset α → finset α → Prop) = (⊆) := rfl
@[simp] theorem lt_eq_subset : ((<) : finset α → finset α → Prop) = (⊂) := rfl

theorem le_iff_subset {s₁ s₂ : finset α} : s₁ ≤ s₂ ↔ s₁ ⊆ s₂ := iff.rfl
theorem lt_iff_ssubset {s₁ s₂ : finset α} : s₁ < s₂ ↔ s₁ ⊂ s₂ := iff.rfl

@[simp, norm_cast] lemma coe_ssubset {s₁ s₂ : finset α} : (s₁ : set α) ⊂ s₂ ↔ s₁ ⊂ s₂ :=
show (s₁ : set α) ⊂ s₂ ↔ s₁ ⊆ s₂ ∧ ¬s₂ ⊆ s₁,
  by simp only [set.ssubset_def, finset.coe_subset]

@[simp] theorem val_lt_iff {s₁ s₂ : finset α} : s₁.1 < s₂.1 ↔ s₁ ⊂ s₂ :=
and_congr val_le_iff $ not_congr val_le_iff

lemma ssubset_iff_subset_ne {s t : finset α} : s ⊂ t ↔ s ⊆ t ∧ s ≠ t :=
@lt_iff_le_and_ne _ _ s t

theorem ssubset_iff_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁ ⊂ s₂ ↔ ∃ x ∈ s₂, x ∉ s₁ :=
set.ssubset_iff_of_subset h

lemma ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
  s₁ ⊂ s₃ :=
set.ssubset_of_ssubset_of_subset hs₁s₂ hs₂s₃

lemma ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
  s₁ ⊂ s₃ :=
set.ssubset_of_subset_of_ssubset hs₁s₂ hs₂s₃

lemma exists_of_ssubset {s₁ s₂ : finset α} (h : s₁ ⊂ s₂) :
  ∃ x ∈ s₂, x ∉ s₁ :=
set.exists_of_ssubset h

end subset

-- TODO: these should be global attributes, but this will require fixing other files
local attribute [trans] subset.trans superset.trans

/-! ### Order embedding from `finset α` to `set α` -/

/-- Coercion to `set α` as an `order_embedding`. -/
def coe_emb : finset α ↪o set α := ⟨⟨coe, coe_injective⟩, λ s t, coe_subset⟩

@[simp] lemma coe_coe_emb : ⇑(coe_emb : finset α ↪o set α) = coe := rfl

/-! ### Nonempty -/

/-- The property `s.nonempty` expresses the fact that the finset `s` is not empty. It should be used
in theorem assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks
to the dot notation. -/
protected def nonempty (s : finset α) : Prop := ∃ x:α, x ∈ s

@[simp, norm_cast] lemma coe_nonempty {s : finset α} : (s:set α).nonempty ↔ s.nonempty := iff.rfl

@[simp] lemma nonempty_coe_sort (s : finset α) : nonempty ↥s ↔ s.nonempty := nonempty_subtype

alias coe_nonempty ↔ _ finset.nonempty.to_set

lemma nonempty.bex {s : finset α} (h : s.nonempty) : ∃ x:α, x ∈ s := h

lemma nonempty.mono {s t : finset α} (hst : s ⊆ t) (hs : s.nonempty) : t.nonempty :=
set.nonempty.mono hst hs

lemma nonempty.forall_const {s : finset α} (h : s.nonempty) {p : Prop} : (∀ x ∈ s, p) ↔ p :=
let ⟨x, hx⟩ := h in ⟨λ h, h x hx, λ h x hx, h⟩

/-! ### empty -/

/-- The empty finset -/
protected def empty : finset α := ⟨0, nodup_zero⟩

instance : has_emptyc (finset α) := ⟨finset.empty⟩

instance inhabited_finset : inhabited (finset α) := ⟨∅⟩

@[simp] theorem empty_val : (∅ : finset α).1 = 0 := rfl

@[simp] theorem not_mem_empty (a : α) : a ∉ (∅ : finset α) := id

@[simp] theorem not_nonempty_empty : ¬(∅ : finset α).nonempty :=
λ ⟨x, hx⟩, not_mem_empty x hx

@[simp] theorem mk_zero : (⟨0, nodup_zero⟩ : finset α) = ∅ := rfl

theorem ne_empty_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ≠ ∅ :=
λ e, not_mem_empty a $ e ▸ h

theorem nonempty.ne_empty {s : finset α} (h : s.nonempty) : s ≠ ∅ :=
exists.elim h $ λ a, ne_empty_of_mem

@[simp] theorem empty_subset (s : finset α) : ∅ ⊆ s := zero_subset _

lemma eq_empty_of_forall_not_mem {s : finset α} (H : ∀ x, x ∉ s) : s = ∅ :=
eq_of_veq (eq_zero_of_forall_not_mem H)

lemma eq_empty_iff_forall_not_mem {s : finset α} : s = ∅ ↔ ∀ x, x ∉ s :=
⟨by rintro rfl x; exact id, λ h, eq_empty_of_forall_not_mem h⟩

@[simp] theorem val_eq_zero {s : finset α} : s.1 = 0 ↔ s = ∅ := @val_inj _ s ∅

theorem subset_empty {s : finset α} : s ⊆ ∅ ↔ s = ∅ := subset_zero.trans val_eq_zero

@[simp] lemma not_ssubset_empty (s : finset α) : ¬s ⊂ ∅ :=
λ h, let ⟨x, he, hs⟩ := exists_of_ssubset h in he

theorem nonempty_of_ne_empty {s : finset α} (h : s ≠ ∅) : s.nonempty :=
exists_mem_of_ne_zero (mt val_eq_zero.1 h)

theorem nonempty_iff_ne_empty {s : finset α} : s.nonempty ↔ s ≠ ∅ :=
⟨nonempty.ne_empty, nonempty_of_ne_empty⟩

@[simp] theorem not_nonempty_iff_eq_empty {s : finset α} : ¬s.nonempty ↔ s = ∅ :=
nonempty_iff_ne_empty.not.trans not_not

theorem eq_empty_or_nonempty (s : finset α) : s = ∅ ∨ s.nonempty :=
classical.by_cases or.inl (λ h, or.inr (nonempty_of_ne_empty h))

@[simp, norm_cast] lemma coe_empty : ((∅ : finset α) : set α) = ∅ := rfl

@[simp, norm_cast] lemma coe_eq_empty {s : finset α} : (s : set α) = ∅ ↔ s = ∅ :=
by rw [← coe_empty, coe_inj]

/-- A `finset` for an empty type is empty. -/
lemma eq_empty_of_is_empty [is_empty α] (s : finset α) : s = ∅ :=
finset.eq_empty_of_forall_not_mem is_empty_elim

/-! ### singleton -/
/--
`{a} : finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `decidable_eq` instance for `α`.
-/
instance : has_singleton α (finset α) := ⟨λ a, ⟨{a}, nodup_singleton a⟩⟩

@[simp] theorem singleton_val (a : α) : ({a} : finset α).1 = {a} := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ({a} : finset α) ↔ b = a := mem_singleton

lemma eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : finset α)) : x = y := mem_singleton.1 h

theorem not_mem_singleton {a b : α} : a ∉ ({b} : finset α) ↔ a ≠ b := not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : finset α) := or.inl rfl

lemma singleton_injective : injective (singleton : α → finset α) :=
λ a b h, mem_singleton.1 (h ▸ mem_singleton_self _)

theorem singleton_inj {a b : α} : ({a} : finset α) = {b} ↔ a = b :=
singleton_injective.eq_iff

@[simp] theorem singleton_nonempty (a : α) : ({a} : finset α).nonempty := ⟨a, mem_singleton_self a⟩

@[simp] theorem singleton_ne_empty (a : α) : ({a} : finset α) ≠ ∅ := (singleton_nonempty a).ne_empty

@[simp, norm_cast] lemma coe_singleton (a : α) : (({a} : finset α) : set α) = {a} :=
by { ext, simp }

@[simp, norm_cast] lemma coe_eq_singleton {α : Type*} {s : finset α} {a : α} :
  (s : set α) = {a} ↔ s = {a} :=
by rw [←finset.coe_singleton, finset.coe_inj]

lemma eq_singleton_iff_unique_mem {s : finset α} {a : α} :
  s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
begin
  split; intro t,
    rw t,
    refine ⟨finset.mem_singleton_self _, λ _, finset.mem_singleton.1⟩,
  ext, rw finset.mem_singleton,
  refine ⟨t.right _, λ r, r.symm ▸ t.left⟩
end

lemma eq_singleton_iff_nonempty_unique_mem {s : finset α} {a : α} :
  s = {a} ↔ s.nonempty ∧ ∀ x ∈ s, x = a :=
begin
  split,
  { rintro rfl, simp },
  { rintros ⟨hne, h_uniq⟩, rw eq_singleton_iff_unique_mem, refine ⟨_, h_uniq⟩,
    rw ← h_uniq hne.some hne.some_spec, exact hne.some_spec }
end

lemma singleton_iff_unique_mem (s : finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s :=
by simp only [eq_singleton_iff_unique_mem, exists_unique]

lemma singleton_subset_set_iff {s : set α} {a : α} : ↑({a} : finset α) ⊆ s ↔ a ∈ s :=
by rw [coe_singleton, set.singleton_subset_iff]

@[simp] lemma singleton_subset_iff {s : finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
singleton_subset_set_iff

@[simp] lemma subset_singleton_iff {s : finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} :=
begin
  refine ⟨λ hs, s.eq_empty_or_nonempty.imp_right _, _⟩,
  { rintro ⟨t, ht⟩,
    apply subset.antisymm hs,
    rwa [singleton_subset_iff, ←mem_singleton.1 (hs ht)] },
  rintro (rfl | rfl),
  { exact empty_subset _ },
  exact subset.rfl,
end

lemma subset_singleton_iff' {s : finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
forall₂_congr $ λ _ _, mem_singleton

@[simp] lemma ssubset_singleton_iff {s : finset α} {a : α} :
  s ⊂ {a} ↔ s = ∅ :=
by rw [←coe_ssubset, coe_singleton, set.ssubset_singleton_iff, coe_eq_empty]

lemma eq_empty_of_ssubset_singleton {s : finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
ssubset_singleton_iff.1 hs

/-! ### cons -/

section cons
variables {s t : finset α} {a b : α}

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `decidable_eq α`,
and the union is guaranteed to be disjoint. -/
def cons (a : α) (s : finset α) (h : a ∉ s) : finset α := ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp] lemma mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s := mem_cons
@[simp] lemma mem_cons_self (a : α) (s : finset α) {h} : a ∈ cons a s h := mem_cons_self _ _
@[simp] lemma cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 := rfl

@[simp] lemma mk_cons {s : multiset α} (h : (a ::ₘ s).nodup) :
  (⟨a ::ₘ s, h⟩ : finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 := rfl

@[simp] lemma nonempty_cons (h : a ∉ s) : (cons a s h).nonempty := ⟨a, mem_cons.2 $ or.inl rfl⟩

@[simp] lemma nonempty_mk_coe : ∀ {l : list α} {hl}, (⟨↑l, hl⟩ : finset α).nonempty ↔ l ≠ []
| []       hl := by simp
| (a :: l) hl := by simp [← multiset.cons_coe]

@[simp] lemma coe_cons {a s h} : (@cons α a s h : set α) = insert a s := by { ext, simp }

@[simp] lemma cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t :=
by rwa [← coe_subset, coe_cons, coe_cons, set.insert_subset_insert_iff, coe_subset]

/-! ### disjoint union -/

/-- `disj_union s t h` is the set such that `a ∈ disj_union s t h` iff `a ∈ s` or `a ∈ t`.
It is the same as `s ∪ t`, but it does not require decidable equality on the type. The hypothesis
ensures that the sets are disjoint. -/
def disj_union {α} (s t : finset α) (h : ∀ a ∈ s, a ∉ t) : finset α :=
⟨s.1 + t.1, multiset.nodup_add.2 ⟨s.2, t.2, h⟩⟩

@[simp] theorem mem_disj_union {α s t h a} :
  a ∈ @disj_union α s t h ↔ a ∈ s ∨ a ∈ t :=
by rcases s with ⟨⟨s⟩⟩; rcases t with ⟨⟨t⟩⟩; apply list.mem_append

end cons

/-! ### insert -/

section decidable_eq
variables [decidable_eq α] {s t u v : finset α} {a b : α}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : has_insert α (finset α) := ⟨λ a s, ⟨_, nodup_ndinsert a s.2⟩⟩

theorem insert_def (a : α) (s : finset α) : insert a s = ⟨_, nodup_ndinsert a s.2⟩ := rfl

@[simp] theorem insert_val (a : α) (s : finset α) : (insert a s).1 = ndinsert a s.1 := rfl

theorem insert_val' (a : α) (s : finset α) : (insert a s).1 = erase_dup (a ::ₘ s.1) :=
by rw [erase_dup_cons, erase_dup_eq_self]; refl

theorem insert_val_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 :=
by rw [insert_val, ndinsert_of_not_mem h]

@[simp] lemma mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s := mem_ndinsert

theorem mem_insert_self (a : α) (s : finset α) : a ∈ insert a s := mem_ndinsert_self a s.1
lemma mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s := mem_ndinsert_of_mem h
lemma mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s := (mem_insert.1 h).resolve_left

@[simp] theorem cons_eq_insert {α} [decidable_eq α] (a s h) : @cons α a s h = insert a s :=
ext $ λ a, by simp

@[simp, norm_cast] lemma coe_insert (a : α) (s : finset α) :
  ↑(insert a s) = (insert a s : set α) :=
set.ext $ λ x, by simp only [mem_coe, mem_insert, set.mem_insert_iff]

lemma mem_insert_coe {s : finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : set α) :=
by simp

instance : is_lawful_singleton α (finset α) := ⟨λ a, by { ext, simp }⟩

@[simp] lemma insert_eq_of_mem (h : a ∈ s) : insert a s = s := eq_of_veq $ ndinsert_of_mem h

@[simp] theorem insert_singleton_self_eq (a : α) : ({a, a} : finset α) = {a} :=
insert_eq_of_mem $ mem_singleton_self _

theorem insert.comm (a b : α) (s : finset α) : insert a (insert b s) = insert b (insert a s) :=
ext $ λ x, by simp only [mem_insert, or.left_comm]

theorem insert_singleton_comm (a b : α) : ({a, b} : finset α) = {b, a} :=
begin
  ext,
  simp [or.comm]
end

@[simp] theorem insert_idem (a : α) (s : finset α) : insert a (insert a s) = insert a s :=
ext $ λ x, by simp only [mem_insert, or.assoc.symm, or_self]

@[simp] theorem insert_nonempty (a : α) (s : finset α) : (insert a s).nonempty :=
⟨a, mem_insert_self a s⟩

@[simp] theorem insert_ne_empty (a : α) (s : finset α) : insert a s ≠ ∅ :=
(insert_nonempty a s).ne_empty

/-!
The universe annotation is required for the following instance, possibly this is a bug in Lean. See
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/strange.20error.20(universe.20issue.3F)
-/

instance {α : Type u} [decidable_eq α] (i : α) (s : finset α) :
  nonempty.{u + 1} ((insert i s : finset α) : set α) :=
(finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

lemma ne_insert_of_not_mem (s t : finset α) {a : α} (h : a ∉ s) : s ≠ insert a t :=
by { contrapose! h, simp [h] }

lemma insert_subset : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp only [subset_iff, mem_insert, forall_eq, or_imp_distrib, forall_and_distrib]

lemma subset_insert (a : α) (s : finset α) : s ⊆ insert a s := λ b, mem_insert_of_mem

theorem insert_subset_insert (a : α) {s t : finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
insert_subset.2 ⟨mem_insert_self _ _, subset.trans h (subset_insert _ _)⟩

lemma ssubset_iff : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t :=
by exact_mod_cast @set.ssubset_iff_insert α s t

lemma ssubset_insert (h : a ∉ s) : s ⊂ insert a s := ssubset_iff.mpr ⟨a, h, subset.rfl⟩

@[elab_as_eliminator]
lemma cons_induction {α : Type*} {p : finset α → Prop}
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
| ⟨s, nd⟩ := multiset.induction_on s (λ _, h₁) (λ a s IH nd, begin
    cases nodup_cons.1 nd with m nd',
    rw [← (eq_of_veq _ : cons a (finset.mk s _) m = ⟨a ::ₘ s, nd⟩)],
    { exact h₂ (by exact m) (IH nd') },
    { rw [cons_val] }
  end) nd

@[elab_as_eliminator]
lemma cons_induction_on {α : Type*} {p : finset α → Prop} (s : finset α)
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
cons_induction h₁ h₂ s

@[elab_as_eliminator]
protected theorem induction {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
cons_induction h₁ $ λ a s ha, (s.cons_eq_insert a ha).symm ▸ h₂ ha

/--
To prove a proposition about an arbitrary `finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α`,
then it holds for the `finset` obtained by inserting a new element.
-/
@[elab_as_eliminator]
protected theorem induction_on {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (s : finset α) (h₁ : p ∅) (h₂ : ∀ ⦃a : α⦄ {s : finset α}, a ∉ s → p s → p (insert a s)) : p s :=
finset.induction h₁ h₂ s

/--
To prove a proposition about `S : finset α`,
it suffices to prove it for the empty `finset`,
and to show that if it holds for some `finset α ⊆ S`,
then it holds for the `finset` obtained by inserting a new element of `S`.
-/
@[elab_as_eliminator]
theorem induction_on' {α : Type*} {p : finset α → Prop} [decidable_eq α]
  (S : finset α) (h₁ : p ∅) (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
@finset.induction_on α (λ T, T ⊆ S → p T) _ S (λ _, h₁) (λ a s has hqs hs,
  let ⟨hS, sS⟩ := finset.insert_subset.1 hs in h₂ hS sS has (hqs sS)) (finset.subset.refl S)

/-- To prove a proposition about a nonempty `s : finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : finset α`, then it also holds for the `finset`
obtained by inserting an element in `t`. -/
@[elab_as_eliminator]
lemma nonempty.cons_induction {α : Type*} {p : Π s : finset α, s.nonempty → Prop}
  (h₀ : ∀ a, p {a} (singleton_nonempty _))
  (h₁ : ∀ ⦃a⦄ s (h : a ∉ s) hs, p s hs → p (finset.cons a s h) (nonempty_cons h))
  {s : finset α} (hs : s.nonempty) : p s hs :=
begin
  induction s using finset.cons_induction with a t ha h,
  { exact (not_nonempty_empty hs).elim },
  obtain rfl | ht := t.eq_empty_or_nonempty,
  { exact h₀ a },
  { exact h₁ t ha ht (h ht) }
end

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtype_insert_equiv_option {t : finset α} {x : α} (h : x ∉ t) :
  {i // i ∈ insert x t} ≃ option {i // i ∈ t} :=
begin
  refine
  { to_fun := λ y, if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩,
    inv_fun := λ y, y.elim ⟨x, mem_insert_self _ _⟩ $ λ z, ⟨z, mem_insert_of_mem z.2⟩,
    .. },
  { intro y, by_cases h : ↑y = x,
    simp only [subtype.ext_iff, h, option.elim, dif_pos, subtype.coe_mk],
    simp only [h, option.elim, dif_neg, not_false_iff, subtype.coe_eta, subtype.coe_mk] },
  { rintro (_|y), simp only [option.elim, dif_pos, subtype.coe_mk],
    have : ↑y ≠ x, { rintro ⟨⟩, exact h y.2 },
    simp only [this, option.elim, subtype.eta, dif_neg, not_false_iff, subtype.coe_eta,
      subtype.coe_mk] },
end

/-! ### Lattice structure -/

/-- `s ∪ t` is the set such that `a ∈ s ∪ t` iff `a ∈ s` or `a ∈ t`. -/
instance : has_union (finset α) := ⟨λ s t, ⟨_, nodup_ndunion s.1 t.2⟩⟩

/-- `s ∩ t` is the set such that `a ∈ s ∩ t` iff `a ∈ s` and `a ∈ t`. -/
instance : has_inter (finset α) := ⟨λ s t, ⟨_, nodup_ndinter t.1 s.2⟩⟩

instance : lattice (finset α) :=
{ sup          := (∪),
  sup_le       := λ s t u hs ht a ha, (mem_ndunion.1 ha).elim (λ h, hs h) (λ h, ht h),
  le_sup_left  := λ s t a h, mem_ndunion.2 $ or.inl h,
  le_sup_right := λ s t a h, mem_ndunion.2 $ or.inr h,
  inf          := (∩),
  le_inf       := λ s t u ht hu a h, mem_ndinter.2 ⟨ht h, hu h⟩,
  inf_le_left  := λ s t a h, (mem_ndinter.1 h).1,
  inf_le_right := λ s t a h, (mem_ndinter.1 h).2,
  ..finset.partial_order }

/-! #### union -/

@[simp] lemma sup_eq_union : ((⊔) : finset α → finset α → finset α) = (∪) := rfl
@[simp] lemma inf_eq_inter : ((⊓) : finset α → finset α → finset α) = (∩) := rfl

lemma union_val_nd (s t : finset α) : (s ∪ t).1 = ndunion s.1 t.1 := rfl

@[simp] lemma union_val (s t : finset α) : (s ∪ t).1 = s.1 ∪ t.1 := ndunion_eq_union s.2
@[simp] lemma mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t := mem_ndunion
@[simp] lemma disj_union_eq_union (s t h) : @disj_union α s t h = s ∪ t := ext $ λ a, by simp

lemma mem_union_left (t : finset α) (h : a ∈ s) : a ∈ s ∪ t := mem_union.2 $ or.inl h
lemma mem_union_right (s : finset α) (h : a ∈ t) : a ∈ s ∪ t := mem_union.2 $ or.inr h

lemma forall_mem_union {p : α → Prop} : (∀ a ∈ s ∪ t, p a) ↔ (∀ a ∈ s, p a) ∧ ∀ a ∈ t, p a :=
⟨λ h, ⟨λ a, h a ∘ mem_union_left _, λ b, h b ∘ mem_union_right _⟩,
 λ h ab hab, (mem_union.mp hab).elim (h.1 _) (h.2 _)⟩

lemma not_mem_union : a ∉ s ∪ t ↔ a ∉ s ∧ a ∉ t := by rw [mem_union, not_or_distrib]

@[simp, norm_cast]
lemma coe_union (s₁ s₂ : finset α) : ↑(s₁ ∪ s₂) = (s₁ ∪ s₂ : set α) := set.ext $ λ x, mem_union

lemma union_subset (hs : s ⊆ u) : t ⊆ u → s ∪ t ⊆ u := sup_le $ le_iff_subset.2 hs

theorem subset_union_left (s₁ s₂ : finset α) : s₁ ⊆ s₁ ∪ s₂ := λ x, mem_union_left _
theorem subset_union_right (s₁ s₂ : finset α) : s₂ ⊆ s₁ ∪ s₂ := λ x, mem_union_right _

lemma union_subset_union (hsu : s ⊆ u) (htv : t ⊆ v) : s ∪ t ⊆ u ∪ v :=
sup_le_sup (le_iff_subset.2 hsu) htv

lemma union_comm (s₁ s₂ : finset α) : s₁ ∪ s₂ = s₂ ∪ s₁ := sup_comm

instance : is_commutative (finset α) (∪) := ⟨union_comm⟩

@[simp] lemma union_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∪ s₂) ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) := sup_assoc

instance : is_associative (finset α) (∪) := ⟨union_assoc⟩

@[simp] lemma union_idempotent (s : finset α) : s ∪ s = s := sup_idem

instance : is_idempotent (finset α) (∪) := ⟨union_idempotent⟩

lemma union_subset_left (h : s ∪ t ⊆ u) : s ⊆ u := (subset_union_left _ _).trans  h

lemma union_subset_right {s t u : finset α} (h : s ∪ t ⊆ u) : t ⊆ u :=
subset.trans (subset_union_right _ _) h

lemma union_left_comm (s t u : finset α) : s ∪ (t ∪ u) = t ∪ (s ∪ u) :=
ext $ λ _, by simp only [mem_union, or.left_comm]

lemma union_right_comm (s t u : finset α) : (s ∪ t) ∪ u = (s ∪ u) ∪ t :=
ext $ λ x, by simp only [mem_union, or_assoc, or_comm (x ∈ t)]

theorem union_self (s : finset α) : s ∪ s = s := union_idempotent s

@[simp] theorem union_empty (s : finset α) : s ∪ ∅ = s :=
ext $ λ x, mem_union.trans $ or_false _

@[simp] theorem empty_union (s : finset α) : ∅ ∪ s = s :=
ext $ λ x, mem_union.trans $ false_or _

theorem insert_eq (a : α) (s : finset α) : insert a s = {a} ∪ s := rfl

@[simp] theorem insert_union (a : α) (s t : finset α) : insert a s ∪ t = insert a (s ∪ t) :=
by simp only [insert_eq, union_assoc]

@[simp] theorem union_insert (a : α) (s t : finset α) : s ∪ insert a t = insert a (s ∪ t) :=
by simp only [insert_eq, union_left_comm]

lemma insert_union_distrib (a : α) (s t : finset α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
by simp only [insert_union, union_insert, insert_idem]

@[simp] lemma union_eq_left_iff_subset {s t : finset α} : s ∪ t = s ↔ t ⊆ s := sup_eq_left
@[simp] lemma left_eq_union_iff_subset {s t : finset α} : s = s ∪ t ↔ t ⊆ s :=
by rw [← union_eq_left_iff_subset, eq_comm]

@[simp] lemma union_eq_right_iff_subset {s t : finset α} : s ∪ t = t ↔ s ⊆ t := sup_eq_right
@[simp] lemma right_eq_union_iff_subset {s t : finset α} : s = t ∪ s ↔ t ⊆ s :=
by rw [← union_eq_right_iff_subset, eq_comm]

/--
To prove a relation on pairs of `finset X`, it suffices to show that it is
  * symmetric,
  * it holds when one of the `finset`s is empty,
  * it holds for pairs of singletons,
  * if it holds for `[a, c]` and for `[b, c]`, then it holds for `[a ∪ b, c]`.
-/
lemma induction_on_union (P : finset α → finset α → Prop)
  (symm : ∀ {a b}, P a b → P b a)
  (empty_right : ∀ {a}, P a ∅)
  (singletons : ∀ {a b}, P {a} {b})
  (union_of : ∀ {a b c}, P a c → P b c → P (a ∪ b) c) :
  ∀ a b, P a b :=
begin
  intros a b,
  refine finset.induction_on b empty_right (λ x s xs hi, symm _),
  rw finset.insert_eq,
  apply union_of _ (symm hi),
  refine finset.induction_on a empty_right (λ a t ta hi, symm _),
  rw finset.insert_eq,
  exact union_of singletons (symm hi),
end

lemma exists_mem_subset_of_subset_bUnion_of_directed_on {α ι : Type*}
  {f : ι → set α}  {c : set ι} {a : ι} (hac : a ∈ c) (hc : directed_on (λ i j, f i ⊆ f j) c)
  {s : finset α} (hs : (s : set α) ⊆ ⋃ i ∈ c, f i) : ∃ i ∈ c, (s : set α) ⊆ f i :=
begin
  classical,
  revert hs,
  apply s.induction_on,
  { intros,
    use [a, hac],
    simp },
  { intros b t hbt htc hbtc,
    obtain ⟨i : ι , hic : i ∈ c, hti : (t : set α) ⊆ f i⟩ :=
      htc (set.subset.trans (t.subset_insert b) hbtc),
    obtain ⟨j, hjc, hbj⟩ : ∃ j ∈ c, b ∈ f j,
      by simpa [set.mem_Union₂] using hbtc (t.mem_insert_self b),
    rcases hc j hjc i hic with ⟨k, hkc, hk, hk'⟩,
    use [k, hkc],
    rw [coe_insert, set.insert_subset],
    exact ⟨hk hbj, trans hti hk'⟩ }
end

/-! #### inter -/

theorem inter_val_nd (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = ndinter s₁.1 s₂.1 := rfl

@[simp] lemma inter_val (s₁ s₂ : finset α) : (s₁ ∩ s₂).1 = s₁.1 ∩ s₂.1 := ndinter_eq_inter s₁.2

@[simp] theorem mem_inter {a : α} {s₁ s₂ : finset α} : a ∈ s₁ ∩ s₂ ↔ a ∈ s₁ ∧ a ∈ s₂ := mem_ndinter

theorem mem_of_mem_inter_left {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) :
  a ∈ s₁ := (mem_inter.1 h).1

theorem mem_of_mem_inter_right {a : α} {s₁ s₂ : finset α} (h : a ∈ s₁ ∩ s₂) :
  a ∈ s₂ := (mem_inter.1 h).2

theorem mem_inter_of_mem {a : α} {s₁ s₂ : finset α} : a ∈ s₁ → a ∈ s₂ → a ∈ s₁ ∩ s₂ :=
and_imp.1 mem_inter.2

theorem inter_subset_left (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₁ := λ a, mem_of_mem_inter_left

theorem inter_subset_right (s₁ s₂ : finset α) : s₁ ∩ s₂ ⊆ s₂ := λ a, mem_of_mem_inter_right

lemma subset_inter {s₁ s₂ u : finset α} : s₁ ⊆ s₂ → s₁ ⊆ u → s₁ ⊆ s₂ ∩ u :=
by simp only [subset_iff, mem_inter] {contextual:=tt}; intros; split; trivial

@[simp, norm_cast]
lemma coe_inter (s₁ s₂ : finset α) : ↑(s₁ ∩ s₂) = (s₁ ∩ s₂ : set α) := set.ext $ λ _, mem_inter

@[simp] theorem union_inter_cancel_left {s t : finset α} : (s ∪ t) ∩ s = s :=
by rw [← coe_inj, coe_inter, coe_union, set.union_inter_cancel_left]

@[simp] theorem union_inter_cancel_right {s t : finset α} : (s ∪ t) ∩ t = t :=
by rw [← coe_inj, coe_inter, coe_union, set.union_inter_cancel_right]

theorem inter_comm (s₁ s₂ : finset α) : s₁ ∩ s₂ = s₂ ∩ s₁ :=
ext $ λ _, by simp only [mem_inter, and_comm]

@[simp] theorem inter_assoc (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = s₁ ∩ (s₂ ∩ s₃) :=
ext $ λ _, by simp only [mem_inter, and_assoc]

theorem inter_left_comm (s₁ s₂ s₃ : finset α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
ext $ λ _, by simp only [mem_inter, and.left_comm]

theorem inter_right_comm (s₁ s₂ s₃ : finset α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
ext $ λ _, by simp only [mem_inter, and.right_comm]

@[simp] lemma inter_self (s : finset α) : s ∩ s = s := ext $ λ _, mem_inter.trans $ and_self _
@[simp] lemma inter_empty (s : finset α) : s ∩ ∅ = ∅ := ext $ λ _, mem_inter.trans $ and_false _
@[simp] lemma empty_inter (s : finset α) : ∅ ∩ s = ∅ := ext $ λ _, mem_inter.trans $ false_and _

@[simp] lemma inter_union_self (s t : finset α) : s ∩ (t ∪ s) = s :=
by rw [inter_comm, union_inter_cancel_right]

@[simp] theorem insert_inter_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₂) :
  insert a s₁ ∩ s₂ = insert a (s₁ ∩ s₂) :=
ext $ λ x, have x = a ∨ x ∈ s₂ ↔ x ∈ s₂, from or_iff_right_of_imp $ by rintro rfl; exact h,
by simp only [mem_inter, mem_insert, or_and_distrib_left, this]

@[simp] theorem inter_insert_of_mem {s₁ s₂ : finset α} {a : α} (h : a ∈ s₁) :
  s₁ ∩ insert a s₂ = insert a (s₁ ∩ s₂) :=
by rw [inter_comm, insert_inter_of_mem h, inter_comm]

@[simp] theorem insert_inter_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₂) :
  insert a s₁ ∩ s₂ = s₁ ∩ s₂ :=
ext $ λ x, have ¬ (x = a ∧ x ∈ s₂), by rintro ⟨rfl, H⟩; exact h H,
by simp only [mem_inter, mem_insert, or_and_distrib_right, this, false_or]

@[simp] theorem inter_insert_of_not_mem {s₁ s₂ : finset α} {a : α} (h : a ∉ s₁) :
  s₁ ∩ insert a s₂ = s₁ ∩ s₂ :=
by rw [inter_comm, insert_inter_of_not_mem h, inter_comm]

@[simp] theorem singleton_inter_of_mem {a : α} {s : finset α} (H : a ∈ s) : {a} ∩ s = {a} :=
show insert a ∅ ∩ s = insert a ∅, by rw [insert_inter_of_mem H, empty_inter]

@[simp] theorem singleton_inter_of_not_mem {a : α} {s : finset α} (H : a ∉ s) : {a} ∩ s = ∅ :=
eq_empty_of_forall_not_mem $ by simp only [mem_inter, mem_singleton]; rintro x ⟨rfl, h⟩; exact H h

@[simp] theorem inter_singleton_of_mem {a : α} {s : finset α} (h : a ∈ s) : s ∩ {a} = {a} :=
by rw [inter_comm, singleton_inter_of_mem h]

@[simp] theorem inter_singleton_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : s ∩ {a} = ∅ :=
by rw [inter_comm, singleton_inter_of_not_mem h]

@[mono]
lemma inter_subset_inter {x y s t : finset α} (h : x ⊆ y) (h' : s ⊆ t) : x ∩ s ⊆ y ∩ t :=
begin
  intros a a_in,
  rw finset.mem_inter at a_in ⊢,
  exact ⟨h a_in.1, h' a_in.2⟩
end

lemma inter_subset_inter_left (h : t ⊆ u) : s ∩ t ⊆ s ∩ u := inter_subset_inter subset.rfl h
lemma inter_subset_inter_right (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := inter_subset_inter h subset.rfl

instance {α : Type u} : order_bot (finset α) :=
{ bot := ∅, bot_le := empty_subset }

@[simp] lemma bot_eq_empty {α : Type u} : (⊥ : finset α) = ∅ := rfl

instance : distrib_lattice (finset α) :=
{ le_sup_inf := assume a b c, show (a ∪ b) ∩ (a ∪ c) ⊆ a ∪ b ∩ c,
    by simp only [subset_iff, mem_inter, mem_union, and_imp, or_imp_distrib] {contextual:=tt};
    simp only [true_or, imp_true_iff, true_and, or_true],
  ..finset.lattice }

@[simp] theorem union_left_idem (s t : finset α) : s ∪ (s ∪ t) = s ∪ t := sup_left_idem

@[simp] theorem union_right_idem (s t : finset α) : s ∪ t ∪ t = s ∪ t := sup_right_idem
@[simp] theorem inter_left_idem (s t : finset α) : s ∩ (s ∩ t) = s ∩ t := inf_left_idem

@[simp] theorem inter_right_idem (s t : finset α) : s ∩ t ∩ t = s ∩ t := inf_right_idem

theorem inter_distrib_left (s t u : finset α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := inf_sup_left

theorem inter_distrib_right (s t u : finset α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := inf_sup_right

theorem union_distrib_left (s t u : finset α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) := sup_inf_left

theorem union_distrib_right (s t u : finset α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) := sup_inf_right

lemma union_eq_empty_iff (A B : finset α) : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := sup_eq_bot_iff

lemma union_subset_iff : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u := (sup_le_iff : s ⊔ t ≤ u ↔ s ≤ u ∧ t ≤ u)
lemma subset_inter_iff : s ⊆ t ∩ u ↔ s ⊆ t ∧ s ⊆ u := (le_inf_iff : s ≤ t ⊓ u ↔ s ≤ t ∧ s ≤ u)

lemma inter_eq_left_iff_subset (s t : finset α) : s ∩ t = s ↔ s ⊆ t := inf_eq_left
lemma inter_eq_right_iff_subset (s t : finset α) : t ∩ s = s ↔ s ⊆ t := inf_eq_right

lemma ite_subset_union (s s' : finset α) (P : Prop) [decidable P] :
  ite P s s' ⊆ s ∪ s' := ite_le_sup s s' P

lemma inter_subset_ite (s s' : finset α) (P : Prop) [decidable P] :
  s ∩ s' ⊆ ite P s s' := inf_le_ite s s' P

/-! ### erase -/

/-- `erase s a` is the set `s - {a}`, that is, the elements of `s` which are
  not equal to `a`. -/
def erase (s : finset α) (a : α) : finset α := ⟨_, nodup_erase_of_nodup a s.2⟩

@[simp] theorem erase_val (s : finset α) (a : α) : (erase s a).1 = s.1.erase a := rfl

@[simp] theorem mem_erase {a b : α} {s : finset α} : a ∈ erase s b ↔ a ≠ b ∧ a ∈ s :=
mem_erase_iff_of_nodup s.2

theorem not_mem_erase (a : α) (s : finset α) : a ∉ erase s a := mem_erase_of_nodup s.2

-- While this can be solved by `simp`, this lemma is eligible for `dsimp`
@[nolint simp_nf, simp] theorem erase_empty (a : α) : erase ∅ a = ∅ := rfl

@[simp] lemma erase_singleton (a : α) : ({a} : finset α).erase a = ∅ :=
begin
  ext x,
  rw [mem_erase, mem_singleton, not_and_self],
  refl,
end

lemma ne_of_mem_erase : b ∈ erase s a → b ≠ a := λ h, (mem_erase.1 h).1
lemma mem_of_mem_erase : b ∈ erase s a → b ∈ s := mem_of_mem_erase

lemma mem_erase_of_ne_of_mem : a ≠ b → a ∈ s → a ∈ erase s b :=
by simp only [mem_erase]; exact and.intro

/-- An element of `s` that is not an element of `erase s a` must be
`a`. -/
lemma eq_of_mem_of_not_mem_erase (hs : b ∈ s) (hsa : b ∉ s.erase a) : b = a :=
begin
  rw [mem_erase, not_and] at hsa,
  exact not_imp_not.mp hsa hs
end

theorem erase_insert {a : α} {s : finset α} (h : a ∉ s) : erase (insert a s) a = s :=
ext $ assume x, by simp only [mem_erase, mem_insert, and_or_distrib_left, not_and_self, false_or];
apply and_iff_right_of_imp; rintro H rfl; exact h H

theorem insert_erase {a : α} {s : finset α} (h : a ∈ s) : insert a (erase s a) = s :=
ext $ assume x, by simp only [mem_insert, mem_erase, or_and_distrib_left, dec_em, true_and];
apply or_iff_right_of_imp; rintro rfl; exact h

theorem erase_subset_erase (a : α) {s t : finset α} (h : s ⊆ t) : erase s a ⊆ erase t a :=
val_le_iff.1 $ erase_le_erase _ $ val_le_iff.2 h

theorem erase_subset (a : α) (s : finset α) : erase s a ⊆ s := erase_subset _ _

lemma subset_erase {a : α} {s t : finset α} : s ⊆ t.erase a ↔ s ⊆ t ∧ a ∉ s :=
⟨λ h, ⟨h.trans (erase_subset _ _), λ ha, not_mem_erase _ _ (h ha)⟩,
  λ h b hb, mem_erase.2 ⟨ne_of_mem_of_not_mem hb h.2, h.1 hb⟩⟩

@[simp, norm_cast] lemma coe_erase (a : α) (s : finset α) : ↑(erase s a) = (s \ {a} : set α) :=
set.ext $ λ _, mem_erase.trans $ by rw [and_comm, set.mem_diff, set.mem_singleton_iff]; refl

lemma erase_ssubset {a : α} {s : finset α} (h : a ∈ s) : s.erase a ⊂ s :=
calc s.erase a ⊂ insert a (s.erase a) : ssubset_insert $ not_mem_erase _ _
  ... = _ : insert_erase h

@[simp]
theorem erase_eq_of_not_mem {a : α} {s : finset α} (h : a ∉ s) : erase s a = s :=
eq_of_veq $ erase_of_not_mem h

lemma erase_idem {a : α} {s : finset α} : erase (erase s a) a = erase s a :=
by simp

lemma erase_right_comm {a b : α} {s : finset α} : erase (erase s a) b = erase (erase s b) a :=
by { ext x, simp only [mem_erase, ←and_assoc], rw and_comm (x ≠ a) }

theorem subset_insert_iff {a : α} {s t : finset α} : s ⊆ insert a t ↔ erase s a ⊆ t :=
by simp only [subset_iff, or_iff_not_imp_left, mem_erase, mem_insert, and_imp];
exact forall_congr (λ x, forall_swap)

theorem erase_insert_subset (a : α) (s : finset α) : erase (insert a s) a ⊆ s :=
subset_insert_iff.1 $ subset.rfl

theorem insert_erase_subset (a : α) (s : finset α) : s ⊆ insert a (erase s a) :=
subset_insert_iff.2 $ subset.rfl

lemma erase_inj {x y : α} (s : finset α) (hx : x ∈ s) : s.erase x = s.erase y ↔ x = y :=
begin
  refine ⟨λ h, _, congr_arg _⟩,
  rw eq_of_mem_of_not_mem_erase hx,
  rw ←h,
  simp,
end

lemma erase_inj_on (s : finset α) : set.inj_on s.erase s := λ _ _ _ _, (erase_inj s ‹_›).mp

/-! ### sdiff -/

/-- `s \ t` is the set consisting of the elements of `s` that are not in `t`. -/
instance : has_sdiff (finset α) := ⟨λs₁ s₂, ⟨s₁.1 - s₂.1, nodup_of_le tsub_le_self s₁.2⟩⟩

@[simp] lemma sdiff_val (s₁ s₂ : finset α) : (s₁ \ s₂).val = s₁.val - s₂.val := rfl

@[simp] theorem mem_sdiff : a ∈ s \ t ↔ a ∈ s ∧ a ∉ t := mem_sub_of_nodup s.2

@[simp] theorem inter_sdiff_self (s₁ s₂ : finset α) : s₁ ∩ (s₂ \ s₁) = ∅ :=
eq_empty_of_forall_not_mem $
by simp only [mem_inter, mem_sdiff]; rintro x ⟨h, _, hn⟩; exact hn h

instance : generalized_boolean_algebra (finset α) :=
{ sup_inf_sdiff := λ x y, by { simp only [ext_iff, mem_union, mem_sdiff, inf_eq_inter, sup_eq_union,
      mem_inter], tauto },
  inf_inf_sdiff := λ x y, by { simp only [ext_iff, inter_sdiff_self, inter_empty, inter_assoc,
      false_iff, inf_eq_inter, not_mem_empty], tauto },
  ..finset.has_sdiff,
  ..finset.distrib_lattice,
  ..finset.order_bot }

lemma not_mem_sdiff_of_mem_right (h : a ∈ t) : a ∉ s \ t :=
by simp only [mem_sdiff, h, not_true, not_false_iff, and_false]

lemma union_sdiff_of_subset (h : s ⊆ t) : s ∪ (t \ s) = t := sup_sdiff_cancel_right h

theorem sdiff_union_of_subset {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : (s₂ \ s₁) ∪ s₁ = s₂ :=
(union_comm _ _).trans (union_sdiff_of_subset h)

lemma inter_sdiff (s t u : finset α) : s ∩ (t \ u) = s ∩ t \ u := by { ext x, simp [and_assoc] }

@[simp] lemma sdiff_inter_self (s₁ s₂ : finset α) : (s₂ \ s₁) ∩ s₁ = ∅ := inf_sdiff_self_left

@[simp] lemma sdiff_self (s₁ : finset α) : s₁ \ s₁ = ∅ := sdiff_self

lemma sdiff_inter_distrib_right (s t u : finset α) : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := sdiff_inf

@[simp] lemma sdiff_inter_self_left (s t : finset α) : s \ (s ∩ t) = s \ t := sdiff_inf_self_left
@[simp] lemma sdiff_inter_self_right (s t : finset α) : s \ (t ∩ s) = s \ t := sdiff_inf_self_right

@[simp] lemma sdiff_empty : s \ ∅ = s := sdiff_bot

@[mono] lemma sdiff_subset_sdiff (hst : s ⊆ t) (hvu : v ⊆ u) : s \ u ⊆ t \ v :=
sdiff_le_sdiff ‹s ≤ t› ‹v ≤ u›

@[simp, norm_cast] lemma coe_sdiff (s₁ s₂ : finset α) : ↑(s₁ \ s₂) = (s₁ \ s₂ : set α) :=
set.ext $ λ _, mem_sdiff

@[simp] theorem union_sdiff_self_eq_union : s ∪ (t \ s) = s ∪ t := sup_sdiff_self_right

@[simp] theorem sdiff_union_self_eq_union : (s \ t) ∪ t = s ∪ t := sup_sdiff_self_left

lemma union_sdiff_symm : s ∪ (t \ s) = t ∪ (s \ t) := sup_sdiff_symm

lemma sdiff_union_inter (s t : finset α) : (s \ t) ∪ (s ∩ t) = s := sup_sdiff_inf _ _

@[simp] lemma sdiff_idem (s t : finset α) : s \ t \ t = s \ t := sdiff_idem

lemma sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t := sdiff_eq_bot_iff

@[simp] lemma empty_sdiff (s : finset α) : ∅ \ s = ∅ := bot_sdiff

lemma insert_sdiff_of_not_mem (s : finset α) {t : finset α} {x : α} (h : x ∉ t) :
  (insert x s) \ t = insert x (s \ t) :=
begin
  rw [← coe_inj, coe_insert, coe_sdiff, coe_sdiff, coe_insert],
  exact set.insert_diff_of_not_mem s h
end

lemma insert_sdiff_of_mem (s : finset α) {x : α} (h : x ∈ t) : (insert x s) \ t = s \ t :=
begin
  rw [← coe_inj, coe_sdiff, coe_sdiff, coe_insert],
  exact set.insert_diff_of_mem s h
end

@[simp] lemma insert_sdiff_insert (s t : finset α) (x : α) :
  (insert x s) \ (insert x t) = s \ insert x t :=
insert_sdiff_of_mem _ (mem_insert_self _ _)

lemma sdiff_insert_of_not_mem {x : α} (h : x ∉ s) (t : finset α) : s \ (insert x t) = s \ t :=
begin
  refine subset.antisymm (sdiff_subset_sdiff (subset.refl _) (subset_insert _ _)) (λ y hy, _),
  simp only [mem_sdiff, mem_insert, not_or_distrib] at hy ⊢,
  exact ⟨hy.1, λ hxy, h $ hxy ▸ hy.1, hy.2⟩
end

@[simp] lemma sdiff_subset (s t : finset α) : s \ t ⊆ s := show s \ t ≤ s, from sdiff_le

lemma sdiff_ssubset (h : t ⊆ s) (ht : t.nonempty) : s \ t ⊂ s := sdiff_lt ‹t ≤ s› ht.ne_empty

lemma union_sdiff_distrib (s₁ s₂ t : finset α) : (s₁ ∪ s₂) \ t = s₁ \ t ∪ s₂ \ t := sup_sdiff
lemma sdiff_union_distrib (s t₁ t₂ : finset α) : s \ (t₁ ∪ t₂) = (s \ t₁) ∩ (s \ t₂) := sdiff_sup

lemma union_sdiff_self (s t : finset α) : (s ∪ t) \ t = s \ t := sup_sdiff_right_self

lemma sdiff_singleton_eq_erase (a : α) (s : finset α) : s \ singleton a = erase s a :=
by { ext, rw [mem_erase, mem_sdiff, mem_singleton], tauto }

@[simp] lemma sdiff_singleton_not_mem_eq_self (s : finset α) {a : α} (ha : a ∉ s) : s \ {a} = s :=
by simp only [sdiff_singleton_eq_erase, ha, erase_eq_of_not_mem, not_false_iff]

lemma sdiff_erase {x : α} (hx : x ∈ s) : s \ s.erase x = {x} :=
begin
  rw [← sdiff_singleton_eq_erase, sdiff_sdiff_right_self],
  exact inf_eq_right.2 (singleton_subset_iff.2 hx),
end

lemma sdiff_sdiff_self_left (s t : finset α) : s \ (s \ t) = s ∩ t := sdiff_sdiff_right_self

lemma sdiff_sdiff_eq_self (h : t ⊆ s) : s \ (s \ t) = t := sdiff_sdiff_eq_self h

lemma sdiff_eq_sdiff_iff_inter_eq_inter {s t₁ t₂ : finset α} : s \ t₁ = s \ t₂ ↔ s ∩ t₁ = s ∩ t₂ :=
sdiff_eq_sdiff_iff_inf_eq_inf

lemma union_eq_sdiff_union_sdiff_union_inter (s t : finset α) :
  s ∪ t = (s \ t) ∪ (t \ s) ∪ (s ∩ t) :=
sup_eq_sdiff_sup_sdiff_sup_inf

lemma erase_eq_empty_iff (s : finset α) (a : α) : s.erase a = ∅ ↔ s = ∅ ∨ s = {a} :=
by rw [←sdiff_singleton_eq_erase, sdiff_eq_empty_iff_subset, subset_singleton_iff]

end decidable_eq

/-! ### attach -/

/-- `attach s` takes the elements of `s` and forms a new set of elements of the subtype
`{x // x ∈ s}`. -/
def attach (s : finset α) : finset {x // x ∈ s} := ⟨attach s.1, nodup_attach.2 s.2⟩

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {s : finset α} (hx : x ∈ s) :
  sizeof x < sizeof s := by
{ cases s, dsimp [sizeof, has_sizeof.sizeof, finset.sizeof],
  apply lt_add_left, exact multiset.sizeof_lt_sizeof_of_mem hx }

@[simp] theorem attach_val (s : finset α) : s.attach.1 = s.1.attach := rfl

@[simp] theorem mem_attach (s : finset α) : ∀ x, x ∈ s.attach := mem_attach _

@[simp] theorem attach_empty : attach (∅ : finset α) = ∅ := rfl

@[simp] lemma attach_nonempty_iff (s : finset α) : s.attach.nonempty ↔ s.nonempty :=
by simp [finset.nonempty]

@[simp] lemma attach_eq_empty_iff (s : finset α) : s.attach = ∅ ↔ s = ∅ :=
by simpa [eq_empty_iff_forall_not_mem]

/-! ### piecewise -/

section piecewise

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise {α : Type*} {δ : α → Sort*} (s : finset α) (f g : Π i, δ i) [Π j, decidable (j ∈ s)] :
  Π i, δ i :=
λi, if i ∈ s then f i else g i

variables {δ : α → Sort*} (s : finset α) (f g : Π i, δ i)

@[simp] lemma piecewise_insert_self [decidable_eq α] {j : α} [∀ i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g j = f j :=
by simp [piecewise]

@[simp] lemma piecewise_empty [Π i : α, decidable (i ∈ (∅ : finset α))] : piecewise ∅ f g = g :=
by { ext i, simp [piecewise] }

variable [Π j, decidable (j ∈ s)]

-- TODO: fix this in norm_cast
@[norm_cast move] lemma piecewise_coe [∀ j, decidable (j ∈ (s : set α))] :
  (s : set α).piecewise f g = s.piecewise f g :=
by { ext, congr }

@[simp, priority 980]
lemma piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i := by simp [piecewise, hi]

@[simp, priority 980]
lemma piecewise_eq_of_not_mem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
by simp [piecewise, hi]

lemma piecewise_congr {f f' g g' : Π i, δ i} (hf : ∀ i ∈ s, f i = f' i) (hg : ∀ i ∉ s, g i = g' i) :
  s.piecewise f g = s.piecewise f' g' :=
funext $ λ i, if_ctx_congr iff.rfl (hf i) (hg i)

@[simp, priority 990]
lemma piecewise_insert_of_ne [decidable_eq α] {i j : α} [∀ i, decidable (i ∈ insert j s)]
  (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i :=
by simp [piecewise, h]

lemma piecewise_insert [decidable_eq α] (j : α) [∀ i, decidable (i ∈ insert j s)] :
  (insert j s).piecewise f g = update (s.piecewise f g) j (f j) :=
by { classical, simp only [← piecewise_coe, coe_insert, ← set.piecewise_insert] }

lemma piecewise_cases {i} (p : δ i → Prop) (hf : p (f i)) (hg : p (g i)) : p (s.piecewise f g i) :=
by by_cases hi : i ∈ s; simpa [hi]

lemma piecewise_mem_set_pi {δ : α → Type*} {t : set α} {t' : Π i, set (δ i)}
  {f g} (hf : f ∈ set.pi t t') (hg : g ∈ set.pi t t') : s.piecewise f g ∈ set.pi t t' :=
by { classical, rw ← piecewise_coe, exact set.piecewise_mem_pi ↑s hf hg }

lemma piecewise_singleton [decidable_eq α] (i : α) :
  piecewise {i} f g = update g i (f i) :=
by rw [← insert_emptyc_eq, piecewise_insert, piecewise_empty]

lemma piecewise_piecewise_of_subset_left {s t : finset α} [Π i, decidable (i ∈ s)]
  [Π i, decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : Π a, δ a) :
  s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
s.piecewise_congr (λ i hi, piecewise_eq_of_mem _ _ _ (h hi)) (λ _ _, rfl)

@[simp] lemma piecewise_idem_left (f₁ f₂ g : Π a, δ a) :
  s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
piecewise_piecewise_of_subset_left (subset.refl _) _ _ _

lemma piecewise_piecewise_of_subset_right {s t : finset α} [Π i, decidable (i ∈ s)]
  [Π i, decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : Π a, δ a) :
  s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
s.piecewise_congr (λ _ _, rfl) (λ i hi, t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi))

@[simp] lemma piecewise_idem_right (f g₁ g₂ : Π a, δ a) :
  s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
piecewise_piecewise_of_subset_right (subset.refl _) f g₁ g₂

lemma update_eq_piecewise {β : Type*} [decidable_eq α] (f : α → β) (i : α) (v : β) :
  update f i v = piecewise (singleton i) (λj, v) f :=
(piecewise_singleton _ _ _).symm

lemma update_piecewise [decidable_eq α] (i : α) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) :=
begin
  ext j,
  rcases em (j = i) with (rfl|hj); by_cases hs : j ∈ s; simp *
end

lemma update_piecewise_of_mem [decidable_eq α] {i : α} (hi : i ∈ s) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise (update f i v) g :=
begin
  rw update_piecewise,
  refine s.piecewise_congr (λ _ _, rfl) (λ j hj, update_noteq _ _ _),
  exact λ h, hj (h.symm ▸ hi)
end

lemma update_piecewise_of_not_mem [decidable_eq α] {i : α} (hi : i ∉ s) (v : δ i) :
  update (s.piecewise f g) i v = s.piecewise f (update g i v) :=
begin
  rw update_piecewise,
  refine s.piecewise_congr (λ j hj, update_noteq _ _ _) (λ _ _, rfl),
  exact λ h, hi (h ▸ hj)
end

lemma piecewise_le_of_le_of_le {δ : α → Type*} [Π i, preorder (δ i)] {f g h : Π i, δ i}
  (Hf : f ≤ h) (Hg : g ≤ h) : s.piecewise f g ≤ h :=
λ x, piecewise_cases s f g (≤ h x) (Hf x) (Hg x)

lemma le_piecewise_of_le_of_le {δ : α → Type*} [Π i, preorder (δ i)] {f g h : Π i, δ i}
  (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ s.piecewise f g :=
λ x, piecewise_cases s f g (λ y, h x ≤ y) (Hf x) (Hg x)

lemma piecewise_le_piecewise' {δ : α → Type*} [Π i, preorder (δ i)] {f g f' g' : Π i, δ i}
  (Hf : ∀ x ∈ s, f x ≤ f' x) (Hg : ∀ x ∉ s, g x ≤ g' x) : s.piecewise f g ≤ s.piecewise f' g' :=
λ x, by { by_cases hx : x ∈ s; simp [hx, *] }

lemma piecewise_le_piecewise {δ : α → Type*} [Π i, preorder (δ i)] {f g f' g' : Π i, δ i}
  (Hf : f ≤ f') (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
s.piecewise_le_piecewise' (λ x _, Hf x) (λ x _, Hg x)

lemma piecewise_mem_Icc_of_mem_of_mem {δ : α → Type*} [Π i, preorder (δ i)] {f f₁ g g₁ : Π i, δ i}
  (hf : f ∈ set.Icc f₁ g₁) (hg : g ∈ set.Icc f₁ g₁) :
  s.piecewise f g ∈ set.Icc f₁ g₁ :=
⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩

lemma piecewise_mem_Icc {δ : α → Type*} [Π i, preorder (δ i)] {f g : Π i, δ i} (h : f ≤ g) :
  s.piecewise f g ∈ set.Icc f g :=
piecewise_mem_Icc_of_mem_of_mem _ (set.left_mem_Icc.2 h) (set.right_mem_Icc.2 h)

lemma piecewise_mem_Icc' {δ : α → Type*} [Π i, preorder (δ i)] {f g : Π i, δ i} (h : g ≤ f) :
  s.piecewise f g ∈ set.Icc g f :=
piecewise_mem_Icc_of_mem_of_mem _ (set.right_mem_Icc.2 h) (set.left_mem_Icc.2 h)

end piecewise

section decidable_pi_exists
variables {s : finset α}

instance decidable_dforall_finset {p : Π a ∈ s, Prop} [hp : ∀ a (h : a ∈ s), decidable (p a h)] :
  decidable (∀ a (h : a ∈ s), p a h) :=
multiset.decidable_dforall_multiset

/-- decidable equality for functions whose domain is bounded by finsets -/
instance decidable_eq_pi_finset {β : α → Type*} [h : ∀ a, decidable_eq (β a)] :
  decidable_eq (Π a ∈ s, β a) :=
multiset.decidable_eq_pi_multiset

instance decidable_dexists_finset {p : Π a ∈ s, Prop} [hp : ∀ a (h : a ∈ s), decidable (p a h)] :
  decidable (∃ a (h : a ∈ s), p a h) :=
multiset.decidable_dexists_multiset

end decidable_pi_exists

/-! ### filter -/
section filter
variables (p q : α → Prop) [decidable_pred p] [decidable_pred q]

/-- `filter p s` is the set of elements of `s` that satisfy `p`. -/
def filter (s : finset α) : finset α :=
⟨_, nodup_filter p s.2⟩

@[simp] theorem filter_val (s : finset α) : (filter p s).1 = s.1.filter p := rfl

@[simp] theorem filter_subset (s : finset α) : s.filter p ⊆ s := filter_subset _ _

variable {p}

@[simp] theorem mem_filter {s : finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := mem_filter

theorem filter_ssubset {s : finset α} : s.filter p ⊂ s ↔ ∃ x ∈ s, ¬ p x :=
⟨λ h, let ⟨x, hs, hp⟩ := set.exists_of_ssubset h in ⟨x, hs, mt (λ hp, mem_filter.2 ⟨hs, hp⟩) hp⟩,
  λ ⟨x, hs, hp⟩, ⟨s.filter_subset _, λ h, hp (mem_filter.1 (h hs)).2⟩⟩

variable (p)

theorem filter_filter (s : finset α) : (s.filter p).filter q = s.filter (λa, p a ∧ q a) :=
ext $ assume a, by simp only [mem_filter, and_comm, and.left_comm]

lemma filter_true {s : finset α} [h : decidable_pred (λ _, true)] :
  @finset.filter α (λ _, true) h s = s :=
by ext; simp

@[simp] theorem filter_false {h} (s : finset α) : @filter α (λa, false) h s = ∅ :=
ext $ assume a, by simp only [mem_filter, and_false]; refl

variables {p q}

/-- If all elements of a `finset` satisfy the predicate `p`, `s.filter p` is `s`. -/
@[simp] lemma filter_true_of_mem {s : finset α} (h : ∀ x ∈ s, p x) : s.filter p = s :=
ext $ λ x, ⟨λ h, (mem_filter.1 h).1, λ hx, mem_filter.2 ⟨hx, h x hx⟩⟩

/-- If all elements of a `finset` fail to satisfy the predicate `p`, `s.filter p` is `∅`. -/
lemma filter_false_of_mem {s : finset α} (h : ∀ x ∈ s, ¬ p x) : s.filter p = ∅ :=
eq_empty_of_forall_not_mem (by simpa)

lemma filter_congr {s : finset α} (H : ∀ x ∈ s, p x ↔ q x) : filter p s = filter q s :=
eq_of_veq $ filter_congr H

variables (p q)

lemma filter_empty : filter p ∅ = ∅ := subset_empty.1 $ filter_subset _ _

lemma filter_subset_filter {s t : finset α} (h : s ⊆ t) : s.filter p ⊆ t.filter p :=
assume a ha, mem_filter.2 ⟨h (mem_filter.1 ha).1, (mem_filter.1 ha).2⟩

lemma monotone_filter_left (p : α → Prop) [decidable_pred p] : monotone (filter p) :=
λ _ _, filter_subset_filter p

lemma monotone_filter_right (s : finset α) ⦃p q : α → Prop⦄
  [decidable_pred p] [decidable_pred q] (h : p ≤ q) :
  s.filter p ≤ s.filter q :=
multiset.subset_of_le (multiset.monotone_filter_right s.val h)

@[simp, norm_cast] lemma coe_filter (s : finset α) : ↑(s.filter p) = ({x ∈ ↑s | p x} : set α) :=
set.ext $ λ _, mem_filter

theorem filter_singleton (a : α) : filter p (singleton a) = if p a then singleton a else ∅ :=
by { classical, ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

variable [decidable_eq α]

theorem filter_union (s₁ s₂ : finset α) : (s₁ ∪ s₂).filter p = s₁.filter p ∪ s₂.filter p :=
ext $ λ _, by simp only [mem_filter, mem_union, or_and_distrib_right]

theorem filter_union_right (s : finset α) : s.filter p ∪ s.filter q = s.filter (λx, p x ∨ q x) :=
ext $ λ x, by simp only [mem_filter, mem_union, and_or_distrib_left.symm]

lemma filter_mem_eq_inter {s t : finset α} [Π i, decidable (i ∈ t)] :
  s.filter (λ i, i ∈ t) = s ∩ t :=
ext $ λ i, by rw [mem_filter, mem_inter]

theorem filter_inter (s t : finset α) : filter p s ∩ t = filter p (s ∩ t) :=
by { ext, simp only [mem_inter, mem_filter, and.right_comm] }

theorem inter_filter (s t : finset α) : s ∩ filter p t = filter p (s ∩ t) :=
by rw [inter_comm, filter_inter, inter_comm]

theorem filter_insert (a : α) (s : finset α) :
  filter p (insert a s) = if p a then insert a (filter p s) else filter p s :=
by { ext x, simp, split_ifs with h; by_cases h' : x = a; simp [h, h'] }

theorem filter_erase (a : α) (s : finset α) : filter p (erase s a) = erase (filter p s) a :=
by { ext x, simp only [and_assoc, mem_filter, iff_self, mem_erase] }

theorem filter_or [decidable_pred (λ a, p a ∨ q a)] (s : finset α) :
  s.filter (λ a, p a ∨ q a) = s.filter p ∪ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_union, and_or_distrib_left]

theorem filter_and [decidable_pred (λ a, p a ∧ q a)] (s : finset α) :
  s.filter (λ a, p a ∧ q a) = s.filter p ∩ s.filter q :=
ext $ λ _, by simp only [mem_filter, mem_inter, and_comm, and.left_comm, and_self]

theorem filter_not [decidable_pred (λ a, ¬ p a)] (s : finset α) :
  s.filter (λ a, ¬ p a) = s \ s.filter p :=
ext $ by simpa only [mem_filter, mem_sdiff, and_comm, not_and] using λ a, and_congr_right $
  λ h : a ∈ s, (imp_iff_right h).symm.trans imp_not_comm

theorem sdiff_eq_filter (s₁ s₂ : finset α) :
  s₁ \ s₂ = filter (∉ s₂) s₁ := ext $ λ _, by simp only [mem_sdiff, mem_filter]

lemma sdiff_eq_self (s₁ s₂ : finset α) : s₁ \ s₂ = s₁ ↔ s₁ ∩ s₂ ⊆ ∅ :=
by { simp [subset.antisymm_iff],
     split; intro h,
     { transitivity' ((s₁ \ s₂) ∩ s₂), mono, simp },
     { calc  s₁ \ s₂
           ⊇ s₁ \ (s₁ ∩ s₂) : by simp [(⊇)]
       ... ⊇ s₁ \ ∅         : by mono using [(⊇)]
       ... ⊇ s₁             : by simp [(⊇)] } }

theorem filter_union_filter_neg_eq [decidable_pred (λ a, ¬ p a)]
  (s : finset α) : s.filter p ∪ s.filter (λa, ¬ p a) = s :=
by simp only [filter_not, union_sdiff_of_subset (filter_subset p s)]

theorem filter_inter_filter_neg_eq [decidable_pred (λ a, ¬ p a)]
  (s : finset α) : s.filter p ∩ s.filter (λa, ¬ p a) = ∅ :=
by simp only [filter_not, inter_sdiff_self]

lemma subset_union_elim {s : finset α} {t₁ t₂ : set α} (h : ↑s ⊆ t₁ ∪ t₂) :
  ∃ s₁ s₂ : finset α, s₁ ∪ s₂ = s ∧ ↑s₁ ⊆ t₁ ∧ ↑s₂ ⊆ t₂ \ t₁ :=
begin
  classical,
  refine ⟨s.filter (∈ t₁), s.filter (∉ t₁), _, _ , _⟩,
  { simp [filter_union_right, em] },
  { intro x, simp },
  { intro x, simp, intros hx hx₂, refine ⟨or.resolve_left (h hx) hx₂, hx₂⟩ }
end

/- We can simplify an application of filter where the decidability is inferred in "the wrong way" -/
@[simp] lemma filter_congr_decidable {α} (s : finset α) (p : α → Prop) (h : decidable_pred p)
  [decidable_pred p] : @filter α p h s = s.filter p :=
by congr

section classical
open_locale classical
/-- The following instance allows us to write `{x ∈ s | p x}` for `finset.filter p s`.
  Since the former notation requires us to define this for all propositions `p`, and `finset.filter`
  only works for decidable propositions, the notation `{x ∈ s | p x}` is only compatible with
  classical logic because it uses `classical.prop_decidable`.
  We don't want to redo all lemmas of `finset.filter` for `has_sep.sep`, so we make sure that `simp`
  unfolds the notation `{x ∈ s | p x}` to `finset.filter p s`. If `p` happens to be decidable, the
  simp-lemma `finset.filter_congr_decidable` will make sure that `finset.filter` uses the right
  instance for decidability.
-/
noncomputable instance {α : Type*} : has_sep α (finset α) := ⟨λ p x, x.filter p⟩

@[simp] lemma sep_def {α : Type*} (s : finset α) (p : α → Prop) : {x ∈ s | p x} = s.filter p := rfl

end classical

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq'` with the equality the other way.
-/
-- This is not a good simp lemma, as it would prevent `finset.mem_filter` from firing
-- on, e.g. `x ∈ s.filter(eq b)`.
lemma filter_eq [decidable_eq β] (s : finset β) (b : β) : s.filter (eq b) = ite (b ∈ s) {b} ∅ :=
begin
  split_ifs,
  { ext,
    simp only [mem_filter, mem_singleton],
    exact ⟨λ h, h.2.symm, by { rintro ⟨h⟩, exact ⟨h, rfl⟩ }⟩ },
  { ext,
    simp only [mem_filter, not_and, iff_false, not_mem_empty],
    rintro m ⟨e⟩, exact h m }
end

/--
  After filtering out everything that does not equal a given value, at most that value remains.

  This is equivalent to `filter_eq` with the equality the other way.
-/
lemma filter_eq' [decidable_eq β] (s : finset β) (b : β) :
  s.filter (λ a, a = b) = ite (b ∈ s) {b} ∅ :=
trans (filter_congr (λ _ _, ⟨eq.symm, eq.symm⟩)) (filter_eq s b)

lemma filter_ne [decidable_eq β] (s : finset β) (b : β) : s.filter (λ a, b ≠ a) = s.erase b :=
by { ext, simp only [mem_filter, mem_erase, ne.def], tauto }

lemma filter_ne' [decidable_eq β] (s : finset β) (b : β) : s.filter (λ a, a ≠ b) = s.erase b :=
trans (filter_congr (λ _ _, ⟨ne.symm, ne.symm⟩)) (filter_ne s b)

end filter

/-! ### range -/

section range
variables {n m l : ℕ}

/-- `range n` is the set of natural numbers less than `n`. -/
def range (n : ℕ) : finset ℕ := ⟨_, nodup_range n⟩

@[simp] theorem range_coe (n : ℕ) : (range n).1 = multiset.range n := rfl

@[simp] theorem mem_range : m ∈ range n ↔ m < n := mem_range

@[simp] theorem range_zero : range 0 = ∅ := rfl

@[simp] theorem range_one : range 1 = {0} := rfl

theorem range_succ : range (succ n) = insert n (range n) :=
eq_of_veq $ (range_succ n).trans $ (ndinsert_of_not_mem not_mem_range_self).symm

lemma range_add_one : range (n + 1) = insert n (range n) := range_succ

@[simp] theorem not_mem_range_self : n ∉ range n := not_mem_range_self

@[simp] theorem self_mem_range_succ (n : ℕ) : n ∈ range (n + 1) := multiset.self_mem_range_succ n

@[simp] theorem range_subset {n m} : range n ⊆ range m ↔ n ≤ m := range_subset

theorem range_mono : monotone range := λ _ _, range_subset.2

lemma mem_range_succ_iff {a b : ℕ} : a ∈ finset.range b.succ ↔ a ≤ b :=
finset.mem_range.trans nat.lt_succ_iff

lemma mem_range_le {n x : ℕ} (hx : x ∈ range n) : x ≤ n := (mem_range.1 hx).le

lemma mem_range_sub_ne_zero {n x : ℕ} (hx : x ∈ range n) : n - x ≠ 0 :=
ne_of_gt $ tsub_pos_of_lt $ mem_range.1 hx

@[simp] lemma nonempty_range_iff : (range n).nonempty ↔ n ≠ 0 :=
⟨λ ⟨k, hk⟩, ((zero_le k).trans_lt $ mem_range.1 hk).ne',
  λ h, ⟨0, mem_range.2 $ pos_iff_ne_zero.2 h⟩⟩

@[simp] lemma range_eq_empty_iff : range n = ∅ ↔ n = 0 :=
by rw [← not_nonempty_iff_eq_empty, nonempty_range_iff, not_not]

lemma nonempty_range_succ : (range $ n + 1).nonempty :=
nonempty_range_iff.2 n.succ_ne_zero

end range

/- useful rules for calculations with quantifiers -/
theorem exists_mem_empty_iff (p : α → Prop) : (∃ x, x ∈ (∅ : finset α) ∧ p x) ↔ false :=
by simp only [not_mem_empty, false_and, exists_false]

lemma exists_mem_insert [decidable_eq α] (a : α) (s : finset α) (p : α → Prop) :
  (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x :=
by simp only [mem_insert, or_and_distrib_right, exists_or_distrib, exists_eq_left]

theorem forall_mem_empty_iff (p : α → Prop) : (∀ x, x ∈ (∅ : finset α) → p x) ↔ true :=
iff_true_intro $ λ _, false.elim

lemma forall_mem_insert [decidable_eq α] (a : α) (s : finset α) (p : α → Prop) :
  (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x :=
by simp only [mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

end finset

/-- Equivalence between the set of natural numbers which are `≥ k` and `ℕ`, given by `n → n - k`. -/
def not_mem_range_equiv (k : ℕ) : {n // n ∉ range k} ≃ ℕ :=
{ to_fun := λ i, i.1 - k,
  inv_fun := λ j, ⟨j + k, by simp⟩,
  left_inv := λ j,
  begin
    rw subtype.ext_iff_val,
    apply tsub_add_cancel_of_le,
    simpa using j.2
  end,
  right_inv := λ j, add_tsub_cancel_right _ _ }

@[simp] lemma coe_not_mem_range_equiv (k : ℕ) :
  (not_mem_range_equiv k : {n // n ∉ range k} → ℕ) = (λ i, i - k) := rfl

@[simp] lemma coe_not_mem_range_equiv_symm (k : ℕ) :
  ((not_mem_range_equiv k).symm : ℕ → {n // n ∉ range k}) = λ j, ⟨j + k, by simp⟩ := rfl

/-! ### erase_dup on list and multiset -/

namespace multiset
variable [decidable_eq α]

/-- `to_finset s` removes duplicates from the multiset `s` to produce a finset. -/
def to_finset (s : multiset α) : finset α := ⟨_, nodup_erase_dup s⟩

@[simp] theorem to_finset_val (s : multiset α) : s.to_finset.1 = s.erase_dup := rfl

theorem to_finset_eq {s : multiset α} (n : nodup s) : finset.mk s n = s.to_finset :=
finset.val_inj.1 n.erase_dup.symm

lemma nodup.to_finset_inj {l l' : multiset α} (hl : nodup l) (hl' : nodup l')
  (h : l.to_finset = l'.to_finset) : l = l' :=
by simpa [←to_finset_eq hl, ←to_finset_eq hl'] using h

@[simp] lemma mem_to_finset {a : α} {s : multiset α} : a ∈ s.to_finset ↔ a ∈ s := mem_erase_dup

@[simp] lemma to_finset_zero : to_finset (0 : multiset α) = ∅ := rfl

@[simp] lemma to_finset_cons (a : α) (s : multiset α) :
  to_finset (a ::ₘ s) = insert a (to_finset s) :=
finset.eq_of_veq erase_dup_cons

@[simp] lemma to_finset_singleton (a : α) : to_finset ({a} : multiset α) = {a} :=
by rw [singleton_eq_cons, to_finset_cons, to_finset_zero, is_lawful_singleton.insert_emptyc_eq]

@[simp] lemma to_finset_add (s t : multiset α) : to_finset (s + t) = to_finset s ∪ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_nsmul (s : multiset α) :
  ∀ (n : ℕ) (hn : n ≠ 0), (n • s).to_finset = s.to_finset
| 0     h := by contradiction
| (n+1) h :=
  begin
    by_cases n = 0,
    { rw [h, zero_add, one_nsmul] },
    { rw [add_nsmul, to_finset_add, one_nsmul, to_finset_nsmul n h, finset.union_idempotent] }
  end

@[simp] lemma to_finset_inter (s t : multiset α) : to_finset (s ∩ t) = to_finset s ∩ to_finset t :=
finset.ext $ by simp

@[simp] lemma to_finset_union (s t : multiset α) : (s ∪ t).to_finset = s.to_finset ∪ t.to_finset :=
by ext; simp

theorem to_finset_eq_empty {m : multiset α} : m.to_finset = ∅ ↔ m = 0 :=
finset.val_inj.symm.trans multiset.erase_dup_eq_zero

@[simp] lemma to_finset_subset (s t : multiset α) : s.to_finset ⊆ t.to_finset ↔ s ⊆ t :=
by simp only [finset.subset_iff, multiset.subset_iff, multiset.mem_to_finset]

end multiset

namespace finset

@[simp] lemma val_to_finset [decidable_eq α] (s : finset α) : s.val.to_finset = s :=
by { ext, rw [multiset.mem_to_finset, ←mem_def] }

lemma val_le_iff_val_subset {a : finset α} {b : multiset α} : a.val ≤ b ↔ a.val ⊆ b :=
multiset.le_iff_subset a.nodup

end finset

namespace list
variables [decidable_eq α] {l l' : list α} {a : α}

/-- `to_finset l` removes duplicates from the list `l` to produce a finset. -/
def to_finset (l : list α) : finset α := multiset.to_finset l

@[simp] theorem to_finset_val (l : list α) : l.to_finset.1 = (l.erase_dup : multiset α) := rfl

lemma to_finset_eq (n : nodup l) : @finset.mk α l n = l.to_finset := multiset.to_finset_eq n

@[simp] lemma mem_to_finset : a ∈ l.to_finset ↔ a ∈ l := mem_erase_dup
@[simp] lemma to_finset_nil : to_finset (@nil α) = ∅ := rfl

@[simp] lemma to_finset_cons : to_finset (a :: l) = insert a (to_finset l) :=
finset.eq_of_veq $ by by_cases h : a ∈ l; simp [finset.insert_val', multiset.erase_dup_cons, h]

lemma to_finset_surj_on : set.surj_on to_finset {l : list α | l.nodup} set.univ :=
by { rintro ⟨⟨l⟩, hl⟩ _, exact ⟨l, hl, (to_finset_eq hl).symm⟩ }

theorem to_finset_surjective : surjective (to_finset : list α → finset α) :=
λ s, let ⟨l, _, hls⟩ := to_finset_surj_on (set.mem_univ s) in ⟨l, hls⟩

lemma to_finset_eq_iff_perm_erase_dup : l.to_finset = l'.to_finset ↔ l.erase_dup ~ l'.erase_dup :=
by simp [finset.ext_iff, perm_ext (nodup_erase_dup _) (nodup_erase_dup _)]

lemma to_finset.ext_iff {a b : list α} : a.to_finset = b.to_finset ↔ ∀ x, x ∈ a ↔ x ∈ b :=
by simp only [finset.ext_iff, mem_to_finset]

lemma to_finset.ext : (∀ x, x ∈ l ↔ x ∈ l') → l.to_finset = l'.to_finset := to_finset.ext_iff.mpr

lemma to_finset_eq_of_perm (l l' : list α) (h : l ~ l') : l.to_finset = l'.to_finset :=
to_finset_eq_iff_perm_erase_dup.mpr h.erase_dup

lemma perm_of_nodup_nodup_to_finset_eq (hl : nodup l) (hl' : nodup l')
  (h : l.to_finset = l'.to_finset) : l ~ l' :=
by { rw ←multiset.coe_eq_coe, exact multiset.nodup.to_finset_inj hl hl' h }

@[simp] lemma to_finset_append : to_finset (l ++ l') = l.to_finset ∪ l'.to_finset :=
begin
  induction l with hd tl hl,
  { simp },
  { simp [hl] }
end

@[simp] lemma to_finset_reverse {l : list α} : to_finset l.reverse = l.to_finset :=
to_finset_eq_of_perm _ _ (reverse_perm l)

lemma to_finset_repeat_of_ne_zero {n : ℕ} (hn : n ≠ 0) : (list.repeat a n).to_finset = {a} :=
by { ext x, simp [hn, list.mem_repeat] }

@[simp] lemma to_finset_union (l l' : list α) : (l ∪ l').to_finset = l.to_finset ∪ l'.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_inter (l l' : list α) : (l ∩ l').to_finset = l.to_finset ∩ l'.to_finset :=
by { ext, simp }

@[simp] lemma to_finset_eq_empty_iff (l : list α) : l.to_finset = ∅ ↔ l = nil := by cases l; simp

end list

namespace finset

/-! ### map -/
section map
open function

/-- When `f` is an embedding of `α` in `β` and `s` is a finset in `α`, then `s.map f` is the image
finset in `β`. The embedding condition guarantees that there are no duplicates in the image. -/
def map (f : α ↪ β) (s : finset α) : finset β :=
⟨s.1.map f, nodup_map f.2 s.2⟩

@[simp] theorem map_val (f : α ↪ β) (s : finset α) : (map f s).1 = s.1.map f := rfl

@[simp] theorem map_empty (f : α ↪ β) : (∅ : finset α).map f = ∅ := rfl

variables {f : α ↪ β} {s : finset α}

@[simp] theorem mem_map {b : β} : b ∈ s.map f ↔ ∃ a ∈ s, f a = b :=
mem_map.trans $ by simp only [exists_prop]; refl

@[simp] lemma mem_map_equiv {f : α ≃ β} {b : β} : b ∈ s.map f.to_embedding ↔ f.symm b ∈ s :=
by { rw mem_map, exact ⟨by { rintro ⟨a, H, rfl⟩, simpa }, λ h, ⟨_, h, by simp⟩⟩ }

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
lemma map_perm {σ : equiv.perm α} (hs : {a | σ a ≠ a} ⊆ s) : s.map (σ : α ↪ α) = s :=
begin
  ext i,
  rw mem_map,
  obtain hi | hi := eq_or_ne (σ i) i,
  { refine ⟨_, λ h, ⟨i, h, hi⟩⟩,
    rintro ⟨j, hj, h⟩,
    rwa σ.injective (hi.trans h.symm) },
  { refine iff_of_true ⟨σ.symm i, hs $ λ h, hi _, σ.apply_symm_apply _⟩ (hs hi),
    convert congr_arg σ h; exact (σ.apply_symm_apply _).symm }
end

lemma mem_map' (f : α ↪ β) {a} {s : finset α} : f a ∈ s.map f ↔ a ∈ s := mem_map_of_injective f.2

lemma mem_map_of_mem (f : α ↪ β) {a} {s : finset α} : a ∈ s → f a ∈ s.map f := (mem_map' _).2

lemma apply_coe_mem_map (f : α ↪ β) (s : finset α) (x : s) : f x ∈ s.map f :=
mem_map_of_mem f x.prop

@[simp, norm_cast] theorem coe_map (f : α ↪ β) (s : finset α) : (s.map f : set β) = f '' s :=
set.ext $ λ x, mem_map.trans set.mem_image_iff_bex.symm

theorem coe_map_subset_range (f : α ↪ β) (s : finset α) : (s.map f : set β) ⊆ set.range f :=
calc ↑(s.map f) = f '' s      : coe_map f s
            ... ⊆ set.range f : set.image_subset_range f ↑s

theorem map_to_finset [decidable_eq α] [decidable_eq β] {s : multiset α} :
  s.to_finset.map f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_map, multiset.mem_map, exists_prop, multiset.mem_to_finset]

@[simp] theorem map_refl : s.map (embedding.refl _) = s :=
ext $ λ _, by simpa only [mem_map, exists_prop] using exists_eq_right

@[simp] theorem map_cast_heq {α β} (h : α = β) (s : finset α) :
  s.map (equiv.cast h).to_embedding == s :=
by { subst h, simp }

theorem map_map {g : β ↪ γ} : (s.map f).map g = s.map (f.trans g) :=
eq_of_veq $ by simp only [map_val, multiset.map_map]; refl

@[simp] theorem map_subset_map {s₁ s₂ : finset α} : s₁.map f ⊆ s₂.map f ↔ s₁ ⊆ s₂ :=
⟨λ h x xs, (mem_map' _).1 $ h $ (mem_map' f).2 xs,
 λ h, by simp [subset_def, map_subset_map h]⟩

/-- Associate to an embedding `f` from `α` to `β` the order embedding that maps a finset to its
image under `f`. -/
def map_embedding (f : α ↪ β) : finset α ↪o finset β :=
order_embedding.of_map_le_iff (map f) (λ _ _, map_subset_map)

@[simp] theorem map_inj {s₁ s₂ : finset α} : s₁.map f = s₂.map f ↔ s₁ = s₂ :=
(map_embedding f).injective.eq_iff

@[simp] theorem map_embedding_apply : map_embedding f s = map f s := rfl

theorem map_filter {p : β → Prop} [decidable_pred p] :
  (s.map f).filter p = (s.filter (p ∘ f)).map f :=
eq_of_veq (map_filter _ _ _)

theorem map_union [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∪ s₂).map f = s₁.map f ∪ s₂.map f :=
coe_injective $ by simp only [coe_map, coe_union, set.image_union]

theorem map_inter [decidable_eq α] [decidable_eq β]
  {f : α ↪ β} (s₁ s₂ : finset α) : (s₁ ∩ s₂).map f = s₁.map f ∩ s₂.map f :=
coe_injective $ by simp only [coe_map, coe_inter, set.image_inter f.injective]

@[simp] theorem map_singleton (f : α ↪ β) (a : α) : map f {a} = {f a} :=
coe_injective $ by simp only [coe_map, coe_singleton, set.image_singleton]

@[simp] lemma map_insert [decidable_eq α] [decidable_eq β] (f : α ↪ β) (a : α) (s : finset α) :
  (insert a s).map f = insert (f a) (s.map f) :=
by simp only [insert_eq, map_union, map_singleton]

@[simp] theorem map_eq_empty : s.map f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_map_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

@[simp] lemma map_nonempty : (s.map f).nonempty ↔ s.nonempty :=
by rw [nonempty_iff_ne_empty, nonempty_iff_ne_empty, ne.def, map_eq_empty]

alias map_nonempty ↔ _ finset.nonempty.map

lemma attach_map_val {s : finset α} : s.attach.map (embedding.subtype _) = s :=
eq_of_veq $ by rw [map_val, attach_val]; exact attach_map_val _

end map

lemma range_add_one' (n : ℕ) :
  range (n + 1) = insert 0 ((range n).map ⟨λi, i + 1, assume i j, nat.succ.inj⟩) :=
by ext (⟨⟩ | ⟨n⟩); simp [nat.succ_eq_add_one, nat.zero_lt_succ n]

/-! ### image -/

section image
variables [decidable_eq β]

/-- `image f s` is the forward image of `s` under `f`. -/
def image (f : α → β) (s : finset α) : finset β := (s.1.map f).to_finset

@[simp] theorem image_val (f : α → β) (s : finset α) : (image f s).1 = (s.1.map f).erase_dup := rfl

@[simp] theorem image_empty (f : α → β) : (∅ : finset α).image f = ∅ := rfl

variables {f g : α → β} {s : finset α} {t : finset β} {a : α} {b c : β}

@[simp] lemma mem_image : b ∈ s.image f ↔ ∃ a ∈ s, f a = b :=
by simp only [mem_def, image_val, mem_erase_dup, multiset.mem_map, exists_prop]

lemma mem_image_of_mem (f : α → β) {a} (h : a ∈ s) : f a ∈ s.image f := mem_image.2 ⟨_, h, rfl⟩

@[simp] lemma mem_image_const : c ∈ s.image (const α b) ↔ s.nonempty ∧ b = c :=
by { rw mem_image, simp only [exists_prop, const_apply, exists_and_distrib_right], refl }

lemma mem_image_const_self : b ∈ s.image (const α b) ↔ s.nonempty :=
mem_image_const.trans $ and_iff_left rfl

instance [can_lift β α] : can_lift (finset β) (finset α) :=
{ cond := λ s, ∀ x ∈ s, can_lift.cond α x,
  coe := image can_lift.coe,
  prf :=
    begin
      rintro ⟨⟨l⟩, hd : l.nodup⟩ hl,
      lift l to list α using hl,
      refine ⟨⟨l, list.nodup_of_nodup_map _ hd⟩, ext $ λ a, _⟩,
      simp
    end }

lemma image_congr (h : (s : set α).eq_on f g) : finset.image f s = finset.image g s :=
by { ext, simp_rw mem_image, exact bex_congr (λ x hx, by rw h hx) }

lemma _root_.function.injective.mem_finset_image (hf : injective f) : f a ∈ s.image f ↔ a ∈ s :=
begin
  refine ⟨λ h, _, finset.mem_image_of_mem f⟩,
  obtain ⟨y, hy, heq⟩ := mem_image.1 h,
  exact hf heq ▸ hy,
end

lemma filter_mem_image_eq_image (f : α → β) (s : finset α) (t : finset β) (h : ∀ x ∈ s, f x ∈ t) :
  t.filter (λ y, y ∈ s.image f) = s.image f :=
by { ext, rw [mem_filter, mem_image],
     simp only [and_imp, exists_prop, and_iff_right_iff_imp, exists_imp_distrib],
     rintros x xel rfl, exact h _ xel }

lemma fiber_nonempty_iff_mem_image (f : α → β) (s : finset α) (y : β) :
  (s.filter (λ x, f x = y)).nonempty ↔ y ∈ s.image f :=
by simp [finset.nonempty]

@[simp, norm_cast] lemma coe_image {f : α → β} : ↑(s.image f) = f '' ↑s :=
set.ext $ λ _, mem_image.trans set.mem_image_iff_bex.symm

protected lemma nonempty.image (h : s.nonempty) (f : α → β) : (s.image f).nonempty :=
let ⟨a, ha⟩ := h in ⟨f a, mem_image_of_mem f ha⟩

@[simp] lemma nonempty.image_iff (f : α → β) : (s.image f).nonempty ↔ s.nonempty :=
⟨λ ⟨y, hy⟩, let ⟨x, hx, _⟩ := mem_image.mp hy in ⟨x, hx⟩, λ h, h.image f⟩

theorem image_to_finset [decidable_eq α] {s : multiset α} :
  s.to_finset.image f = (s.map f).to_finset :=
ext $ λ _, by simp only [mem_image, multiset.mem_to_finset, exists_prop, multiset.mem_map]

theorem image_val_of_inj_on (H : set.inj_on f s) : (image f s).1 = s.1.map f :=
(nodup_map_on H s.2).erase_dup

@[simp] lemma image_id [decidable_eq α] : s.image id = s :=
ext $ λ _, by simp only [mem_image, exists_prop, id, exists_eq_right]

@[simp] theorem image_id' [decidable_eq α] : s.image (λ x, x) = s := image_id

theorem image_image [decidable_eq γ] {g : β → γ} : (s.image f).image g = s.image (g ∘ f) :=
eq_of_veq $ by simp only [image_val, erase_dup_map_erase_dup_eq, multiset.map_map]

theorem image_subset_image {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) : s₁.image f ⊆ s₂.image f :=
by simp only [subset_def, image_val, subset_erase_dup', erase_dup_subset',
  multiset.map_subset_map h]

lemma image_subset_iff : s.image f ⊆ t ↔ ∀ x ∈ s, f x ∈ t :=
calc s.image f ⊆ t ↔ f '' ↑s ⊆ ↑t : by norm_cast
               ... ↔ _ : set.image_subset_iff

theorem image_mono (f : α → β) : monotone (finset.image f) := λ _ _, image_subset_image

theorem coe_image_subset_range : ↑(s.image f) ⊆ set.range f :=
calc ↑(s.image f) = f '' ↑s     : coe_image
              ... ⊆ set.range f : set.image_subset_range f ↑s

theorem image_filter {p : β → Prop} [decidable_pred p] :
  (s.image f).filter p = (s.filter (p ∘ f)).image f :=
ext $ λ b, by simp only [mem_filter, mem_image, exists_prop]; exact
⟨by rintro ⟨⟨x, h1, rfl⟩, h2⟩; exact ⟨x, ⟨h1, h2⟩, rfl⟩,
 by rintro ⟨x, ⟨h1, h2⟩, rfl⟩; exact ⟨⟨x, h1, rfl⟩, h2⟩⟩

theorem image_union [decidable_eq α] {f : α → β} (s₁ s₂ : finset α) :
  (s₁ ∪ s₂).image f = s₁.image f ∪ s₂.image f :=
ext $ λ _, by simp only [mem_image, mem_union, exists_prop, or_and_distrib_right,
  exists_or_distrib]

lemma image_inter [decidable_eq α] (s₁ s₂ : finset α) (hf : ∀ x y, f x = f y → x = y) :
  (s₁ ∩ s₂).image f = s₁.image f ∩ s₂.image f :=
ext $ by simp only [mem_image, exists_prop, mem_inter]; exact λ b,
⟨λ ⟨a, ⟨m₁, m₂⟩, e⟩, ⟨⟨a, m₁, e⟩, ⟨a, m₂, e⟩⟩,
 λ ⟨⟨a, m₁, e₁⟩, ⟨a', m₂, e₂⟩⟩, ⟨a, ⟨m₁, hf _ _ (e₂.trans e₁.symm) ▸ m₂⟩, e₁⟩⟩.

@[simp] theorem image_singleton (f : α → β) (a : α) : image f {a} = {f a} :=
ext $ λ x, by simpa only [mem_image, exists_prop, mem_singleton, exists_eq_left] using eq_comm

@[simp] theorem image_insert [decidable_eq α] (f : α → β) (a : α) (s : finset α) :
  (insert a s).image f = insert (f a) (s.image f) :=
by simp only [insert_eq, image_singleton, image_union]

@[simp] lemma image_erase [decidable_eq α] {f : α → β} (hf : injective f) (s : finset α) (a : α) :
  (s.erase a).image f = (s.image f).erase (f a) :=
begin
  ext b,
  simp only [mem_image, exists_prop, mem_erase],
  split,
  { rintro ⟨a', ⟨haa', ha'⟩, rfl⟩,
    exact ⟨hf.ne haa', a', ha', rfl⟩ },
  { rintro ⟨h, a', ha', rfl⟩,
    exact ⟨a', ⟨ne_of_apply_ne _ h, ha'⟩, rfl⟩ }
end

@[simp] theorem image_eq_empty : s.image f = ∅ ↔ s = ∅ :=
⟨λ h, eq_empty_of_forall_not_mem $
 λ a m, ne_empty_of_mem (mem_image_of_mem _ m) h, λ e, e.symm ▸ rfl⟩

lemma mem_range_iff_mem_finset_range_of_mod_eq' [decidable_eq α] {f : ℕ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
begin
  split,
  { rintros ⟨i, hi⟩,
    simp only [mem_image, exists_prop, mem_range],
    exact ⟨i % n, nat.mod_lt i hn, (rfl.congr hi).mp (h i)⟩ },
  { rintro h,
    simp only [mem_image, exists_prop, set.mem_range, mem_range] at *,
    rcases h with ⟨i, hi, ha⟩,
    exact ⟨i, ha⟩ }
end

lemma mem_range_iff_mem_finset_range_of_mod_eq [decidable_eq α] {f : ℤ → α} {a : α} {n : ℕ}
  (hn : 0 < n) (h : ∀ i, f (i % n) = f i) :
  a ∈ set.range f ↔ a ∈ (finset.range n).image (λi, f i) :=
suffices (∃ i, f (i % n) = a) ↔ ∃ i, i < n ∧ f ↑i = a, by simpa [h],
have hn' : 0 < (n : ℤ), from int.coe_nat_lt.mpr hn,
iff.intro
  (assume ⟨i, hi⟩,
    have 0 ≤ i % ↑n, from int.mod_nonneg _ (ne_of_gt hn'),
    ⟨int.to_nat (i % n),
      by rw [←int.coe_nat_lt, int.to_nat_of_nonneg this]; exact ⟨int.mod_lt_of_pos i hn', hi⟩⟩)
  (assume ⟨i, hi, ha⟩,
    ⟨i, by rw [int.mod_eq_of_lt (int.coe_zero_le _) (int.coe_nat_lt_coe_nat_of_lt hi), ha]⟩)

lemma range_add (a b : ℕ) : range (a + b) = range a ∪ (range b).map (add_left_embedding a) :=
by { rw [←val_inj, union_val], exact multiset.range_add_eq_union a b }

@[simp] lemma attach_image_val [decidable_eq α] {s : finset α} : s.attach.image subtype.val = s :=
eq_of_veq $ by rw [image_val, attach_val, multiset.attach_map_val, erase_dup_eq_self]

@[simp] lemma attach_image_coe [decidable_eq α] {s : finset α} : s.attach.image coe = s :=
finset.attach_image_val

@[simp] lemma attach_insert [decidable_eq α] {a : α} {s : finset α} :
  attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : {x // x ∈ insert a s})
    ((attach s).image (λx, ⟨x.1, mem_insert_of_mem x.2⟩)) :=
ext $ λ ⟨x, hx⟩, ⟨or.cases_on (mem_insert.1 hx)
  (λ h : x = a, λ _, mem_insert.2 $ or.inl $ subtype.eq h)
  (λ h : x ∈ s, λ _, mem_insert_of_mem $ mem_image.2 $ ⟨⟨x, h⟩, mem_attach _ _, subtype.eq rfl⟩),
λ _, finset.mem_attach _ _⟩

theorem map_eq_image (f : α ↪ β) (s : finset α) : s.map f = s.image f :=
eq_of_veq (s.map f).2.erase_dup.symm

lemma image_const {s : finset α} (h : s.nonempty) (b : β) : s.image (λa, b) = singleton b :=
ext $ assume b', by simp only [mem_image, exists_prop, exists_and_distrib_right,
  h.bex, true_and, mem_singleton, eq_comm]

@[simp] lemma map_erase [decidable_eq α] (f : α ↪ β) (s : finset α) (a : α) :
  (s.erase a).map f = (s.map f).erase (f a) :=
by { simp_rw map_eq_image, exact s.image_erase f.2 a }

/-! ### Subtype -/

/-- Given a finset `s` and a predicate `p`, `s.subtype p` is the finset of `subtype p` whose
elements belong to `s`. -/
protected def subtype {α} (p : α → Prop) [decidable_pred p] (s : finset α) : finset (subtype p) :=
(s.filter p).attach.map ⟨λ x, ⟨x.1, (finset.mem_filter.1 x.2).2⟩,
λ x y H, subtype.eq $ subtype.mk.inj H⟩

@[simp] lemma mem_subtype {p : α → Prop} [decidable_pred p] {s : finset α} :
  ∀ {a : subtype p}, a ∈ s.subtype p ↔ (a : α) ∈ s
| ⟨a, ha⟩ := by simp [finset.subtype, ha]

lemma subtype_eq_empty {p : α → Prop} [decidable_pred p] {s : finset α} :
  s.subtype p = ∅ ↔ ∀ x, p x → x ∉ s :=
by simp [ext_iff, subtype.forall, subtype.coe_mk]; refl

@[mono] lemma subtype_mono {p : α → Prop} [decidable_pred p] : monotone (finset.subtype p) :=
λ s t h x hx, mem_subtype.2 $ h $ mem_subtype.1 hx

/-- `s.subtype p` converts back to `s.filter p` with
`embedding.subtype`. -/
@[simp] lemma subtype_map (p : α → Prop) [decidable_pred p] :
  (s.subtype p).map (embedding.subtype _) = s.filter p :=
begin
  ext x,
  simp [and_comm _ (_ = _), @and.left_comm _ (_ = _), and_comm (p x) (x ∈ s)]
end

/-- If all elements of a `finset` satisfy the predicate `p`,
`s.subtype p` converts back to `s` with `embedding.subtype`. -/
lemma subtype_map_of_mem {p : α → Prop} [decidable_pred p] (h : ∀ x ∈ s, p x) :
  (s.subtype p).map (embedding.subtype _) = s :=
by rw [subtype_map, filter_true_of_mem h]

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, all elements of the result have the property of
the subtype. -/
lemma property_of_mem_map_subtype {p : α → Prop} (s : finset {x // p x}) {a : α}
  (h : a ∈ s.map (embedding.subtype _)) : p a :=
begin
  rcases mem_map.1 h with ⟨x, hx, rfl⟩,
  exact x.2
end

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result does not contain any value that does
not satisfy the property of the subtype. -/
lemma not_mem_map_subtype_of_not_property {p : α → Prop} (s : finset {x // p x})
  {a : α} (h : ¬ p a) : a ∉ (s.map (embedding.subtype _)) :=
mt s.property_of_mem_map_subtype h

/-- If a `finset` of a subtype is converted to the main type with
`embedding.subtype`, the result is a subset of the set giving the
subtype. -/
lemma map_subtype_subset {t : set α} (s : finset t) : ↑(s.map (embedding.subtype _)) ⊆ t :=
begin
  intros a ha,
  rw mem_coe at ha,
  convert property_of_mem_map_subtype s ha
end

lemma subset_image_iff {s : set α} : ↑t ⊆ f '' s ↔ ∃ s' : finset α, ↑s' ⊆ s ∧ s'.image f = t :=
begin
  split, swap,
  { rintro ⟨t, ht, rfl⟩, rw [coe_image], exact set.image_subset f ht },
  intro h,
  letI : can_lift β s := ⟨f ∘ coe, λ y, y ∈ f '' s, λ y ⟨x, hxt, hy⟩, ⟨⟨x, hxt⟩, hy⟩⟩,
  lift t to finset s using h,
  refine ⟨t.map (embedding.subtype _), map_subtype_subset _, _⟩,
  ext y, simp
end

lemma range_sdiff_zero {n : ℕ} : range (n + 1) \ {0} = (range n).image nat.succ :=
begin
  induction n with k hk,
  { simp },
  nth_rewrite 1 range_succ,
  rw [range_succ, image_insert, ←hk, insert_sdiff_of_not_mem],
  simp
end

end image

lemma _root_.multiset.to_finset_map [decidable_eq α] [decidable_eq β] (f : α → β) (m : multiset α) :
  (m.map f).to_finset = m.to_finset.image f :=
finset.val_inj.1 (multiset.erase_dup_map_erase_dup_eq _ _).symm

section to_list

/-- Produce a list of the elements in the finite set using choice. -/
@[reducible] noncomputable def to_list (s : finset α) : list α := s.1.to_list

lemma nodup_to_list (s : finset α) : s.to_list.nodup :=
by { rw [to_list, ←multiset.coe_nodup, multiset.coe_to_list], exact s.nodup }

@[simp] lemma mem_to_list {a : α} (s : finset α) : a ∈ s.to_list ↔ a ∈ s :=
by { rw [to_list, ←multiset.mem_coe, multiset.coe_to_list], exact iff.rfl }

@[simp] lemma to_list_empty : (∅ : finset α).to_list = [] := by simp [to_list]

@[simp, norm_cast]
lemma coe_to_list (s : finset α) : (s.to_list : multiset α) = s.val := by { classical, ext, simp }

@[simp] lemma to_list_to_finset [decidable_eq α] (s : finset α) : s.to_list.to_finset = s :=
by { ext, simp }

lemma exists_list_nodup_eq [decidable_eq α] (s : finset α) :
  ∃ (l : list α), l.nodup ∧ l.to_finset = s :=
⟨s.to_list, s.nodup_to_list, s.to_list_to_finset⟩

lemma to_list_cons {a : α} {s : finset α} (h : a ∉ s) : (cons a s h).to_list ~ a :: s.to_list :=
(list.perm_ext (nodup_to_list _) (by simp [h, nodup_to_list s])).2 $
  λ x, by simp only [list.mem_cons_iff, finset.mem_to_list, finset.mem_cons]

lemma to_list_insert [decidable_eq α] {a : α} {s : finset α} (h : a ∉ s) :
  (insert a s).to_list ~ a :: s.to_list :=
cons_eq_insert _ _ h ▸ to_list_cons _

end to_list

section bUnion
/-!
### bUnion

This section is about the bounded union of an indexed family `t : α → finset β` of finite sets
over a finite set `s : finset α`.
-/

variables [decidable_eq β] {s s₁ s₂ : finset α} {t t₁ t₂ : α → finset β}

/-- `bUnion s t` is the union of `t x` over `x ∈ s`.
(This was formerly `bind` due to the monad structure on types with `decidable_eq`.) -/
protected def bUnion (s : finset α) (t : α → finset β) : finset β :=
(s.1.bind (λ a, (t a).1)).to_finset

@[simp] theorem bUnion_val (s : finset α) (t : α → finset β) :
  (s.bUnion t).1 = (s.1.bind (λ a, (t a).1)).erase_dup := rfl

@[simp] theorem bUnion_empty : finset.bUnion ∅ t = ∅ := rfl

@[simp] lemma mem_bUnion {b : β} : b ∈ s.bUnion t ↔ ∃ a ∈ s, b ∈ t a :=
by simp only [mem_def, bUnion_val, mem_erase_dup, mem_bind, exists_prop]

@[simp] lemma coe_bUnion : (s.bUnion t : set β) = ⋃ x ∈ (s : set α), t x :=
by simp only [set.ext_iff, mem_bUnion, set.mem_Union, iff_self, mem_coe, implies_true_iff]

@[simp] theorem bUnion_insert [decidable_eq α] {a : α} : (insert a s).bUnion t = t a ∪ s.bUnion t :=
ext $ λ x, by simp only [mem_bUnion, exists_prop, mem_union, mem_insert,
  or_and_distrib_right, exists_or_distrib, exists_eq_left]
-- ext $ λ x, by simp [or_and_distrib_right, exists_or_distrib]

lemma bUnion_congr (hs : s₁ = s₂) (ht : ∀ a ∈ s₁, t₁ a = t₂ a) : s₁.bUnion t₁ = s₂.bUnion t₂ :=
ext $ λ x, by simp [hs, ht] { contextual := tt }

theorem bUnion_subset {s' : finset β} : s.bUnion t ⊆ s' ↔ ∀ x ∈ s, t x ⊆ s' :=
by simp only [subset_iff, mem_bUnion]; exact
⟨λ H a ha b hb, H ⟨a, ha, hb⟩, λ H b ⟨a, ha, hb⟩, H a ha hb⟩

@[simp] lemma singleton_bUnion {a : α} : finset.bUnion {a} t = t a :=
by { classical, rw [← insert_emptyc_eq, bUnion_insert, bUnion_empty, union_empty] }

theorem bUnion_inter (s : finset α) (f : α → finset β) (t : finset β) :
  s.bUnion f ∩ t = s.bUnion (λ x, f x ∩ t) :=
begin
  ext x,
  simp only [mem_bUnion, mem_inter],
  tauto
end

theorem inter_bUnion (t : finset β) (s : finset α) (f : α → finset β) :
  t ∩ s.bUnion f = s.bUnion (λ x, t ∩ f x) :=
by rw [inter_comm, bUnion_inter]; simp [inter_comm]

theorem image_bUnion [decidable_eq γ] {f : α → β} {s : finset α} {t : β → finset γ} :
  (s.image f).bUnion t = s.bUnion (λa, t (f a)) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [image_insert, bUnion_insert, ih])

theorem bUnion_image [decidable_eq γ] {s : finset α} {t : α → finset β} {f : β → γ} :
  (s.bUnion t).image f = s.bUnion (λa, (t a).image f) :=
by haveI := classical.dec_eq α; exact
finset.induction_on s rfl (λ a s has ih,
  by simp only [bUnion_insert, image_union, ih])

lemma bUnion_bUnion [decidable_eq γ] (s : finset α) (f : α → finset β) (g : β → finset γ) :
  (s.bUnion f).bUnion g = s.bUnion (λ a, (f a).bUnion g) :=
begin
  ext,
  simp only [finset.mem_bUnion, exists_prop],
  simp_rw [←exists_and_distrib_right, ←exists_and_distrib_left, and_assoc],
  rw exists_comm,
end

theorem bind_to_finset [decidable_eq α] (s : multiset α) (t : α → multiset β) :
  (s.bind t).to_finset = s.to_finset.bUnion (λa, (t a).to_finset) :=
ext $ λ x, by simp only [multiset.mem_to_finset, mem_bUnion, multiset.mem_bind, exists_prop]

lemma bUnion_mono (h : ∀ a ∈ s, t₁ a ⊆ t₂ a) : s.bUnion t₁ ⊆ s.bUnion t₂ :=
have ∀ b a, a ∈ s → b ∈ t₁ a → (∃ (a : α), a ∈ s ∧ b ∈ t₂ a),
  from assume b a ha hb, ⟨a, ha, finset.mem_of_subset (h a ha) hb⟩,
by simpa only [subset_iff, mem_bUnion, exists_imp_distrib, and_imp, exists_prop]

lemma bUnion_subset_bUnion_of_subset_left (t : α → finset β) (h : s₁ ⊆ s₂) :
  s₁.bUnion t ⊆ s₂.bUnion t :=
begin
  intro x,
  simp only [and_imp, mem_bUnion, exists_prop],
  exact Exists.imp (λ a ha, ⟨h ha.1, ha.2⟩)
end

lemma subset_bUnion_of_mem (u : α → finset β) {x : α} (xs : x ∈ s) : u x ⊆ s.bUnion u :=
singleton_bUnion.superset.trans $ bUnion_subset_bUnion_of_subset_left u $ singleton_subset_iff.2 xs

@[simp] lemma bUnion_subset_iff_forall_subset {α β : Type*} [decidable_eq β]
  {s : finset α} {t : finset β} {f : α → finset β} : s.bUnion f ⊆ t ↔ ∀ x ∈ s, f x ⊆ t :=
⟨λ h x hx, (subset_bUnion_of_mem f hx).trans h,
 λ h x hx, let ⟨a, ha₁, ha₂⟩ := mem_bUnion.mp hx in h _ ha₁ ha₂⟩

lemma bUnion_singleton {f : α → β} : s.bUnion (λa, {f a}) = s.image f :=
ext $ λ x, by simp only [mem_bUnion, mem_image, mem_singleton, eq_comm]

@[simp] lemma bUnion_singleton_eq_self [decidable_eq α] : s.bUnion (singleton : α → finset α) = s :=
by { rw bUnion_singleton, exact image_id }

lemma filter_bUnion (s : finset α) (f : α → finset β) (p : β → Prop) [decidable_pred p] :
  (s.bUnion f).filter p = s.bUnion (λ a, (f a).filter p) :=
begin
  ext b,
  simp only [mem_bUnion, exists_prop, mem_filter],
  split,
  { rintro ⟨⟨a, ha, hba⟩, hb⟩,
    exact ⟨a, ha, hba, hb⟩ },
  { rintro ⟨a, ha, hba, hb⟩,
    exact ⟨⟨a, ha, hba⟩, hb⟩ }
end

lemma bUnion_filter_eq_of_maps_to [decidable_eq α] {s : finset α} {t : finset β} {f : α → β}
  (h : ∀ x ∈ s, f x ∈ t) :
  t.bUnion (λa, s.filter $ (λc, f c = a)) = s :=
ext $ λ b, by simpa using h b

lemma image_bUnion_filter_eq [decidable_eq α] (s : finset β) (g : β → α) :
  (s.image g).bUnion (λa, s.filter $ (λc, g c = a)) = s :=
bUnion_filter_eq_of_maps_to (λ x, mem_image_of_mem g)

lemma erase_bUnion (f : α → finset β) (s : finset α) (b : β) :
  (s.bUnion f).erase b = s.bUnion (λ x, (f x).erase b) :=
by { ext, simp only [finset.mem_bUnion, iff_self, exists_and_distrib_left, finset.mem_erase] }

@[simp] lemma bUnion_nonempty : (s.bUnion t).nonempty ↔ ∃ x ∈ s, (t x).nonempty :=
by simp [finset.nonempty, ← exists_and_distrib_left, @exists_swap α]

lemma nonempty.bUnion (hs : s.nonempty) (ht : ∀ x ∈ s, (t x).nonempty) : (s.bUnion t).nonempty :=
bUnion_nonempty.2 $ hs.imp $ λ x hx, ⟨hx, ht x hx⟩

end bUnion

/-! ### disjoint -/
--TODO@Yaël: Kill lemmas duplicate with `boolean_algebra`
section disjoint
variables [decidable_eq α] [decidable_eq β] {s t u : finset α} {a b : α}

lemma disjoint_left : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t :=
by simp only [_root_.disjoint, inf_eq_inter, le_iff_subset, subset_iff, mem_inter, not_and,
  and_imp]; refl

lemma disjoint_val : disjoint s t ↔ s.1.disjoint t.1 := disjoint_left
lemma disjoint_iff_inter_eq_empty : disjoint s t ↔ s ∩ t = ∅ := disjoint_iff

instance decidable_disjoint (U V : finset α) : decidable (disjoint U V) :=
decidable_of_decidable_of_iff (by apply_instance) eq_bot_iff

lemma disjoint_right : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s := by rw [disjoint.comm, disjoint_left]
lemma disjoint_iff_ne : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

lemma not_disjoint_iff : ¬ disjoint s t ↔ ∃ a, a ∈ s ∧ a ∈ t :=
not_forall.trans $ exists_congr $ λ a, not_not.trans mem_inter

lemma disjoint_of_subset_left (h : s ⊆ u) (d : disjoint u t) : disjoint s t :=
disjoint_left.2 (λ x m₁, (disjoint_left.1 d) (h m₁))

lemma disjoint_of_subset_right (h : t ⊆ u) (d : disjoint s u) : disjoint s t :=
disjoint_right.2 (λ x m₁, (disjoint_right.1 d) (h m₁))

@[simp] theorem disjoint_empty_left (s : finset α) : disjoint ∅ s := disjoint_bot_left
@[simp] theorem disjoint_empty_right (s : finset α) : disjoint s ∅ := disjoint_bot_right

@[simp] lemma disjoint_singleton_left : disjoint (singleton a) s ↔ a ∉ s :=
by simp only [disjoint_left, mem_singleton, forall_eq]

@[simp] lemma disjoint_singleton_right : disjoint s (singleton a) ↔ a ∉ s :=
disjoint.comm.trans disjoint_singleton_left

@[simp] lemma disjoint_singleton : disjoint ({a} : finset α) {b} ↔ a ≠ b :=
by rw [disjoint_singleton_left, mem_singleton]

@[simp] lemma disjoint_insert_left : disjoint (insert a s) t ↔ a ∉ t ∧ disjoint s t :=
by simp only [disjoint_left, mem_insert, or_imp_distrib, forall_and_distrib, forall_eq]

@[simp] lemma disjoint_insert_right : disjoint s (insert a t) ↔ a ∉ s ∧ disjoint s t :=
disjoint.comm.trans $ by rw [disjoint_insert_left, disjoint.comm]

@[simp] lemma disjoint_union_left : disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp only [disjoint_left, mem_union, or_imp_distrib, forall_and_distrib]

@[simp] lemma disjoint_union_right : disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp only [disjoint_right, mem_union, or_imp_distrib, forall_and_distrib]

lemma sdiff_disjoint : disjoint (t \ s) s := disjoint_left.2 $ assume a ha, (mem_sdiff.1 ha).2
lemma disjoint_sdiff : disjoint s (t \ s) := sdiff_disjoint.symm

lemma disjoint_sdiff_inter (s t : finset α) : disjoint (s \ t) (s ∩ t) :=
disjoint_of_subset_right (inter_subset_right _ _) sdiff_disjoint

lemma sdiff_eq_self_iff_disjoint : s \ t = s ↔ disjoint s t := sdiff_eq_self_iff_disjoint'
lemma sdiff_eq_self_of_disjoint (h : disjoint s t) : s \ t = s := sdiff_eq_self_iff_disjoint.2 h
lemma disjoint_self_iff_empty (s : finset α) : disjoint s s ↔ s = ∅ := disjoint_self

lemma disjoint_bUnion_left {ι : Type*} (s : finset ι) (f : ι → finset α) (t : finset α) :
  disjoint (s.bUnion f) t ↔ (∀ i ∈ s, disjoint (f i) t) :=
begin
  classical,
  refine s.induction _ _,
  { simp only [forall_mem_empty_iff, bUnion_empty, disjoint_empty_left] },
  { assume i s his ih,
    simp only [disjoint_union_left, bUnion_insert, his, forall_mem_insert, ih] }
end

lemma disjoint_bUnion_right {ι : Type*} (s : finset α) (t : finset ι) (f : ι → finset α) :
  disjoint s (t.bUnion f) ↔ ∀ i ∈ t, disjoint s (f i) :=
by simpa only [disjoint.comm] using disjoint_bUnion_left t f s

lemma disjoint_filter {p q : α → Prop} [decidable_pred p] [decidable_pred q] :
  disjoint (s.filter p) (s.filter q) ↔ ∀ x ∈ s, p x → ¬ q x :=
by split; simp [disjoint_left] {contextual := tt}

lemma disjoint_filter_filter {p q : α → Prop} [decidable_pred p] [decidable_pred q] :
  (disjoint s t) → disjoint (s.filter p) (t.filter q) :=
disjoint.mono (filter_subset _ _) (filter_subset _ _)

lemma disjoint_filter_filter_neg (s : finset α) (p : α → Prop) [decidable_pred p] :
  disjoint (s.filter p) (s.filter $ λ a, ¬ p a) :=
(disjoint_filter.2 $ λ a _, id).symm

lemma disjoint_iff_disjoint_coe : disjoint s t ↔ disjoint (s : set α) (t : set α) :=
by { rw [finset.disjoint_left, set.disjoint_left], refl }

end disjoint

/-! ### choose -/
section choose
variables (p : α → Prop) [decidable_pred p] (l : finset α)

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : (∃! a, a ∈ l ∧ p a)) : { a // a ∈ l ∧ p a } :=
multiset.choose_x p l.val hp

/-- Given a finset `l` and a predicate `p`, associate to a proof that there is a unique element of
`l` satisfying `p` this unique element, as an element of the ambient type. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose
end finset

namespace equiv

/-- Given an equivalence `α` to `β`, produce an equivalence between `finset α` and `finset β`. -/
protected def finset_congr (e : α ≃ β) : finset α ≃ finset β :=
{ to_fun := λ s, s.map e.to_embedding,
  inv_fun := λ s, s.map e.symm.to_embedding,
  left_inv := λ s, by simp [finset.map_map],
  right_inv := λ s, by simp [finset.map_map] }

@[simp] lemma finset_congr_apply (e : α ≃ β) (s : finset α) :
  e.finset_congr s = s.map e.to_embedding :=
rfl

@[simp] lemma finset_congr_refl : (equiv.refl α).finset_congr = equiv.refl _ := by { ext, simp }
@[simp] lemma finset_congr_symm (e : α ≃ β) : e.finset_congr.symm = e.symm.finset_congr := rfl

@[simp] lemma finset_congr_trans (e : α ≃ β) (e' : β ≃ γ) :
  e.finset_congr.trans (e'.finset_congr) = (e.trans e').finset_congr :=
by { ext, simp [-finset.mem_map, -equiv.trans_to_embedding] }

end equiv

namespace multiset
variable [decidable_eq α]

lemma disjoint_to_finset {m1 m2 : multiset α} :
  _root_.disjoint m1.to_finset m2.to_finset ↔ m1.disjoint m2 :=
begin
  rw finset.disjoint_iff_ne,
  refine ⟨λ h a ha1 ha2, _, _⟩,
  { rw ← multiset.mem_to_finset at ha1 ha2,
    exact h _ ha1 _ ha2 rfl },
  { rintros h a ha b hb rfl,
    rw multiset.mem_to_finset at ha hb,
    exact h ha hb }
end

end multiset

namespace list
variables [decidable_eq α] {l l' : list α}

lemma disjoint_to_finset_iff_disjoint : _root_.disjoint l.to_finset l'.to_finset ↔ l.disjoint l' :=
multiset.disjoint_to_finset

end list
