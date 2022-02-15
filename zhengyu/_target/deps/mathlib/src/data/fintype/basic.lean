/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.array.lemmas
import data.finset.fin
import data.finset.option
import data.finset.pi
import data.finset.powerset
import data.finset.prod
import data.finset.sigma
import data.list.nodup_equiv_fin
import data.sym.basic
import data.ulift
import group_theory.perm.basic
import order.well_founded
import tactic.wlog

/-!
# Finite types

This file defines a typeclass to state that a type is finite.

## Main declarations

* `fintype α`:  Typeclass saying that a type is finite. It takes as fields a `finset` and a proof
  that all terms of type `α` are in it.
* `finset.univ`: The finset of all elements of a fintype.
* `fintype.card α`: Cardinality of a fintype. Equal to `finset.univ.card`.
* `perms_of_finset s`: The finset of permutations of the finset `s`.
* `fintype.trunc_equiv_fin`: A fintype `α` is computably equivalent to `fin (card α)`. The
  `trunc`-free, noncomputable version is `fintype.equiv_fin`.
* `fintype.trunc_equiv_of_card_eq` `fintype.equiv_of_card_eq`: Two fintypes of same cardinality are
  equivalent. See above.
* `fin.equiv_iff_eq`: `fin m ≃ fin n` iff `m = n`.
* `infinite α`: Typeclass saying that a type is infinite. Defined as `fintype α → false`.
* `not_fintype`: No `fintype` has an `infinite` instance.
* `infinite.nat_embedding`: An embedding of `ℕ` into an infinite type.

We also provide the following versions of the pigeonholes principle.
* `fintype.exists_ne_map_eq_of_card_lt` and `is_empty_of_card_lt`: Finitely many pigeons and
  pigeonholes. Weak formulation.
* `fintype.exists_ne_map_eq_of_infinite`: Infinitely many pigeons in finitely many pigeonholes.
  Weak formulation.
* `fintype.exists_infinite_fiber`: Infinitely many pigeons in finitely many pigeonholes. Strong
  formulation.

Some more pigeonhole-like statements can be found in `data.fintype.card_embedding`.

## Instances

Among others, we provide `fintype` instances for
* A `subtype` of a fintype. See `fintype.subtype`.
* The `option` of a fintype.
* The product of two fintypes.
* The sum of two fintypes.
* `Prop`.

and `infinite` instances for
* specific types: `ℕ`, `ℤ`
* type constructors: `set α`, `finset α`, `multiset α`, `list α`, `α ⊕ β`, `α × β`

along with some machinery
* Types which have a surjection from/an injection to a `fintype` are themselves fintypes. See
  `fintype.of_injective` and `fintype.of_surjective`.
* Types which have an injection from/a surjection to an `infinite` type are themselves `infinite`.
  See `infinite.of_injective` and `infinite.of_surjective`.
-/

open_locale nat

universes u v

variables {α β γ : Type*}

/-- `fintype α` means that `α` is finite, i.e. there are only
  finitely many distinct elements of type `α`. The evidence of this
  is a finset `elems` (a list up to permutation without duplicates),
  together with a proof that everything of type `α` is in the list. -/
class fintype (α : Type*) :=
(elems [] : finset α)
(complete : ∀ x : α, x ∈ elems)

namespace finset
variable [fintype α]

/-- `univ` is the universal finite set of type `finset α` implied from
  the assumption `fintype α`. -/
def univ : finset α := fintype.elems α

@[simp] theorem mem_univ (x : α) : x ∈ (univ : finset α) :=
fintype.complete x

@[simp] theorem mem_univ_val : ∀ x, x ∈ (univ : finset α).1 := mem_univ

lemma eq_univ_iff_forall {s : finset α} : s = univ ↔ ∀ x, x ∈ s := by simp [ext_iff]

@[simp] lemma coe_univ : ↑(univ : finset α) = (set.univ : set α) :=
by ext; simp

lemma univ_nonempty_iff : (univ : finset α).nonempty ↔ nonempty α :=
by rw [← coe_nonempty, coe_univ, set.nonempty_iff_univ_nonempty]

lemma univ_nonempty [nonempty α] : (univ : finset α).nonempty :=
univ_nonempty_iff.2 ‹_›

lemma univ_eq_empty_iff : (univ : finset α) = ∅ ↔ is_empty α :=
by rw [← not_nonempty_iff, ← univ_nonempty_iff, not_nonempty_iff_eq_empty]

@[simp] lemma univ_eq_empty [is_empty α] : (univ : finset α) = ∅ := univ_eq_empty_iff.2 ‹_›

@[simp] lemma univ_unique [unique α] : (univ : finset α) = {default} :=
finset.ext $ λ x, iff_of_true (mem_univ _) $ mem_singleton.2 $ subsingleton.elim x default

@[simp] theorem subset_univ (s : finset α) : s ⊆ univ := λ a _, mem_univ a

instance : order_top (finset α) :=
{ top := univ,
  le_top := subset_univ }

section boolean_algebra
variables [decidable_eq α] {s : finset α} {a : α}

instance : boolean_algebra (finset α) :=
{ compl := λ s, univ \ s,
  inf_compl_le_bot := λ s x hx, by simpa using hx,
  top_le_sup_compl := λ s x hx, by simp,
  sdiff_eq := λ s t, by simp [ext_iff, compl],
  ..finset.order_top,
  ..finset.order_bot,
  ..finset.generalized_boolean_algebra }

lemma compl_eq_univ_sdiff (s : finset α) : sᶜ = univ \ s := rfl

@[simp] lemma mem_compl : a ∈ sᶜ ↔ a ∉ s := by simp [compl_eq_univ_sdiff]

lemma not_mem_compl : a ∉ sᶜ ↔ a ∈ s := by rw [mem_compl, not_not]

@[simp, norm_cast] lemma coe_compl (s : finset α) : ↑(sᶜ) = (↑s : set α)ᶜ :=
set.ext $ λ x, mem_compl

@[simp] lemma compl_empty : (∅ : finset α)ᶜ = univ := compl_bot

@[simp] lemma union_compl (s : finset α) : s ∪ sᶜ = univ := sup_compl_eq_top

@[simp] lemma inter_compl (s : finset α) : s ∩ sᶜ = ∅ := inf_compl_eq_bot

@[simp] lemma compl_union (s t : finset α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

@[simp] lemma compl_inter (s t : finset α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := compl_inf

@[simp] lemma compl_erase : (s.erase a)ᶜ = insert a sᶜ :=
by { ext, simp only [or_iff_not_imp_left, mem_insert, not_and, mem_compl, mem_erase] }

@[simp] lemma compl_insert : (insert a s)ᶜ = sᶜ.erase a :=
by { ext, simp only [not_or_distrib, mem_insert, iff_self, mem_compl, mem_erase] }

@[simp] lemma insert_compl_self (x : α) : insert x ({x}ᶜ : finset α) = univ :=
by rw [←compl_erase, erase_singleton, compl_empty]

@[simp] lemma compl_filter (p : α → Prop) [decidable_pred p] [Π x, decidable (¬p x)] :
  (univ.filter p)ᶜ = univ.filter (λ x, ¬p x) :=
(filter_not _ _).symm

lemma compl_ne_univ_iff_nonempty (s : finset α) : sᶜ ≠ univ ↔ s.nonempty :=
by simp [eq_univ_iff_forall, finset.nonempty]

lemma compl_singleton (a : α) : ({a} : finset α)ᶜ = univ.erase a :=
by rw [compl_eq_univ_sdiff, sdiff_singleton_eq_erase]

end boolean_algebra

@[simp] lemma univ_inter [decidable_eq α] (s : finset α) :
  univ ∩ s = s := ext $ λ a, by simp

@[simp] lemma inter_univ [decidable_eq α] (s : finset α) :
  s ∩ univ = s :=
by rw [inter_comm, univ_inter]

@[simp] lemma piecewise_univ [Π i : α, decidable (i ∈ (univ : finset α))]
  {δ : α → Sort*} (f g : Π i, δ i) : univ.piecewise f g = f :=
by { ext i, simp [piecewise] }

lemma piecewise_compl [decidable_eq α] (s : finset α) [Π i : α, decidable (i ∈ s)]
  [Π i : α, decidable (i ∈ sᶜ)] {δ : α → Sort*} (f g : Π i, δ i) :
  sᶜ.piecewise f g = s.piecewise g f :=
by { ext i, simp [piecewise] }

@[simp] lemma piecewise_erase_univ {δ : α → Sort*} [decidable_eq α] (a : α) (f g : Π a, δ a) :
  (finset.univ.erase a).piecewise f g = function.update f a (g a) :=
by rw [←compl_singleton, piecewise_compl, piecewise_singleton]

lemma univ_map_equiv_to_embedding {α β : Type*} [fintype α] [fintype β] (e : α ≃ β) :
  univ.map e.to_embedding = univ :=
eq_univ_iff_forall.mpr (λ b, mem_map.mpr ⟨e.symm b, mem_univ _, by simp⟩)

@[simp] lemma univ_filter_exists (f : α → β) [fintype β]
  [decidable_pred (λ y, ∃ x, f x = y)] [decidable_eq β] :
  finset.univ.filter (λ y, ∃ x, f x = y) = finset.univ.image f :=
by { ext, simp }

/-- Note this is a special case of `(finset.image_preimage f univ _).symm`. -/
lemma univ_filter_mem_range (f : α → β) [fintype β]
  [decidable_pred (λ y, y ∈ set.range f)] [decidable_eq β] :
  finset.univ.filter (λ y, y ∈ set.range f) = finset.univ.image f :=
univ_filter_exists f

/-- A special case of `finset.sup_eq_supr` that omits the useless `x ∈ univ` binder. -/
lemma sup_univ_eq_supr [complete_lattice β] (f : α → β) : finset.univ.sup f = supr f :=
(sup_eq_supr _ f).trans $ congr_arg _ $ funext $ λ a, supr_pos (mem_univ _)

/-- A special case of `finset.inf_eq_infi` that omits the useless `x ∈ univ` binder. -/
lemma inf_univ_eq_infi [complete_lattice β] (f : α → β) : finset.univ.inf f = infi f :=
sup_univ_eq_supr (by exact f : α → order_dual β)

@[simp] lemma fold_inf_univ [semilattice_inf α] [order_bot α] (a : α) :
  finset.univ.fold (⊓) a (λ x, x) = ⊥ :=
eq_bot_iff.2 $ ((finset.fold_op_rel_iff_and $ @_root_.le_inf_iff α _).1 le_rfl).2 ⊥ $
  finset.mem_univ _

@[simp] lemma fold_sup_univ [semilattice_sup α] [order_top α] (a : α) :
  finset.univ.fold (⊔) a (λ x, x) = ⊤ :=
@fold_inf_univ (order_dual α) ‹fintype α› _ _ _

end finset

open finset function

namespace fintype

instance decidable_pi_fintype {α} {β : α → Type*} [∀ a, decidable_eq (β a)] [fintype α] :
  decidable_eq (Π a, β a) :=
λ f g, decidable_of_iff (∀ a ∈ fintype.elems α, f a = g a)
  (by simp [function.funext_iff, fintype.complete])

instance decidable_forall_fintype {p : α → Prop} [decidable_pred p] [fintype α] :
  decidable (∀ a, p a) :=
decidable_of_iff (∀ a ∈ @univ α _, p a) (by simp)

instance decidable_exists_fintype {p : α → Prop} [decidable_pred p] [fintype α] :
  decidable (∃ a, p a) :=
decidable_of_iff (∃ a ∈ @univ α _, p a) (by simp)

instance decidable_mem_range_fintype [fintype α] [decidable_eq β] (f : α → β) :
  decidable_pred (∈ set.range f) :=
λ x, fintype.decidable_exists_fintype

section bundled_homs

instance decidable_eq_equiv_fintype [decidable_eq β] [fintype α] :
  decidable_eq (α ≃ β) :=
λ a b, decidable_of_iff (a.1 = b.1) equiv.coe_fn_injective.eq_iff

instance decidable_eq_embedding_fintype [decidable_eq β] [fintype α] :
  decidable_eq (α ↪ β) :=
λ a b, decidable_of_iff ((a : α → β) = b) function.embedding.coe_injective.eq_iff

@[to_additive]
instance decidable_eq_one_hom_fintype [decidable_eq β] [fintype α] [has_one α] [has_one β]:
  decidable_eq (one_hom α β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff one_hom.coe_inj)

@[to_additive]
instance decidable_eq_mul_hom_fintype [decidable_eq β] [fintype α] [has_mul α] [has_mul β]:
  decidable_eq (mul_hom α β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff mul_hom.coe_inj)

@[to_additive]
instance decidable_eq_monoid_hom_fintype [decidable_eq β] [fintype α]
  [mul_one_class α] [mul_one_class β]:
  decidable_eq (α →* β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff monoid_hom.coe_inj)

instance decidable_eq_monoid_with_zero_hom_fintype [decidable_eq β] [fintype α]
  [mul_zero_one_class α] [mul_zero_one_class β] :
  decidable_eq (α →*₀ β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff monoid_with_zero_hom.coe_inj)

instance decidable_eq_ring_hom_fintype [decidable_eq β] [fintype α]
  [semiring α] [semiring β]:
  decidable_eq (α →+* β) :=
λ a b, decidable_of_iff ((a : α → β) = b) (injective.eq_iff ring_hom.coe_inj)

end bundled_homs

instance decidable_injective_fintype [decidable_eq α] [decidable_eq β] [fintype α] :
  decidable_pred (injective : (α → β) → Prop) := λ x, by unfold injective; apply_instance

instance decidable_surjective_fintype [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (surjective : (α → β) → Prop) := λ x, by unfold surjective; apply_instance

instance decidable_bijective_fintype [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (bijective : (α → β) → Prop) := λ x, by unfold bijective; apply_instance

instance decidable_right_inverse_fintype [decidable_eq α] [fintype α] (f : α → β) (g : β → α) :
  decidable (function.right_inverse f g) :=
show decidable (∀ x, g (f x) = x), by apply_instance

instance decidable_left_inverse_fintype [decidable_eq β] [fintype β] (f : α → β) (g : β → α) :
  decidable (function.left_inverse f g) :=
show decidable (∀ x, f (g x) = x), by apply_instance

lemma exists_max [fintype α] [nonempty α] {β : Type*} [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x ≤ f x₀ :=
by simpa using exists_max_image univ f univ_nonempty

lemma exists_min [fintype α] [nonempty α]
  {β : Type*} [linear_order β] (f : α → β) :
  ∃ x₀ : α, ∀ x, f x₀ ≤ f x :=
by simpa using exists_min_image univ f univ_nonempty

/-- Construct a proof of `fintype α` from a universal multiset -/
def of_multiset [decidable_eq α] (s : multiset α) (H : ∀ x : α, x ∈ s) :
  fintype α :=
⟨s.to_finset, by simpa using H⟩

/-- Construct a proof of `fintype α` from a universal list -/
def of_list [decidable_eq α] (l : list α) (H : ∀ x : α, x ∈ l) :
  fintype α :=
⟨l.to_finset, by simpa using H⟩

theorem exists_univ_list (α) [fintype α] :
  ∃ l : list α, l.nodup ∧ ∀ x : α, x ∈ l :=
let ⟨l, e⟩ := quotient.exists_rep (@univ α _).1 in
by have := and.intro univ.2 mem_univ_val;
   exact ⟨_, by rwa ←e at this⟩

/-- `card α` is the number of elements in `α`, defined when `α` is a fintype. -/
def card (α) [fintype α] : ℕ := (@univ α _).card

/-- There is (computably) an equivalence between `α` and `fin (card α)`.

Since it is not unique and depends on which permutation
of the universe list is used, the equivalence is wrapped in `trunc` to
preserve computability.

See `fintype.equiv_fin` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.

See `fintype.trunc_fin_bijection` for a version without `[decidable_eq α]`.
-/
def trunc_equiv_fin (α) [decidable_eq α] [fintype α] : trunc (α ≃ fin (card α)) :=
by { unfold card finset.card,
     exact quot.rec_on_subsingleton (@univ α _).1
       (λ l (h : ∀ x : α, x ∈ l) (nd : l.nodup),
         trunc.mk (nd.nth_le_equiv_of_forall_mem_list _ h).symm)
       mem_univ_val univ.2 }

/-- There is (noncomputably) an equivalence between `α` and `fin (card α)`.

See `fintype.trunc_equiv_fin` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq`
for an equiv `α ≃ fin n` given `fintype.card α = n`.
-/
noncomputable def equiv_fin (α) [fintype α] : α ≃ fin (card α) :=
by { letI := classical.dec_eq α, exact (trunc_equiv_fin α).out }

/-- There is (computably) a bijection between `fin (card α)` and `α`.

Since it is not unique and depends on which permutation
of the universe list is used, the bijection is wrapped in `trunc` to
preserve computability.

See `fintype.trunc_equiv_fin` for a version that gives an equivalence
given `[decidable_eq α]`.
-/
def trunc_fin_bijection (α) [fintype α] :
  trunc {f : fin (card α) → α // bijective f} :=
by { dunfold card finset.card,
     exact quot.rec_on_subsingleton (@univ α _).1
       (λ l (h : ∀ x : α, x ∈ l) (nd : l.nodup),
         trunc.mk (nd.nth_le_bijection_of_forall_mem_list _ h))
       mem_univ_val univ.2 }

instance (α : Type*) : subsingleton (fintype α) :=
⟨λ ⟨s₁, h₁⟩ ⟨s₂, h₂⟩, by congr; simp [finset.ext_iff, h₁, h₂]⟩

/-- Given a predicate that can be represented by a finset, the subtype
associated to the predicate is a fintype. -/
protected def subtype {p : α → Prop} (s : finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
  fintype {x // p x} :=
⟨⟨multiset.pmap subtype.mk s.1 (λ x, (H x).1),
  multiset.nodup_pmap (λ a _ b _, congr_arg subtype.val) s.2⟩,
λ ⟨x, px⟩, multiset.mem_pmap.2 ⟨x, (H x).2 px, rfl⟩⟩

theorem subtype_card {p : α → Prop} (s : finset α) (H : ∀ x : α, x ∈ s ↔ p x) :
  @card {x // p x} (fintype.subtype s H) = s.card :=
multiset.card_pmap _ _ _

theorem card_of_subtype {p : α → Prop} (s : finset α) (H : ∀ x : α, x ∈ s ↔ p x)
  [fintype {x // p x}] :
  card {x // p x} = s.card :=
by { rw ← subtype_card s H, congr }

/-- Construct a fintype from a finset with the same elements. -/
def of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : fintype p :=
fintype.subtype s H

@[simp] theorem card_of_finset {p : set α} (s : finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) :
  @fintype.card p (of_finset s H) = s.card :=
fintype.subtype_card s H

theorem card_of_finset' {p : set α} (s : finset α)
  (H : ∀ x, x ∈ s ↔ x ∈ p) [fintype p] : fintype.card p = s.card :=
by rw ←card_of_finset s H; congr

/-- If `f : α → β` is a bijection and `α` is a fintype, then `β` is also a fintype. -/
def of_bijective [fintype α] (f : α → β) (H : function.bijective f) : fintype β :=
⟨univ.map ⟨f, H.1⟩,
λ b, let ⟨a, e⟩ := H.2 b in e ▸ mem_map_of_mem _ (mem_univ _)⟩

/-- If `f : α → β` is a surjection and `α` is a fintype, then `β` is also a fintype. -/
def of_surjective [decidable_eq β] [fintype α] (f : α → β) (H : function.surjective f) :
  fintype β :=
⟨univ.image f, λ b, let ⟨a, e⟩ := H b in e ▸ mem_image_of_mem _ (mem_univ _)⟩

end fintype

section inv

namespace function

variables [fintype α] [decidable_eq β]

namespace injective

variables {f : α → β} (hf : function.injective f)

/--
The inverse of an `hf : injective` function `f : α → β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f hf).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : set.range f → α :=
λ b, finset.choose (λ a, f a = b) finset.univ ((exists_unique_congr (by simp)).mp
  (hf.exists_unique_of_mem_range b.property))

lemma left_inv_of_inv_of_mem_range (b : set.range f) :
  f (hf.inv_of_mem_range b) = b :=
(finset.choose_spec (λ a, f a = b) _ _).right

@[simp] lemma right_inv_of_inv_of_mem_range (a : α) :
  hf.inv_of_mem_range (⟨f a, set.mem_range_self a⟩) = a :=
hf (finset.choose_spec (λ a', f a' = f a) _ _).right

lemma inv_fun_restrict [nonempty α] :
  (set.range f).restrict (inv_fun f) = hf.inv_of_mem_range :=
begin
  ext ⟨b, h⟩,
  apply hf,
  simp [hf.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
end

lemma inv_of_mem_range_surjective : function.surjective hf.inv_of_mem_range :=
λ a, ⟨⟨f a, set.mem_range_self a⟩, by simp⟩

end injective

namespace embedding
variables (f : α ↪ β) (b : set.range f)

/--
The inverse of an embedding `f : α ↪ β`, of the type `↥(set.range f) → α`.
This is the computable version of `function.inv_fun` that requires `fintype α` and `decidable_eq β`,
or the function version of applying `(equiv.of_injective f f.injective).symm`.
This function should not usually be used for actual computation because for most cases,
an explicit inverse can be stated that has better computational properties.
This function computes by checking all terms `a : α` to find the `f a = b`, so it is O(N) where
`N = fintype.card α`.
-/
def inv_of_mem_range : α :=
f.injective.inv_of_mem_range b

@[simp] lemma left_inv_of_inv_of_mem_range :
  f (f.inv_of_mem_range b) = b :=
f.injective.left_inv_of_inv_of_mem_range b

@[simp] lemma right_inv_of_inv_of_mem_range (a : α) :
  f.inv_of_mem_range ⟨f a, set.mem_range_self a⟩ = a :=
f.injective.right_inv_of_inv_of_mem_range a

lemma inv_fun_restrict [nonempty α] :
  (set.range f).restrict (inv_fun f) = f.inv_of_mem_range :=
begin
  ext ⟨b, h⟩,
  apply f.injective,
  simp [f.left_inv_of_inv_of_mem_range, @inv_fun_eq _ _ _ f b (set.mem_range.mp h)]
end

lemma inv_of_mem_range_surjective : function.surjective f.inv_of_mem_range :=
λ a, ⟨⟨f a, set.mem_range_self a⟩, by simp⟩

end embedding

end function

end inv

namespace fintype

/-- Given an injective function to a fintype, the domain is also a
fintype. This is noncomputable because injectivity alone cannot be
used to construct preimages. -/
noncomputable def of_injective [fintype β] (f : α → β) (H : function.injective f) : fintype α :=
by letI := classical.dec; exact
if hα : nonempty α then by letI := classical.inhabited_of_nonempty hα;
  exact of_surjective (inv_fun f) (inv_fun_surjective H)
else ⟨∅, λ x, (hα ⟨x⟩).elim⟩

/-- If `f : α ≃ β` and `α` is a fintype, then `β` is also a fintype. -/
def of_equiv (α : Type*) [fintype α] (f : α ≃ β) : fintype β := of_bijective _ f.bijective

theorem of_equiv_card [fintype α] (f : α ≃ β) :
  @card β (of_equiv α f) = card α :=
multiset.card_map _ _

theorem card_congr {α β} [fintype α] [fintype β] (f : α ≃ β) : card α = card β :=
by rw ← of_equiv_card f; congr

@[congr]
lemma card_congr' {α β} [fintype α] [fintype β] (h : α = β) : card α = card β :=
card_congr (by rw h)

section

variables [fintype α] [fintype β]

/-- If the cardinality of `α` is `n`, there is computably a bijection between `α` and `fin n`.

See `fintype.equiv_fin_of_card_eq` for the noncomputable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
def trunc_equiv_fin_of_card_eq [decidable_eq α] {n : ℕ} (h : fintype.card α = n) :
  trunc (α ≃ fin n) :=
(trunc_equiv_fin α).map (λ e, e.trans (fin.cast h).to_equiv)


/-- If the cardinality of `α` is `n`, there is noncomputably a bijection between `α` and `fin n`.

See `fintype.trunc_equiv_fin_of_card_eq` for the computable definition,
and `fintype.trunc_equiv_fin` and `fintype.equiv_fin` for the bijection `α ≃ fin (card α)`.
-/
noncomputable def equiv_fin_of_card_eq {n : ℕ} (h : fintype.card α = n) :
  α ≃ fin n :=
by { letI := classical.dec_eq α, exact (trunc_equiv_fin_of_card_eq h).out }

/-- Two `fintype`s with the same cardinality are (computably) in bijection.

See `fintype.equiv_of_card_eq` for the noncomputable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
def trunc_equiv_of_card_eq [decidable_eq α] [decidable_eq β] (h : card α = card β) :
  trunc (α ≃ β) :=
(trunc_equiv_fin_of_card_eq h).bind (λ e, (trunc_equiv_fin β).map (λ e', e.trans e'.symm))

/-- Two `fintype`s with the same cardinality are (noncomputably) in bijection.

See `fintype.trunc_equiv_of_card_eq` for the computable version,
and `fintype.trunc_equiv_fin_of_card_eq` and `fintype.equiv_fin_of_card_eq` for
the specialization to `fin`.
-/
noncomputable def equiv_of_card_eq (h : card α = card β) : α ≃ β :=
by { letI := classical.dec_eq α, letI := classical.dec_eq β,
     exact (trunc_equiv_of_card_eq h).out }

end

theorem card_eq {α β} [F : fintype α] [G : fintype β] : card α = card β ↔ nonempty (α ≃ β) :=
⟨λ h, by { haveI := classical.prop_decidable, exact (trunc_equiv_of_card_eq h).nonempty },
 λ ⟨f⟩, card_congr f⟩

/-- Any subsingleton type with a witness is a fintype (with one term). -/
def of_subsingleton (a : α) [subsingleton α] : fintype α :=
⟨{a}, λ b, finset.mem_singleton.2 (subsingleton.elim _ _)⟩

@[simp] theorem univ_of_subsingleton (a : α) [subsingleton α] :
  @univ _ (of_subsingleton a) = {a} := rfl

/-- Note: this lemma is specifically about `fintype.of_subsingleton`. For a statement about
arbitrary `fintype` instances, use either `fintype.card_le_one_iff_subsingleton` or
`fintype.card_unique`. -/
@[simp] theorem card_of_subsingleton (a : α) [subsingleton α] :
  @fintype.card _ (of_subsingleton a) = 1 := rfl

@[simp] theorem card_unique [unique α] [h : fintype α] :
  fintype.card α = 1 :=
subsingleton.elim (of_subsingleton default) h ▸ card_of_subsingleton _

@[priority 100] -- see Note [lower instance priority]
instance of_is_empty [is_empty α] : fintype α := ⟨∅, is_empty_elim⟩

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `finset.univ_eq_empty`. -/
-- no-lint since while `finset.univ_eq_empty` can prove this, it isn't applicable for `dsimp`.
@[simp, nolint simp_nf] theorem univ_of_is_empty [is_empty α] : @univ α _ = ∅ := rfl

/-- Note: this lemma is specifically about `fintype.of_is_empty`. For a statement about
arbitrary `fintype` instances, use `fintype.card_eq_zero_iff`. -/
@[simp] theorem card_of_is_empty [is_empty α] : fintype.card α = 0 := rfl

open_locale classical
variables (α)

/-- Any subsingleton type is (noncomputably) a fintype (with zero or one term). -/
@[priority 5] -- see Note [lower instance priority]
noncomputable instance of_subsingleton' [subsingleton α] : fintype α :=
if h : nonempty α then
  of_subsingleton (nonempty.some h)
else
  @fintype.of_is_empty _ $ not_nonempty_iff.mp h

end fintype

namespace set

/-- Construct a finset enumerating a set `s`, given a `fintype` instance.  -/
def to_finset (s : set α) [fintype s] : finset α :=
⟨(@finset.univ s _).1.map subtype.val,
 multiset.nodup_map (λ a b, subtype.eq) finset.univ.2⟩

@[congr]
lemma to_finset_congr {s t : set α} [fintype s] [fintype t] (h : s = t) :
  to_finset s = to_finset t :=
by cc

@[simp] theorem mem_to_finset {s : set α} [fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
by simp [to_finset]

@[simp] theorem mem_to_finset_val {s : set α} [fintype s] {a : α} : a ∈ s.to_finset.1 ↔ a ∈ s :=
mem_to_finset

-- We use an arbitrary `[fintype s]` instance here,
-- not necessarily coming from a `[fintype α]`.
@[simp]
lemma to_finset_card {α : Type*} (s : set α) [fintype s] :
  s.to_finset.card = fintype.card s :=
multiset.card_map subtype.val finset.univ.val

@[simp] theorem coe_to_finset (s : set α) [fintype s] : (↑s.to_finset : set α) = s :=
set.ext $ λ _, mem_to_finset

@[simp] theorem to_finset_inj {s t : set α} [fintype s] [fintype t] :
  s.to_finset = t.to_finset ↔ s = t :=
⟨λ h, by rw [←s.coe_to_finset, h, t.coe_to_finset], λ h, by simp [h]; congr⟩

@[simp, mono] theorem to_finset_mono {s t : set α} [fintype s] [fintype t] :
  s.to_finset ⊆ t.to_finset ↔ s ⊆ t :=
by simp [finset.subset_iff, set.subset_def]

@[simp, mono] theorem to_finset_strict_mono {s t : set α} [fintype s] [fintype t] :
  s.to_finset ⊂ t.to_finset ↔ s ⊂ t :=
begin
  rw [←lt_eq_ssubset, ←finset.lt_iff_ssubset, lt_iff_le_and_ne, lt_iff_le_and_ne],
  simp
end

@[simp] theorem to_finset_disjoint_iff [decidable_eq α] {s t : set α} [fintype s] [fintype t] :
  disjoint s.to_finset t.to_finset ↔ disjoint s t :=
⟨λ h x hx, h (by simpa using hx), λ h x hx, h (by simpa using hx)⟩

end set

lemma finset.card_univ [fintype α] : (finset.univ : finset α).card = fintype.card α :=
rfl

lemma finset.eq_univ_of_card [fintype α] (s : finset α) (hs : s.card = fintype.card α) :
  s = univ :=
eq_of_subset_of_card_le (subset_univ _) $ by rw [hs, finset.card_univ]

lemma finset.card_eq_iff_eq_univ [fintype α] (s : finset α) :
  s.card = fintype.card α ↔ s = finset.univ :=
⟨s.eq_univ_of_card, by { rintro rfl, exact finset.card_univ, }⟩

lemma finset.card_le_univ [fintype α] (s : finset α) :
  s.card ≤ fintype.card α :=
card_le_of_subset (subset_univ s)

lemma finset.card_lt_univ_of_not_mem [fintype α] {s : finset α} {x : α} (hx : x ∉ s) :
  s.card < fintype.card α :=
card_lt_card ⟨subset_univ s, not_forall.2 ⟨x, λ hx', hx (hx' $ mem_univ x)⟩⟩

lemma finset.card_lt_iff_ne_univ [fintype α] (s : finset α) :
  s.card < fintype.card α ↔ s ≠ finset.univ :=
s.card_le_univ.lt_iff_ne.trans (not_iff_not_of_iff s.card_eq_iff_eq_univ)

lemma finset.card_compl_lt_iff_nonempty [fintype α] [decidable_eq α] (s : finset α) :
  sᶜ.card < fintype.card α ↔ s.nonempty :=
sᶜ.card_lt_iff_ne_univ.trans s.compl_ne_univ_iff_nonempty

lemma finset.card_univ_diff [decidable_eq α] [fintype α] (s : finset α) :
  (finset.univ \ s).card = fintype.card α - s.card :=
finset.card_sdiff (subset_univ s)

lemma finset.card_compl [decidable_eq α] [fintype α] (s : finset α) :
  sᶜ.card = fintype.card α - s.card :=
finset.card_univ_diff s

instance (n : ℕ) : fintype (fin n) :=
⟨finset.fin_range n, finset.mem_fin_range⟩

lemma fin.univ_def (n : ℕ) : (univ : finset (fin n)) = finset.fin_range n := rfl

@[simp] theorem fintype.card_fin (n : ℕ) : fintype.card (fin n) = n :=
list.length_fin_range n

@[simp] lemma finset.card_fin (n : ℕ) : finset.card (finset.univ : finset (fin n)) = n :=
by rw [finset.card_univ, fintype.card_fin]

/-- `fin` as a map from `ℕ` to `Type` is injective. Note that since this is a statement about
equality of types, using it should be avoided if possible. -/
lemma fin_injective : function.injective fin :=
λ m n h,
  (fintype.card_fin m).symm.trans $ (fintype.card_congr $ equiv.cast h).trans (fintype.card_fin n)

/-- A reversed version of `fin.cast_eq_cast` that is easier to rewrite with. -/
theorem fin.cast_eq_cast' {n m : ℕ} (h : fin n = fin m) :
  cast h = ⇑(fin.cast $ fin_injective h) :=
(fin.cast_eq_cast _).symm

/-- The cardinality of `fin (bit0 k)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
lemma fintype.card_fin_even {k : ℕ} : fact (even (fintype.card (fin (bit0 k)))) :=
⟨by { rw [fintype.card_fin], exact even_bit0 k }⟩

lemma card_finset_fin_le {n : ℕ} (s : finset (fin n)) : s.card ≤ n :=
by simpa only [fintype.card_fin] using s.card_le_univ

lemma fin.equiv_iff_eq {m n : ℕ} : nonempty (fin m ≃ fin n) ↔ m = n :=
  ⟨λ ⟨h⟩, by simpa using fintype.card_congr h, λ h, ⟨equiv.cast $ h ▸ rfl ⟩ ⟩

@[simp] lemma fin.image_succ_above_univ {n : ℕ} (i : fin (n + 1)) :
  univ.image i.succ_above = {i}ᶜ :=
by { ext m, simp }

@[simp] lemma fin.image_succ_univ (n : ℕ) : (univ : finset (fin n)).image fin.succ = {0}ᶜ :=
by rw [← fin.succ_above_zero, fin.image_succ_above_univ]

@[simp] lemma fin.image_cast_succ (n : ℕ) :
  (univ : finset (fin n)).image fin.cast_succ = {fin.last n}ᶜ :=
by rw [← fin.succ_above_last, fin.image_succ_above_univ]

/-- Embed `fin n` into `fin (n + 1)` by prepending zero to the `univ` -/
lemma fin.univ_succ (n : ℕ) :
  (univ : finset (fin (n + 1))) = insert 0 (univ.image fin.succ) :=
by simp

/-- Embed `fin n` into `fin (n + 1)` by appending a new `fin.last n` to the `univ` -/
lemma fin.univ_cast_succ (n : ℕ) :
  (univ : finset (fin (n + 1))) = insert (fin.last n) (univ.image fin.cast_succ) :=
by simp

/-- Embed `fin n` into `fin (n + 1)` by inserting
around a specified pivot `p : fin (n + 1)` into the `univ` -/
lemma fin.univ_succ_above (n : ℕ) (p : fin (n + 1)) :
  (univ : finset (fin (n + 1))) = insert p (univ.image (fin.succ_above p)) :=
by simp

@[instance, priority 10] def unique.fintype {α : Type*} [unique α] : fintype α :=
fintype.of_subsingleton default

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance fintype.subtype_eq (y : α) : fintype {x // x = y} :=
fintype.subtype {y} (by simp)

/-- Short-circuit instance to decrease search for `unique.fintype`,
since that relies on a subsingleton elimination for `unique`. -/
instance fintype.subtype_eq' (y : α) : fintype {x // y = x} :=
fintype.subtype {y} (by simp [eq_comm])

@[simp] lemma fintype.card_subtype_eq (y : α) [fintype {x // x = y}] :
  fintype.card {x // x = y} = 1 :=
fintype.card_unique

@[simp] lemma fintype.card_subtype_eq' (y : α) [fintype {x // y = x}] :
  fintype.card {x // y = x} = 1 :=
fintype.card_unique

@[simp] theorem fintype.univ_empty : @univ empty _ = ∅ := rfl

@[simp] theorem fintype.card_empty : fintype.card empty = 0 := rfl

@[simp] theorem fintype.univ_pempty : @univ pempty _ = ∅ := rfl

@[simp] theorem fintype.card_pempty : fintype.card pempty = 0 := rfl

instance : fintype unit := fintype.of_subsingleton ()

theorem fintype.univ_unit : @univ unit _ = {()} := rfl

theorem fintype.card_unit : fintype.card unit = 1 := rfl

instance : fintype punit := fintype.of_subsingleton punit.star

@[simp] theorem fintype.univ_punit : @univ punit _ = {punit.star} := rfl

@[simp] theorem fintype.card_punit : fintype.card punit = 1 := rfl

instance : fintype bool := ⟨⟨tt ::ₘ ff ::ₘ 0, by simp⟩, λ x, by cases x; simp⟩

@[simp] theorem fintype.univ_bool : @univ bool _ = {tt, ff} := rfl

instance units_int.fintype : fintype ℤˣ :=
⟨{1, -1}, λ x, by cases int.units_eq_one_or x; simp *⟩

@[simp] lemma units_int.univ : (finset.univ : finset ℤˣ) = {1, -1} := rfl

instance additive.fintype : Π [fintype α], fintype (additive α) := id

instance multiplicative.fintype : Π [fintype α], fintype (multiplicative α) := id

@[simp] theorem fintype.card_units_int : fintype.card ℤˣ = 2 := rfl

@[simp] theorem fintype.card_bool : fintype.card bool = 2 := rfl

instance {α : Type*} [fintype α] : fintype (option α) :=
⟨univ.insert_none, λ a, by simp⟩

lemma univ_option (α : Type*) [fintype α] : (univ : finset (option α)) = insert_none univ := rfl

@[simp] theorem fintype.card_option {α : Type*} [fintype α] :
  fintype.card (option α) = fintype.card α + 1 :=
(finset.card_cons _).trans $ congr_arg2 _ (card_map _) rfl

instance {α : Type*} (β : α → Type*)
  [fintype α] [∀ a, fintype (β a)] : fintype (sigma β) :=
⟨univ.sigma (λ _, univ), λ ⟨a, b⟩, by simp⟩

@[simp] lemma finset.univ_sigma_univ {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  (univ : finset α).sigma (λ a, (univ : finset (β a))) = univ := rfl

instance (α β : Type*) [fintype α] [fintype β] : fintype (α × β) :=
⟨univ.product univ, λ ⟨a, b⟩, by simp⟩

@[simp] lemma finset.univ_product_univ {α β : Type*} [fintype α] [fintype β] :
  (univ : finset α).product (univ : finset β) = univ :=
rfl

@[simp] theorem fintype.card_prod (α β : Type*) [fintype α] [fintype β] :
  fintype.card (α × β) = fintype.card α * fintype.card β :=
card_product _ _

/-- Given that `α × β` is a fintype, `α` is also a fintype. -/
def fintype.prod_left {α β} [decidable_eq α] [fintype (α × β)] [nonempty β] : fintype α :=
⟨(fintype.elems (α × β)).image prod.fst,
  λ a, let ⟨b⟩ := ‹nonempty β› in by simp; exact ⟨b, fintype.complete _⟩⟩

/-- Given that `α × β` is a fintype, `β` is also a fintype. -/
def fintype.prod_right {α β} [decidable_eq β] [fintype (α × β)] [nonempty α] : fintype β :=
⟨(fintype.elems (α × β)).image prod.snd,
  λ b, let ⟨a⟩ := ‹nonempty α› in by simp; exact ⟨a, fintype.complete _⟩⟩

instance (α : Type*) [fintype α] : fintype (ulift α) :=
fintype.of_equiv _ equiv.ulift.symm

@[simp] theorem fintype.card_ulift (α : Type*) [fintype α] :
  fintype.card (ulift α) = fintype.card α :=
fintype.of_equiv_card _

instance (α : Type*) [fintype α] : fintype (plift α) :=
fintype.of_equiv _ equiv.plift.symm

@[simp] theorem fintype.card_plift (α : Type*) [fintype α] :
  fintype.card (plift α) = fintype.card α :=
fintype.of_equiv_card _

instance (α : Type*) [fintype α] : fintype (order_dual α) := ‹fintype α›

@[simp] lemma fintype.card_order_dual (α : Type*) [fintype α] :
  fintype.card (order_dual α) = fintype.card α := rfl

instance (α : Type*) [fintype α] : fintype (lex α) := ‹fintype α›

@[simp] lemma fintype.card_lex (α : Type*) [fintype α] :
  fintype.card (lex α) = fintype.card α := rfl

lemma univ_sum_type {α β : Type*} [fintype α] [fintype β] [fintype (α ⊕ β)] [decidable_eq (α ⊕ β)] :
  (univ : finset (α ⊕ β)) = map function.embedding.inl univ ∪ map function.embedding.inr univ :=
begin
  rw [eq_comm, eq_univ_iff_forall], simp only [mem_union, mem_map, exists_prop, mem_univ, true_and],
  rintro (x|y), exacts [or.inl ⟨x, rfl⟩, or.inr ⟨y, rfl⟩]
end

instance (α : Type u) (β : Type v) [fintype α] [fintype β] : fintype (α ⊕ β) :=
@fintype.of_equiv _ _ (@sigma.fintype _
    (λ b, cond b (ulift α) (ulift.{(max u v) v} β)) _
    (λ b, by cases b; apply ulift.fintype))
  ((equiv.sum_equiv_sigma_bool _ _).symm.trans
    (equiv.sum_congr equiv.ulift equiv.ulift))

/-- Given that `α ⊕ β` is a fintype, `α` is also a fintype. This is non-computable as it uses
that `sum.inl` is an injection, but there's no clear inverse if `α` is empty. -/
noncomputable def fintype.sum_left {α β} [fintype (α ⊕ β)] : fintype α :=
fintype.of_injective (sum.inl : α → α ⊕ β) sum.inl_injective

/-- Given that `α ⊕ β` is a fintype, `β` is also a fintype. This is non-computable as it uses
that `sum.inr` is an injection, but there's no clear inverse if `β` is empty. -/
noncomputable def fintype.sum_right {α β} [fintype (α ⊕ β)] : fintype β :=
fintype.of_injective (sum.inr : β → α ⊕ β) sum.inr_injective

@[simp] theorem fintype.card_sum [fintype α] [fintype β] :
  fintype.card (α ⊕ β) = fintype.card α + fintype.card β :=
begin
  classical,
  rw [←finset.card_univ, univ_sum_type, finset.card_union_eq],
  { simp [finset.card_univ] },
  { intros x hx,
    suffices : (∃ (a : α), sum.inl a = x) ∧ ∃ (b : β), sum.inr b = x,
    { obtain ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ := this,
      simpa using hb },
    simpa using hx }
end

/-- If the subtype of all-but-one elements is a `fintype` then the type itself is a `fintype`. -/
def fintype_of_fintype_ne (a : α) [decidable_pred (= a)] (h : fintype {b // b ≠ a}) : fintype α :=
fintype.of_equiv _ $ equiv.sum_compl (= a)

section finset

/-! ### `fintype (s : finset α)` -/

instance finset.fintype_coe_sort {α : Type u} (s : finset α) : fintype s :=
⟨s.attach, s.mem_attach⟩

@[simp] lemma finset.univ_eq_attach {α : Type u} (s : finset α) :
  (univ : finset s) = s.attach :=
rfl

end finset

namespace fintype
variables [fintype α] [fintype β]

lemma card_le_of_injective (f : α → β) (hf : function.injective f) : card α ≤ card β :=
finset.card_le_card_of_inj_on f (λ _ _, finset.mem_univ _) (λ _ _ _ _ h, hf h)

lemma card_le_of_embedding (f : α ↪ β) : card α ≤ card β := card_le_of_injective f f.2

lemma card_lt_of_injective_of_not_mem (f : α → β) (h : function.injective f)
  {b : β} (w : b ∉ set.range f) : card α < card β :=
calc card α = (univ.map ⟨f, h⟩).card : (card_map _).symm
... < card β : finset.card_lt_univ_of_not_mem $
                 by rwa [← mem_coe, coe_map, coe_univ, set.image_univ]

lemma card_lt_of_injective_not_surjective (f : α → β) (h : function.injective f)
  (h' : ¬function.surjective f) : card α < card β :=
let ⟨y, hy⟩ := not_forall.1 h' in card_lt_of_injective_of_not_mem f h hy

lemma card_le_of_surjective (f : α → β) (h : function.surjective f) : card β ≤ card α :=
card_le_of_injective _ (function.injective_surj_inv h)

lemma card_range_le {α β : Type*} (f : α → β) [fintype α] [fintype (set.range f)] :
  fintype.card (set.range f) ≤ fintype.card α :=
fintype.card_le_of_surjective (λ a, ⟨f a, by simp⟩) (λ ⟨_, a, ha⟩, ⟨a, by simpa using ha⟩)

/--
The pigeonhole principle for finitely many pigeons and pigeonholes.
This is the `fintype` version of `finset.exists_ne_map_eq_of_card_lt_of_maps_to`.
-/
lemma exists_ne_map_eq_of_card_lt (f : α → β) (h : fintype.card β < fintype.card α) :
  ∃ x y, x ≠ y ∧ f x = f y :=
let ⟨x, _, y, _, h⟩ := finset.exists_ne_map_eq_of_card_lt_of_maps_to h (λ x _, mem_univ (f x))
in ⟨x, y, h⟩

lemma card_eq_one_iff : card α = 1 ↔ (∃ x : α, ∀ y, y = x) :=
by rw [←card_unit, card_eq]; exact
⟨λ ⟨a⟩, ⟨a.symm (), λ y, a.injective (subsingleton.elim _ _)⟩,
  λ ⟨x, hx⟩, ⟨⟨λ _, (), λ _, x, λ _, (hx _).trans (hx _).symm,
    λ _, subsingleton.elim _ _⟩⟩⟩

lemma card_eq_zero_iff : card α = 0 ↔ is_empty α :=
by rw [card, finset.card_eq_zero, univ_eq_empty_iff]

lemma card_eq_zero [is_empty α] : card α = 0 := card_eq_zero_iff.2 ‹_›

lemma card_eq_one_iff_nonempty_unique : card α = 1 ↔ nonempty (unique α) :=
⟨λ h, let ⟨d, h⟩ := fintype.card_eq_one_iff.mp h in ⟨{ default := d, uniq := h}⟩,
 λ ⟨h⟩, by exactI fintype.card_unique⟩

/-- A `fintype` with cardinality zero is equivalent to `empty`. -/
def card_eq_zero_equiv_equiv_empty : card α = 0 ≃ (α ≃ empty) :=
(equiv.of_iff card_eq_zero_iff).trans (equiv.equiv_empty_equiv α).symm

lemma card_pos_iff : 0 < card α ↔ nonempty α :=
pos_iff_ne_zero.trans $ not_iff_comm.mp $ not_nonempty_iff.trans card_eq_zero_iff.symm

lemma card_pos [h : nonempty α] : 0 < card α :=
card_pos_iff.mpr h

lemma card_ne_zero [nonempty α] : card α ≠ 0 :=
ne_of_gt card_pos

lemma card_le_one_iff : card α ≤ 1 ↔ (∀ a b : α, a = b) :=
let n := card α in
have hn : n = card α := rfl,
match n, hn with
| 0     := λ ha, ⟨λ h, λ a, (card_eq_zero_iff.1 ha.symm).elim a, λ _, ha ▸ nat.le_succ _⟩
| 1     := λ ha, ⟨λ h, λ a b, let ⟨x, hx⟩ := card_eq_one_iff.1 ha.symm in
  by rw [hx a, hx b],
    λ _, ha ▸ le_rfl⟩
| (n+2) := λ ha, ⟨λ h, by rw ← ha at h; exact absurd h dec_trivial,
  (λ h, card_unit ▸ card_le_of_injective (λ _, ())
    (λ _ _ _, h _ _))⟩
end

lemma card_le_one_iff_subsingleton : card α ≤ 1 ↔ subsingleton α :=
card_le_one_iff.trans subsingleton_iff.symm

lemma one_lt_card_iff_nontrivial : 1 < card α ↔ nontrivial α :=
begin
  classical,
  rw ←not_iff_not,
  push_neg,
  rw [not_nontrivial_iff_subsingleton, card_le_one_iff_subsingleton]
end

lemma exists_ne_of_one_lt_card (h : 1 < card α) (a : α) : ∃ b : α, b ≠ a :=
by { haveI : nontrivial α := one_lt_card_iff_nontrivial.1 h, exact exists_ne a }

lemma exists_pair_of_one_lt_card (h : 1 < card α) : ∃ (a b : α), a ≠ b :=
by { haveI : nontrivial α := one_lt_card_iff_nontrivial.1 h, exact exists_pair_ne α }

lemma card_eq_one_of_forall_eq {i : α} (h : ∀ j, j = i) : card α = 1 :=
fintype.card_eq_one_iff.2 ⟨i,h⟩

lemma one_lt_card [h : nontrivial α] : 1 < fintype.card α :=
fintype.one_lt_card_iff_nontrivial.mpr h

lemma one_lt_card_iff : 1 < card α ↔ ∃ a b : α, a ≠ b :=
one_lt_card_iff_nontrivial.trans nontrivial_iff

lemma two_lt_card_iff : 2 < card α ↔ ∃ a b c : α, a ≠ b ∧ a ≠ c ∧ b ≠ c :=
by simp_rw [←finset.card_univ, two_lt_card_iff, mem_univ, true_and]

lemma injective_iff_surjective {f : α → α} : injective f ↔ surjective f :=
by haveI := classical.prop_decidable; exact
have ∀ {f : α → α}, injective f → surjective f,
from λ f hinj x,
  have h₁ : image f univ = univ := eq_of_subset_of_card_le (subset_univ _)
    ((card_image_of_injective univ hinj).symm ▸ le_rfl),
  have h₂ : x ∈ image f univ := h₁.symm ▸ mem_univ _,
  exists_of_bex (mem_image.1 h₂),
⟨this,
  λ hsurj, has_left_inverse.injective
    ⟨surj_inv hsurj, left_inverse_of_surjective_of_right_inverse
      (this (injective_surj_inv _)) (right_inverse_surj_inv _)⟩⟩

lemma injective_iff_bijective {f : α → α} : injective f ↔ bijective f :=
by simp [bijective, injective_iff_surjective]

lemma surjective_iff_bijective {f : α → α} : surjective f ↔ bijective f :=
by simp [bijective, injective_iff_surjective]

lemma injective_iff_surjective_of_equiv {β : Type*} {f : α → β} (e : α ≃ β) :
  injective f ↔ surjective f :=
have injective (e.symm ∘ f) ↔ surjective (e.symm ∘ f), from injective_iff_surjective,
⟨λ hinj, by simpa [function.comp] using
  e.surjective.comp (this.1 (e.symm.injective.comp hinj)),
λ hsurj, by simpa [function.comp] using
  e.injective.comp (this.2 (e.symm.surjective.comp hsurj))⟩

lemma card_of_bijective {f : α → β} (hf : bijective f) : card α = card β :=
card_congr (equiv.of_bijective f hf)

lemma bijective_iff_injective_and_card (f : α → β) :
  bijective f ↔ injective f ∧ card α = card β :=
begin
  split,
  { intro h, exact ⟨h.1, card_of_bijective h⟩ },
  { rintro ⟨hf, h⟩,
    refine ⟨hf, _⟩,
    rwa ←injective_iff_surjective_of_equiv (equiv_of_card_eq h) }
end

lemma bijective_iff_surjective_and_card (f : α → β) :
  bijective f ↔ surjective f ∧ card α = card β :=
begin
  split,
  { intro h, exact ⟨h.2, card_of_bijective h⟩ },
  { rintro ⟨hf, h⟩,
    refine ⟨_, hf⟩,
    rwa injective_iff_surjective_of_equiv (equiv_of_card_eq h) }
end

lemma right_inverse_of_left_inverse_of_card_le {f : α → β} {g : β → α}
  (hfg : left_inverse f g) (hcard : card α ≤ card β) :
  right_inverse f g :=
have hsurj : surjective f, from surjective_iff_has_right_inverse.2 ⟨g, hfg⟩,
right_inverse_of_injective_of_left_inverse
  ((bijective_iff_surjective_and_card _).2
    ⟨hsurj, le_antisymm hcard (card_le_of_surjective f hsurj)⟩ ).1
  hfg

lemma left_inverse_of_right_inverse_of_card_le {f : α → β} {g : β → α}
  (hfg : right_inverse f g) (hcard : card β ≤ card α) :
  left_inverse f g :=
right_inverse_of_left_inverse_of_card_le hfg hcard

end fintype

lemma fintype.coe_image_univ [fintype α] [decidable_eq β] {f : α → β} :
  ↑(finset.image f finset.univ) = set.range f :=
by { ext x, simp }

instance list.subtype.fintype [decidable_eq α] (l : list α) : fintype {x // x ∈ l} :=
fintype.of_list l.attach l.mem_attach

instance multiset.subtype.fintype [decidable_eq α] (s : multiset α) : fintype {x // x ∈ s} :=
fintype.of_multiset s.attach s.mem_attach

instance finset.subtype.fintype (s : finset α) : fintype {x // x ∈ s} :=
⟨s.attach, s.mem_attach⟩

instance finset_coe.fintype (s : finset α) : fintype (↑s : set α) :=
finset.subtype.fintype s

@[simp] lemma fintype.card_coe (s : finset α) :
  fintype.card s = s.card := card_attach

lemma finset.attach_eq_univ {s : finset α} : s.attach = finset.univ := rfl

instance plift.fintype_Prop (p : Prop) [decidable p] : fintype (plift p) :=
⟨if h : p then {⟨h⟩} else ∅, λ ⟨h⟩, by simp [h]⟩

instance Prop.fintype : fintype Prop :=
⟨⟨true ::ₘ false ::ₘ 0, by simp [true_ne_false]⟩,
 classical.cases (by simp) (by simp)⟩

@[simp] lemma fintype.card_Prop : fintype.card Prop = 2 := rfl

instance subtype.fintype (p : α → Prop) [decidable_pred p] [fintype α] : fintype {x // p x} :=
fintype.subtype (univ.filter p) (by simp)

/- TODO Without the coercion arrow (`↥`) there is an elaboration bug;
it essentially infers `fintype.{v} (set.univ.{u} : set α)` with `v` and `u` distinct.
Reported in leanprover-community/lean#672 -/
@[simp] lemma set.to_finset_univ [fintype ↥(set.univ : set α)] [fintype α] :
  (set.univ : set α).to_finset = finset.univ :=
by { ext, simp only [set.mem_univ, mem_univ, set.mem_to_finset] }

@[simp] lemma set.to_finset_eq_empty_iff {s : set α} [fintype s] : s.to_finset = ∅ ↔ s = ∅ :=
by simp [ext_iff, set.ext_iff]

@[simp] lemma set.to_finset_empty : (∅ : set α).to_finset = ∅ :=
set.to_finset_eq_empty_iff.mpr rfl

@[simp] lemma set.to_finset_range [decidable_eq α] [fintype β] (f : β → α) [fintype (set.range f)] :
  (set.range f).to_finset = finset.univ.image f :=
by simp [ext_iff]

/-- A set on a fintype, when coerced to a type, is a fintype. -/
def set_fintype [fintype α] (s : set α) [decidable_pred (∈ s)] : fintype s :=
subtype.fintype (λ x, x ∈ s)

lemma set_fintype_card_le_univ [fintype α] (s : set α) [fintype ↥s] :
  fintype.card ↥s ≤ fintype.card α :=
fintype.card_le_of_embedding (function.embedding.subtype s)

lemma set_fintype_card_eq_univ_iff [fintype α] (s : set α) [fintype ↥s] :
  fintype.card s = fintype.card α ↔ s = set.univ :=
by rw [←set.to_finset_card, finset.card_eq_iff_eq_univ, ←set.to_finset_univ, set.to_finset_inj]

section
variables (α)

/-- The `αˣ` type is equivalent to a subtype of `α × α`. -/
@[simps]
def _root_.units_equiv_prod_subtype [monoid α] :
  αˣ ≃ {p : α × α // p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} :=
{ to_fun := λ u, ⟨(u, ↑u⁻¹), u.val_inv, u.inv_val⟩,
  inv_fun := λ p, units.mk (p : α × α).1 (p : α × α).2 p.prop.1 p.prop.2,
  left_inv := λ u, units.ext rfl,
  right_inv := λ p, subtype.ext $ prod.ext rfl rfl}

/-- In a `group_with_zero` `α`, the unit group `αˣ` is equivalent to the subtype of nonzero
elements. -/
@[simps]
def _root_.units_equiv_ne_zero [group_with_zero α] : αˣ ≃ {a : α // a ≠ 0} :=
⟨λ a, ⟨a, a.ne_zero⟩, λ a, units.mk0 _ a.prop, λ _, units.ext rfl, λ _, subtype.ext rfl⟩

end

instance [monoid α] [fintype α] [decidable_eq α] : fintype αˣ :=
fintype.of_equiv _ (units_equiv_prod_subtype α).symm

lemma fintype.card_units [group_with_zero α] [fintype α] [fintype αˣ] :
  fintype.card αˣ = fintype.card α - 1 :=
begin
  classical,
  rw [eq_comm, nat.sub_eq_iff_eq_add (fintype.card_pos_iff.2 ⟨(0 : α)⟩),
    fintype.card_congr (units_equiv_ne_zero α)],
  have := fintype.card_congr (equiv.sum_compl (= (0 : α))).symm,
  rwa [fintype.card_sum, add_comm, fintype.card_subtype_eq] at this,
end

namespace function.embedding

/-- An embedding from a `fintype` to itself can be promoted to an equivalence. -/
noncomputable def equiv_of_fintype_self_embedding [fintype α] (e : α ↪ α) : α ≃ α :=
equiv.of_bijective e (fintype.injective_iff_bijective.1 e.2)

@[simp]
lemma equiv_of_fintype_self_embedding_to_embedding [fintype α] (e : α ↪ α) :
  e.equiv_of_fintype_self_embedding.to_embedding = e :=
by { ext, refl, }

/-- If `‖β‖ < ‖α‖` there are no embeddings `α ↪ β`.
This is a formulation of the pigeonhole principle.

Note this cannot be an instance as it needs `h`. -/
@[simp] lemma is_empty_of_card_lt [fintype α] [fintype β]
  (h : fintype.card β < fintype.card α) : is_empty (α ↪ β) :=
⟨λ f, let ⟨x, y, ne, feq⟩ := fintype.exists_ne_map_eq_of_card_lt f h in ne $ f.injective feq⟩

/-- A constructive embedding of a fintype `α` in another fintype `β` when `card α ≤ card β`. -/
def trunc_of_card_le [fintype α] [fintype β] [decidable_eq α] [decidable_eq β]
  (h : fintype.card α ≤ fintype.card β) : trunc (α ↪ β) :=
(fintype.trunc_equiv_fin α).bind $ λ ea,
  (fintype.trunc_equiv_fin β).map $ λ eb,
    ea.to_embedding.trans ((fin.cast_le h).to_embedding.trans eb.symm.to_embedding)

lemma nonempty_of_card_le [fintype α] [fintype β]
  (h : fintype.card α ≤ fintype.card β) : nonempty (α ↪ β) :=
by { classical, exact (trunc_of_card_le h).nonempty }

lemma exists_of_card_le_finset [fintype α] {s : finset β} (h : fintype.card α ≤ s.card) :
  ∃ (f : α ↪ β), set.range f ⊆ s :=
begin
  rw ← fintype.card_coe at h,
  rcases nonempty_of_card_le h with ⟨f⟩,
  exact ⟨f.trans (embedding.subtype _), by simp [set.range_subset_iff]⟩
end

end function.embedding

@[simp]
lemma finset.univ_map_embedding {α : Type*} [fintype α] (e : α ↪ α) :
  univ.map e = univ :=
by rw [←e.equiv_of_fintype_self_embedding_to_embedding, univ_map_equiv_to_embedding]

namespace fintype

lemma card_lt_of_surjective_not_injective [fintype α] [fintype β] (f : α → β)
  (h : function.surjective f) (h' : ¬function.injective f) : card β < card α :=
card_lt_of_injective_not_surjective _ (function.injective_surj_inv h) $ λ hg,
have w : function.bijective (function.surj_inv h) := ⟨function.injective_surj_inv h, hg⟩,
h' $ (injective_iff_surjective_of_equiv (equiv.of_bijective _ w).symm).mpr h

variables [decidable_eq α] [fintype α] {δ : α → Type*}

/-- Given for all `a : α` a finset `t a` of `δ a`, then one can define the
finset `fintype.pi_finset t` of all functions taking values in `t a` for all `a`. This is the
analogue of `finset.pi` where the base finset is `univ` (but formally they are not the same, as
there is an additional condition `i ∈ finset.univ` in the `finset.pi` definition). -/
def pi_finset (t : Π a, finset (δ a)) : finset (Π a, δ a) :=
(finset.univ.pi t).map ⟨λ f a, f a (mem_univ a), λ _ _, by simp [function.funext_iff]⟩

@[simp] lemma mem_pi_finset {t : Π a, finset (δ a)} {f : Π a, δ a} :
  f ∈ pi_finset t ↔ ∀ a, f a ∈ t a :=
begin
  split,
  { simp only [pi_finset, mem_map, and_imp, forall_prop_of_true, exists_prop, mem_univ,
               exists_imp_distrib, mem_pi],
    rintro g hg hgf a,
    rw ← hgf,
    exact hg a },
  { simp only [pi_finset, mem_map, forall_prop_of_true, exists_prop, mem_univ, mem_pi],
    exact λ hf, ⟨λ a ha, f a, hf, rfl⟩ }
end

@[simp] lemma coe_pi_finset (t : Π a, finset (δ a)) :
  (pi_finset t : set (Π a, δ a)) = set.pi set.univ (λ a, t a) :=
set.ext $ λ x, by { rw set.mem_univ_pi, exact fintype.mem_pi_finset }

lemma pi_finset_subset (t₁ t₂ : Π a, finset (δ a)) (h : ∀ a, t₁ a ⊆ t₂ a) :
  pi_finset t₁ ⊆ pi_finset t₂ :=
λ g hg, mem_pi_finset.2 $ λ a, h a $ mem_pi_finset.1 hg a

lemma pi_finset_disjoint_of_disjoint [∀ a, decidable_eq (δ a)]
  (t₁ t₂ : Π a, finset (δ a)) {a : α} (h : disjoint (t₁ a) (t₂ a)) :
  disjoint (pi_finset t₁) (pi_finset t₂) :=
disjoint_iff_ne.2 $ λ f₁ hf₁ f₂ hf₂ eq₁₂,
disjoint_iff_ne.1 h (f₁ a) (mem_pi_finset.1 hf₁ a) (f₂ a) (mem_pi_finset.1 hf₂ a) (congr_fun eq₁₂ a)

end fintype

/-! ### pi -/

/-- A dependent product of fintypes, indexed by a fintype, is a fintype. -/
instance pi.fintype {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀ a, fintype (β a)] : fintype (Π a, β a) :=
⟨fintype.pi_finset (λ _, univ), by simp⟩

@[simp] lemma fintype.pi_finset_univ {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀ a, fintype (β a)] :
  fintype.pi_finset (λ a : α, (finset.univ : finset (β a))) = (finset.univ : finset (Π a, β a)) :=
rfl

instance d_array.fintype {n : ℕ} {α : fin n → Type*}
  [∀ n, fintype (α n)] : fintype (d_array n α) :=
fintype.of_equiv _ (equiv.d_array_equiv_fin _).symm

instance array.fintype {n : ℕ} {α : Type*} [fintype α] : fintype (array n α) :=
d_array.fintype

instance vector.fintype {α : Type*} [fintype α] {n : ℕ} : fintype (vector α n) :=
fintype.of_equiv _ (equiv.vector_equiv_fin _ _).symm

instance quotient.fintype [fintype α] (s : setoid α)
  [decidable_rel ((≈) : α → α → Prop)] : fintype (quotient s) :=
fintype.of_surjective quotient.mk (λ x, quotient.induction_on x (λ x, ⟨x, rfl⟩))

instance finset.fintype [fintype α] : fintype (finset α) :=
⟨univ.powerset, λ x, finset.mem_powerset.2 (finset.subset_univ _)⟩

-- irreducible due to this conversation on Zulip:
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/
-- topic/.60simp.60.20ignoring.20lemmas.3F/near/241824115
@[irreducible] instance function.embedding.fintype {α β} [fintype α] [fintype β]
  [decidable_eq α] [decidable_eq β] : fintype (α ↪ β) :=
fintype.of_equiv _ (equiv.subtype_injective_equiv_embedding α β)

instance [decidable_eq α] [fintype α] {n : ℕ} : fintype (sym.sym' α n) :=
quotient.fintype _

instance [decidable_eq α] [fintype α] {n : ℕ} : fintype (sym α n) :=
fintype.of_equiv _ sym.sym_equiv_sym'.symm

@[simp] lemma fintype.card_finset [fintype α] :
  fintype.card (finset α) = 2 ^ (fintype.card α) :=
finset.card_powerset finset.univ

lemma finset.mem_powerset_len_univ_iff [fintype α] {s : finset α} {k : ℕ} :
  s ∈ powerset_len k (univ : finset α) ↔ card s = k :=
mem_powerset_len.trans $ and_iff_right $ subset_univ _

@[simp] lemma finset.univ_filter_card_eq (α : Type*) [fintype α] (k : ℕ) :
  (finset.univ : finset (finset α)).filter (λ s, s.card = k) = finset.univ.powerset_len k :=
by { ext, simp [finset.mem_powerset_len] }

@[simp] lemma fintype.card_finset_len [fintype α] (k : ℕ) :
  fintype.card {s : finset α // s.card = k} = nat.choose (fintype.card α) k :=
by simp [fintype.subtype_card, finset.card_univ]

theorem fintype.card_subtype_le [fintype α] (p : α → Prop) [decidable_pred p] :
  fintype.card {x // p x} ≤ fintype.card α :=
fintype.card_le_of_embedding (function.embedding.subtype _)

theorem fintype.card_subtype_lt [fintype α] {p : α → Prop} [decidable_pred p]
  {x : α} (hx : ¬ p x) : fintype.card {x // p x} < fintype.card α :=
fintype.card_lt_of_injective_of_not_mem coe subtype.coe_injective $ by rwa subtype.range_coe_subtype

lemma fintype.card_subtype [fintype α] (p : α → Prop) [decidable_pred p] :
  fintype.card {x // p x} = ((finset.univ : finset α).filter p).card :=
begin
  refine fintype.card_of_subtype _ _,
  simp
end

lemma fintype.card_subtype_or (p q : α → Prop)
  [fintype {x // p x}] [fintype {x // q x}] [fintype {x // p x ∨ q x}] :
  fintype.card {x // p x ∨ q x} ≤ fintype.card {x // p x} + fintype.card {x // q x} :=
begin
  classical,
  convert fintype.card_le_of_embedding (subtype_or_left_embedding p q),
  rw fintype.card_sum
end

lemma fintype.card_subtype_or_disjoint (p q : α → Prop) (h : disjoint p q)
  [fintype {x // p x}] [fintype {x // q x}] [fintype {x // p x ∨ q x}] :
  fintype.card {x // p x ∨ q x} = fintype.card {x // p x} + fintype.card {x // q x} :=
begin
  classical,
  convert fintype.card_congr (subtype_or_equiv p q h),
  simp
end

theorem fintype.card_quotient_le [fintype α] (s : setoid α) [decidable_rel ((≈) : α → α → Prop)] :
  fintype.card (quotient s) ≤ fintype.card α :=
fintype.card_le_of_surjective _ (surjective_quotient_mk _)

theorem fintype.card_quotient_lt [fintype α] {s : setoid α} [decidable_rel ((≈) : α → α → Prop)]
  {x y : α} (h1 : x ≠ y) (h2 : x ≈ y) : fintype.card (quotient s) < fintype.card α :=
fintype.card_lt_of_surjective_not_injective _ (surjective_quotient_mk _) $ λ w,
h1 (w $ quotient.eq.mpr h2)

instance psigma.fintype {α : Type*} {β : α → Type*} [fintype α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
fintype.of_equiv _ (equiv.psigma_equiv_sigma _).symm

instance psigma.fintype_prop_left {α : Prop} {β : α → Type*} [decidable α] [∀ a, fintype (β a)] :
  fintype (Σ' a, β a) :=
if h : α then fintype.of_equiv (β h) ⟨λ x, ⟨h, x⟩, psigma.snd, λ _, rfl, λ ⟨_, _⟩, rfl⟩
else ⟨∅, λ x, h x.1⟩

instance psigma.fintype_prop_right {α : Type*} {β : α → Prop} [∀ a, decidable (β a)] [fintype α] :
  fintype (Σ' a, β a) :=
fintype.of_equiv {a // β a} ⟨λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, ⟨x, y⟩, λ ⟨x, y⟩, rfl, λ ⟨x, y⟩, rfl⟩

instance psigma.fintype_prop_prop {α : Prop} {β : α → Prop} [decidable α] [∀ a, decidable (β a)] :
  fintype (Σ' a, β a) :=
if h : ∃ a, β a then ⟨{⟨h.fst, h.snd⟩}, λ ⟨_, _⟩, by simp⟩ else ⟨∅, λ ⟨x, y⟩, h ⟨x, y⟩⟩

instance set.fintype [fintype α] : fintype (set α) :=
⟨(@finset.univ α _).powerset.map ⟨coe, coe_injective⟩, λ s, begin
  classical, refine mem_map.2 ⟨finset.univ.filter s, mem_powerset.2 (subset_univ _), _⟩,
  apply (coe_filter _ _).trans, rw [coe_univ, set.sep_univ], refl
end⟩

@[simp] lemma fintype.card_set [fintype α] : fintype.card (set α) = 2 ^ fintype.card α :=
(finset.card_map _).trans (finset.card_powerset _)

instance pfun_fintype (p : Prop) [decidable p] (α : p → Type*)
  [Π hp, fintype (α hp)] : fintype (Π hp : p, α hp) :=
if hp : p then fintype.of_equiv (α hp) ⟨λ a _, a, λ f, f hp, λ _, rfl, λ _, rfl⟩
          else ⟨singleton (λ h, (hp h).elim), by simp [hp, function.funext_iff]⟩

@[simp] lemma finset.univ_pi_univ {α : Type*} {β : α → Type*}
  [decidable_eq α] [fintype α] [∀ a, fintype (β a)] :
  finset.univ.pi (λ a : α, (finset.univ : finset (β a))) = finset.univ :=
by { ext, simp }

lemma mem_image_univ_iff_mem_range
  {α β : Type*} [fintype α] [decidable_eq β] {f : α → β} {b : β} :
  b ∈ univ.image f ↔ b ∈ set.range f :=
by simp

/-- An auxiliary function for `quotient.fin_choice`.  Given a
collection of setoids indexed by a type `ι`, a (finite) list `l` of
indices, and a function that for each `i ∈ l` gives a term of the
corresponding quotient type, then there is a corresponding term in the
quotient of the product of the setoids indexed by `l`. -/
def quotient.fin_choice_aux {ι : Type*} [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)] :
  Π (l : list ι), (Π i ∈ l, quotient (S i)) → @quotient (Π i ∈ l, α i) (by apply_instance)
| []       f := ⟦λ i, false.elim⟧
| (i :: l) f := begin
  refine quotient.lift_on₂ (f i (list.mem_cons_self _ _))
    (quotient.fin_choice_aux l (λ j h, f j (list.mem_cons_of_mem _ h)))
    _ _,
  exact λ a l, ⟦λ j h,
    if e : j = i then by rw e; exact a else
    l _ (h.resolve_left e)⟧,
  refine λ a₁ l₁ a₂ l₂ h₁ h₂, quotient.sound (λ j h, _),
  by_cases e : j = i; simp [e],
  { subst j, exact h₁ },
  { exact h₂ _ _ }
end

theorem quotient.fin_choice_aux_eq {ι : Type*} [decidable_eq ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)] :
  ∀ (l : list ι) (f : Π i ∈ l, α i), quotient.fin_choice_aux l (λ i h, ⟦f i h⟧) = ⟦f⟧
| []       f := quotient.sound (λ i h, h.elim)
| (i :: l) f := begin
  simp [quotient.fin_choice_aux, quotient.fin_choice_aux_eq l],
  refine quotient.sound (λ j h, _),
  by_cases e : j = i; simp [e],
  subst j, refl
end

/-- Given a collection of setoids indexed by a fintype `ι` and a
function that for each `i : ι` gives a term of the corresponding
quotient type, then there is corresponding term in the quotient of the
product of the setoids. -/
def quotient.fin_choice {ι : Type*} [decidable_eq ι] [fintype ι]
  {α : ι → Type*} [S : ∀ i, setoid (α i)]
  (f : Π i, quotient (S i)) : @quotient (Π i, α i) (by apply_instance) :=
quotient.lift_on (@quotient.rec_on _ _ (λ l : multiset ι,
    @quotient (Π i ∈ l, α i) (by apply_instance))
    finset.univ.1
    (λ l, quotient.fin_choice_aux l (λ i _, f i))
    (λ a b h, begin
      have := λ a, quotient.fin_choice_aux_eq a (λ i h, quotient.out (f i)),
      simp [quotient.out_eq] at this,
      simp [this],
      let g := λ a:multiset ι, ⟦λ (i : ι) (h : i ∈ a), quotient.out (f i)⟧,
      refine eq_of_heq ((eq_rec_heq _ _).trans (_ : g a == g b)),
      congr' 1, exact quotient.sound h,
    end))
  (λ f, ⟦λ i, f i (finset.mem_univ _)⟧)
  (λ a b h, quotient.sound $ λ i, h _ _)

theorem quotient.fin_choice_eq {ι : Type*} [decidable_eq ι] [fintype ι]
  {α : ι → Type*} [∀ i, setoid (α i)]
  (f : Π i, α i) : quotient.fin_choice (λ i, ⟦f i⟧) = ⟦f⟧ :=
begin
  let q, swap, change quotient.lift_on q _ _ = _,
  have : q = ⟦λ i h, f i⟧,
  { dsimp [q],
    exact quotient.induction_on
      (@finset.univ ι _).1 (λ l, quotient.fin_choice_aux_eq _ _) },
  simp [this], exact setoid.refl _
end

section equiv

open list equiv equiv.perm

variables [decidable_eq α] [decidable_eq β]

/-- Given a list, produce a list of all permutations of its elements. -/
def perms_of_list : list α → list (perm α)
| []       := [1]
| (a :: l) := perms_of_list l ++ l.bind (λ b, (perms_of_list l).map (λ f, swap a b * f))

lemma length_perms_of_list : ∀ l : list α, length (perms_of_list l) = l.length!
| []       := rfl
| (a :: l) :=
begin
  rw [length_cons, nat.factorial_succ],
  simp [perms_of_list, length_bind, length_perms_of_list, function.comp, nat.succ_mul],
  cc
end

lemma mem_perms_of_list_of_mem {l : list α} {f : perm α} (h : ∀ x, f x ≠ x → x ∈ l) :
  f ∈ perms_of_list l :=
begin
  induction l with a l IH generalizing f h,
  { exact list.mem_singleton.2 (equiv.ext $ λ x, decidable.by_contradiction $ h _) },
  by_cases hfa : f a = a,
  { refine mem_append_left _ (IH (λ x hx, mem_of_ne_of_mem _ (h x hx))),
    rintro rfl, exact hx hfa },
  have hfa' : f (f a) ≠ f a := mt (λ h, f.injective h) hfa,
  have : ∀ (x : α), (swap a (f a) * f) x ≠ x → x ∈ l,
  { intros x hx,
    have hxa : x ≠ a,
    { rintro rfl, apply hx, simp only [mul_apply, swap_apply_right] },
    refine list.mem_of_ne_of_mem hxa (h x (λ h, _)),
    simp only [h, mul_apply, swap_apply_def, mul_apply, ne.def, apply_eq_iff_eq] at hx;
    split_ifs at hx, exacts [hxa (h.symm.trans h_1), hx h] },
  suffices : f ∈ perms_of_list l ∨ ∃ (b ∈ l) (g ∈ perms_of_list l), swap a b * g = f,
  { simpa only [perms_of_list, exists_prop, list.mem_map, mem_append, list.mem_bind] },
  refine or_iff_not_imp_left.2 (λ hfl, ⟨f a, _, swap a (f a) * f, IH this, _⟩),
  { exact mem_of_ne_of_mem hfa (h _ hfa') },
  { rw [←mul_assoc, mul_def (swap a (f a)) (swap a (f a)),
        swap_swap, ←perm.one_def, one_mul] }
end

lemma mem_of_mem_perms_of_list :
  ∀ {l : list α} {f : perm α}, f ∈ perms_of_list l → ∀ {x}, f x ≠ x → x ∈ l
| []       f h := have f = 1 := by simpa [perms_of_list] using h, by rw this; simp
| (a :: l) f h :=
(mem_append.1 h).elim
  (λ h x hx, mem_cons_of_mem _ (mem_of_mem_perms_of_list h hx))
  (λ h x hx,
    let ⟨y, hy, hy'⟩ := list.mem_bind.1 h in
    let ⟨g, hg₁, hg₂⟩ := list.mem_map.1 hy' in
    if hxa : x = a then by simp [hxa]
    else if hxy : x = y then mem_cons_of_mem _ $ by rwa hxy
    else mem_cons_of_mem _ $
    mem_of_mem_perms_of_list hg₁ $
      by rw [eq_inv_mul_iff_mul_eq.2 hg₂, mul_apply, swap_inv, swap_apply_def];
        split_ifs; cc)

lemma mem_perms_of_list_iff {l : list α} {f : perm α} :
  f ∈ perms_of_list l ↔ ∀ {x}, f x ≠ x → x ∈ l :=
⟨mem_of_mem_perms_of_list, mem_perms_of_list_of_mem⟩

lemma nodup_perms_of_list : ∀ {l : list α} (hl : l.nodup), (perms_of_list l).nodup
| []       hl := by simp [perms_of_list]
| (a :: l) hl :=
have hl' : l.nodup, from nodup_of_nodup_cons hl,
have hln' : (perms_of_list l).nodup, from nodup_perms_of_list hl',
have hmeml : ∀ {f : perm α}, f ∈ perms_of_list l → f a = a,
  from λ f hf, not_not.1 (mt (mem_of_mem_perms_of_list hf) (nodup_cons.1 hl).1),
by rw [perms_of_list, list.nodup_append, list.nodup_bind, pairwise_iff_nth_le]; exact
⟨hln', ⟨λ _ _, nodup_map (λ _ _, mul_left_cancel) hln',
  λ i j hj hij x hx₁ hx₂,
    let ⟨f, hf⟩ := list.mem_map.1 hx₁ in
    let ⟨g, hg⟩ := list.mem_map.1 hx₂ in
    have hix : x a = nth_le l i (lt_trans hij hj),
      by rw [←hf.2, mul_apply, hmeml hf.1, swap_apply_left],
    have hiy : x a = nth_le l j hj,
      by rw [← hg.2, mul_apply, hmeml hg.1, swap_apply_left],
    absurd (hf.2.trans (hg.2.symm)) $
      λ h, ne_of_lt hij $ nodup_iff_nth_le_inj.1 hl' i j (lt_trans hij hj) hj $
        by rw [← hix, hiy]⟩,
  λ f hf₁ hf₂,
    let ⟨x, hx, hx'⟩ := list.mem_bind.1 hf₂ in
    let ⟨g, hg⟩ := list.mem_map.1 hx' in
    have hgxa : g⁻¹ x = a, from f.injective $
      by rw [hmeml hf₁, ← hg.2]; simp,
    have hxa : x ≠ a, from λ h, (list.nodup_cons.1 hl).1 (h ▸ hx),
    (list.nodup_cons.1 hl).1 $
      hgxa ▸ mem_of_mem_perms_of_list hg.1 (by rwa [apply_inv_self, hgxa])⟩

/-- Given a finset, produce the finset of all permutations of its elements. -/
def perms_of_finset (s : finset α) : finset (perm α) :=
quotient.hrec_on s.1 (λ l hl, ⟨perms_of_list l, nodup_perms_of_list hl⟩)
  (λ a b hab, hfunext (congr_arg _ (quotient.sound hab))
    (λ ha hb _, heq_of_eq $ finset.ext $
      by simp [mem_perms_of_list_iff, hab.mem_iff]))
  s.2

lemma mem_perms_of_finset_iff : ∀ {s : finset α} {f : perm α},
  f ∈ perms_of_finset s ↔ ∀ {x}, f x ≠ x → x ∈ s :=
by rintros ⟨⟨l⟩, hs⟩ f; exact mem_perms_of_list_iff

lemma card_perms_of_finset : ∀ (s : finset α),
  (perms_of_finset s).card = s.card! :=
by rintros ⟨⟨l⟩, hs⟩; exact length_perms_of_list l

/-- The collection of permutations of a fintype is a fintype. -/
def fintype_perm [fintype α] : fintype (perm α) :=
⟨perms_of_finset (@finset.univ α _), by simp [mem_perms_of_finset_iff]⟩

instance [fintype α] [fintype β] : fintype (α ≃ β) :=
if h : fintype.card β = fintype.card α
then trunc.rec_on_subsingleton (fintype.trunc_equiv_fin α)
  (λ eα, trunc.rec_on_subsingleton (fintype.trunc_equiv_fin β)
    (λ eβ, @fintype.of_equiv _ (perm α) fintype_perm
      (equiv_congr (equiv.refl α) (eα.trans (eq.rec_on h eβ.symm)) : (α ≃ α) ≃ (α ≃ β))))
else ⟨∅, λ x, false.elim (h (fintype.card_eq.2 ⟨x.symm⟩))⟩

lemma fintype.card_perm [fintype α] : fintype.card (perm α) = (fintype.card α)! :=
subsingleton.elim (@fintype_perm α _ _) (@equiv.fintype α α _ _ _ _) ▸
card_perms_of_finset _

lemma fintype.card_equiv [fintype α] [fintype β] (e : α ≃ β) :
  fintype.card (α ≃ β) = (fintype.card α)! :=
fintype.card_congr (equiv_congr (equiv.refl α) e) ▸ fintype.card_perm

lemma univ_eq_singleton_of_card_one {α} [fintype α] (x : α) (h : fintype.card α = 1) :
  (univ : finset α) = {x} :=
begin
  symmetry,
  apply eq_of_subset_of_card_le (subset_univ ({x})),
  apply le_of_eq,
  simp [h, finset.card_univ]
end

end equiv

namespace fintype

section choose
open fintype equiv

variables [fintype α] (p : α → Prop) [decidable_pred p]

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of the corresponding subtype. -/
def choose_x (hp : ∃! a : α, p a) : {a // p a} :=
⟨finset.choose p univ (by simp; exact hp), finset.choose_property _ _ _⟩

/-- Given a fintype `α` and a predicate `p`, associate to a proof that there is a unique element of
`α` satisfying `p` this unique element, as an element of `α`. -/
def choose (hp : ∃! a, p a) : α := choose_x p hp

lemma choose_spec (hp : ∃! a, p a) : p (choose p hp) :=
(choose_x p hp).property

@[simp] lemma choose_subtype_eq {α : Type*} (p : α → Prop) [fintype {a : α // p a}]
  [decidable_eq α] (x : {a : α // p a})
  (h : ∃! (a : {a // p a}), (a : α) = x := ⟨x, rfl, λ y hy, by simpa [subtype.ext_iff] using hy⟩) :
  fintype.choose (λ (y : {a : α // p a}), (y : α) = x) h = x :=
by rw [subtype.ext_iff, fintype.choose_spec (λ (y : {a : α // p a}), (y : α) = x) _]

end choose

section bijection_inverse
open function

variables [fintype α] [decidable_eq β] {f : α → β}

/--
`bij_inv f` is the unique inverse to a bijection `f`. This acts
  as a computable alternative to `function.inv_fun`. -/
def bij_inv (f_bij : bijective f) (b : β) : α :=
fintype.choose (λ a, f a = b)
begin
  rcases f_bij.right b with ⟨a', fa_eq_b⟩,
  rw ← fa_eq_b,
  exact ⟨a', ⟨rfl, (λ a h, f_bij.left h)⟩⟩
end

lemma left_inverse_bij_inv (f_bij : bijective f) : left_inverse (bij_inv f_bij) f :=
λ a, f_bij.left (choose_spec (λ a', f a' = f a) _)

lemma right_inverse_bij_inv (f_bij : bijective f) : right_inverse (bij_inv f_bij) f :=
λ b, choose_spec (λ a', f a' = b) _

lemma bijective_bij_inv (f_bij : bijective f) : bijective (bij_inv f_bij) :=
⟨(right_inverse_bij_inv _).injective, (left_inverse_bij_inv _).surjective⟩

end bijection_inverse

lemma well_founded_of_trans_of_irrefl [fintype α] (r : α → α → Prop)
  [is_trans α r] [is_irrefl α r] : well_founded r :=
by classical; exact
have ∀ x y, r x y → (univ.filter (λ z, r z x)).card < (univ.filter (λ z, r z y)).card,
  from λ x y hxy, finset.card_lt_card $
    by simp only [finset.lt_iff_ssubset.symm, lt_iff_le_not_le,
      finset.le_iff_subset, finset.subset_iff, mem_filter, true_and, mem_univ, hxy];
    exact ⟨λ z hzx, trans hzx hxy, not_forall_of_exists_not ⟨x, not_imp.2 ⟨hxy, irrefl x⟩⟩⟩,
subrelation.wf this (measure_wf _)

lemma preorder.well_founded [fintype α] [preorder α] : well_founded ((<) : α → α → Prop) :=
well_founded_of_trans_of_irrefl _

@[instance, priority 10] lemma linear_order.is_well_order [fintype α] [linear_order α] :
  is_well_order α (<) :=
{ wf := preorder.well_founded }

end fintype

/-- A type is said to be infinite if it has no fintype instance.
  Note that `infinite α` is equivalent to `is_empty (fintype α)`. -/
class infinite (α : Type*) : Prop :=
(not_fintype : fintype α → false)

lemma not_fintype (α : Type*) [h1 : infinite α] [h2 : fintype α] : false :=
infinite.not_fintype h2

protected lemma fintype.false {α : Type*} [infinite α] (h : fintype α) : false :=
not_fintype α

protected lemma infinite.false {α : Type*} [fintype α] (h : infinite α) : false :=
not_fintype α

@[simp] lemma is_empty_fintype {α : Type*} : is_empty (fintype α) ↔ infinite α :=
⟨λ ⟨x⟩, ⟨x⟩, λ ⟨x⟩, ⟨x⟩⟩

/-- A non-infinite type is a fintype. -/
noncomputable def fintype_of_not_infinite {α : Type*} (h : ¬ infinite α) : fintype α :=
nonempty.some $ by rwa [← not_is_empty_iff, is_empty_fintype]

section
open_locale classical

/--
Any type is (classically) either a `fintype`, or `infinite`.

One can obtain the relevant typeclasses via `cases fintype_or_infinite α; resetI`.
-/
noncomputable def fintype_or_infinite (α : Type*) : psum (fintype α) (infinite α) :=
if h : infinite α then psum.inr h else psum.inl (fintype_of_not_infinite h)

end

lemma finset.exists_minimal {α : Type*} [preorder α] (s : finset α) (h : s.nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬ (x < m) :=
begin
  obtain ⟨c, hcs : c ∈ s⟩ := h,
  have : well_founded (@has_lt.lt {x // x ∈ s} _) := fintype.well_founded_of_trans_of_irrefl _,
  obtain ⟨⟨m, hms : m ∈ s⟩, -, H⟩ := this.has_min set.univ ⟨⟨c, hcs⟩, trivial⟩,
  exact ⟨m, hms, λ x hx hxm, H ⟨x, hx⟩ trivial hxm⟩,
end

lemma finset.exists_maximal {α : Type*} [preorder α] (s : finset α) (h : s.nonempty) :
  ∃ m ∈ s, ∀ x ∈ s, ¬ (m < x) :=
@finset.exists_minimal (order_dual α) _ s h

namespace infinite

lemma exists_not_mem_finset [infinite α] (s : finset α) : ∃ x, x ∉ s :=
not_forall.1 $ λ h, fintype.false ⟨s, h⟩

@[priority 100] -- see Note [lower instance priority]
instance (α : Type*) [H : infinite α] : nontrivial α :=
⟨let ⟨x, hx⟩ := exists_not_mem_finset (∅ : finset α) in
let ⟨y, hy⟩ := exists_not_mem_finset ({x} : finset α) in
⟨y, x, by simpa only [mem_singleton] using hy⟩⟩

protected lemma nonempty (α : Type*) [infinite α] : nonempty α :=
by apply_instance

lemma of_injective [infinite β] (f : β → α) (hf : injective f) : infinite α :=
⟨λ I, by exactI (fintype.of_injective f hf).false⟩

lemma of_surjective [infinite β] (f : α → β) (hf : surjective f) : infinite α :=
⟨λ I, by { classical, exactI (fintype.of_surjective f hf).false }⟩

end infinite

instance : infinite ℕ :=
⟨λ ⟨s, hs⟩, finset.not_mem_range_self $ s.subset_range_sup_succ (hs _)⟩

instance : infinite ℤ :=
infinite.of_injective int.of_nat (λ _ _, int.of_nat.inj)

instance infinite.set [infinite α] : infinite (set α) :=
infinite.of_injective singleton (λ a b, set.singleton_eq_singleton_iff.1)

instance [infinite α] : infinite (finset α) :=
infinite.of_injective singleton finset.singleton_injective

instance [nonempty α] : infinite (multiset α) :=
begin
  inhabit α,
  exact infinite.of_injective (multiset.repeat default) (multiset.repeat_injective _),
end

instance [nonempty α] : infinite (list α) :=
infinite.of_surjective (coe : list α → multiset α) (surjective_quot_mk _)

instance [infinite α] : infinite (option α) :=
infinite.of_injective some (option.some_injective α)

instance sum.infinite_of_left [infinite α] : infinite (α ⊕ β) :=
infinite.of_injective sum.inl sum.inl_injective

instance sum.infinite_of_right [infinite β] : infinite (α ⊕ β) :=
infinite.of_injective sum.inr sum.inr_injective

@[simp] lemma infinite_sum : infinite (α ⊕ β) ↔ infinite α ∨ infinite β :=
begin
  refine ⟨λ H, _, λ H, H.elim (@sum.infinite_of_left α β) (@sum.infinite_of_right α β)⟩,
  contrapose! H, haveI := fintype_of_not_infinite H.1, haveI := fintype_of_not_infinite H.2,
  exact infinite.false
end

instance prod.infinite_of_right [nonempty α] [infinite β] : infinite (α × β) :=
infinite.of_surjective prod.snd prod.snd_surjective

instance prod.infinite_of_left [infinite α] [nonempty β] : infinite (α × β) :=
infinite.of_surjective prod.fst prod.fst_surjective

@[simp] lemma infinite_prod :
  infinite (α × β) ↔ infinite α ∧ nonempty β ∨ nonempty α ∧ infinite β :=
begin
  refine ⟨λ H, _, λ H, H.elim (and_imp.2 $ @prod.infinite_of_left α β)
    (and_imp.2 $ @prod.infinite_of_right α β)⟩,
  rw and.comm, contrapose! H, introI H',
  rcases infinite.nonempty (α × β) with ⟨a, b⟩,
  haveI := fintype_of_not_infinite (H.1 ⟨b⟩), haveI := fintype_of_not_infinite (H.2 ⟨a⟩),
  exact H'.false
end

namespace infinite

private noncomputable def nat_embedding_aux (α : Type*) [infinite α] : ℕ → α
| n := by letI := classical.dec_eq α; exact classical.some (exists_not_mem_finset
  ((multiset.range n).pmap (λ m (hm : m < n), nat_embedding_aux m)
    (λ _, multiset.mem_range.1)).to_finset)

private lemma nat_embedding_aux_injective (α : Type*) [infinite α] :
  function.injective (nat_embedding_aux α) :=
begin
  rintro m n h,
  letI := classical.dec_eq α,
  wlog hmlen : m ≤ n using m n,
  by_contradiction hmn,
  have hmn : m < n, from lt_of_le_of_ne hmlen hmn,
  refine (classical.some_spec (exists_not_mem_finset
    ((multiset.range n).pmap (λ m (hm : m < n), nat_embedding_aux α m)
      (λ _, multiset.mem_range.1)).to_finset)) _,
  refine multiset.mem_to_finset.2 (multiset.mem_pmap.2
    ⟨m, multiset.mem_range.2 hmn, _⟩),
  rw [h, nat_embedding_aux]
end

/-- Embedding of `ℕ` into an infinite type. -/
noncomputable def nat_embedding (α : Type*) [infinite α] : ℕ ↪ α :=
⟨_, nat_embedding_aux_injective α⟩

lemma exists_subset_card_eq (α : Type*) [infinite α] (n : ℕ) :
  ∃ s : finset α, s.card = n :=
⟨(range n).map (nat_embedding α), by rw [card_map, card_range]⟩

end infinite

/-- If every finset in a type has bounded cardinality, that type is finite. -/
noncomputable def fintype_of_finset_card_le {ι : Type*} (n : ℕ)
  (w : ∀ s : finset ι, s.card ≤ n) : fintype ι :=
begin
  apply fintype_of_not_infinite,
  introI i,
  obtain ⟨s, c⟩ := infinite.exists_subset_card_eq ι (n+1),
  specialize w s,
  rw c at w,
  exact nat.not_succ_le_self n w,
end

lemma not_injective_infinite_fintype [infinite α] [fintype β] (f : α → β) :
  ¬ injective f :=
λ hf, (fintype.of_injective f hf).false

/--
The pigeonhole principle for infinitely many pigeons in finitely many pigeonholes. If there are
infinitely many pigeons in finitely many pigeonholes, then there are at least two pigeons in the
same pigeonhole.

See also: `fintype.exists_ne_map_eq_of_card_lt`, `fintype.exists_infinite_fiber`.
-/
lemma fintype.exists_ne_map_eq_of_infinite [infinite α] [fintype β] (f : α → β) :
  ∃ x y : α, x ≠ y ∧ f x = f y :=
begin
  classical, by_contra' hf,
  apply not_injective_infinite_fintype f,
  intros x y, contrapose, apply hf,
end

-- irreducible due to this conversation on Zulip:
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/
-- topic/.60simp.60.20ignoring.20lemmas.3F/near/241824115

@[irreducible]
instance function.embedding.is_empty {α β} [infinite α] [fintype β] : is_empty (α ↪ β) :=
  ⟨λ f, let ⟨x, y, ne, feq⟩ := fintype.exists_ne_map_eq_of_infinite f in ne $ f.injective feq⟩

@[priority 100]
noncomputable instance function.embedding.fintype' {α β : Type*} [fintype β] : fintype (α ↪ β) :=
begin
  by_cases h : infinite α,
  { resetI, apply_instance },
  { have := fintype_of_not_infinite h, classical, apply_instance }
  -- the `classical` generates `decidable_eq α/β` instances, and resets instance cache
end

/--
The strong pigeonhole principle for infinitely many pigeons in
finitely many pigeonholes.  If there are infinitely many pigeons in
finitely many pigeonholes, then there is a pigeonhole with infinitely
many pigeons.

See also: `fintype.exists_ne_map_eq_of_infinite`
-/
lemma fintype.exists_infinite_fiber [infinite α] [fintype β] (f : α → β) :
  ∃ y : β, infinite (f ⁻¹' {y}) :=
begin
  classical,
  by_contra' hf,

  haveI := λ y, fintype_of_not_infinite $ hf y,
  let key : fintype α :=
  { elems := univ.bUnion (λ (y : β), (f ⁻¹' {y}).to_finset),
    complete := by simp },
  exact key.false,
end

lemma not_surjective_fintype_infinite [fintype α] [infinite β] (f : α → β) :
  ¬ surjective f :=
assume (hf : surjective f),
have H : infinite α := infinite.of_surjective f hf,
by exactI not_fintype α

section trunc

/--
For `s : multiset α`, we can lift the existential statement that `∃ x, x ∈ s` to a `trunc α`.
-/
def trunc_of_multiset_exists_mem {α} (s : multiset α) : (∃ x, x ∈ s) → trunc α :=
quotient.rec_on_subsingleton s $ λ l h,
  match l, h with
    | [],       _ := false.elim (by tauto)
    | (a :: _), _ := trunc.mk a
  end

/--
A `nonempty` `fintype` constructively contains an element.
-/
def trunc_of_nonempty_fintype (α) [nonempty α] [fintype α] : trunc α :=
trunc_of_multiset_exists_mem finset.univ.val (by simp)

/--
A `fintype` with positive cardinality constructively contains an element.
-/
def trunc_of_card_pos {α} [fintype α] (h : 0 < fintype.card α) : trunc α :=
by { letI := (fintype.card_pos_iff.mp h), exact trunc_of_nonempty_fintype α }

/--
By iterating over the elements of a fintype, we can lift an existential statement `∃ a, P a`
to `trunc (Σ' a, P a)`, containing data.
-/
def trunc_sigma_of_exists {α} [fintype α] {P : α → Prop} [decidable_pred P] (h : ∃ a, P a) :
  trunc (Σ' a, P a) :=
@trunc_of_nonempty_fintype (Σ' a, P a) (exists.elim h $ λ a ha, ⟨⟨a, ha⟩⟩) _

end trunc

namespace multiset

variables [fintype α] [decidable_eq α]

@[simp] lemma count_univ (a : α) :
  count a finset.univ.val = 1 :=
count_eq_one_of_mem finset.univ.nodup (finset.mem_univ _)

end multiset

namespace fintype

/-- A recursor principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
def trunc_rec_empty_option {P : Type u → Sort v}
  (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
  (h_empty : P pempty)
  (h_option : ∀ {α} [fintype α] [decidable_eq α], P α → P (option α))
  (α : Type u) [fintype α] [decidable_eq α] : trunc (P α) :=
begin
  suffices : ∀ n : ℕ, trunc (P (ulift $ fin n)),
  { apply trunc.bind (this (fintype.card α)),
    intro h,
    apply trunc.map _ (fintype.trunc_equiv_fin α),
    intro e,
    exact of_equiv (equiv.ulift.trans e.symm) h },
  intro n,
  induction n with n ih,
  { have : card pempty = card (ulift (fin 0)),
    { simp only [card_fin, card_pempty, card_ulift] },
    apply trunc.bind (trunc_equiv_of_card_eq this),
    intro e,
    apply trunc.mk,
    refine of_equiv e h_empty, },
  { have : card (option (ulift (fin n))) = card (ulift (fin n.succ)),
    { simp only [card_fin, card_option, card_ulift] },
    apply trunc.bind (trunc_equiv_of_card_eq this),
    intro e,
    apply trunc.map _ ih,
    intro ih,
    refine of_equiv e (h_option ih), },
end

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
@[elab_as_eliminator]
lemma induction_empty_option' {P : Π (α : Type u) [fintype α], Prop}
  (of_equiv : ∀ α β [fintype β] (e : α ≃ β), @P α (@fintype.of_equiv α β ‹_› e.symm) → @P β ‹_›)
  (h_empty : P pempty)
  (h_option : ∀ α [fintype α], by exactI P α → P (option α))
  (α : Type u) [fintype α] : P α :=
begin
  obtain ⟨p⟩ := @trunc_rec_empty_option (λ α, ∀ h, @P α h)
    (λ α β e hα hβ, @of_equiv α β hβ e (hα _)) (λ _i, by convert h_empty)
    _ α _ (classical.dec_eq α),
  { exact p _ },
  { rintro α hα - Pα hα', resetI, convert h_option α (Pα _) }
end

/-- An induction principle for finite types, analogous to `nat.rec`. It effectively says
that every `fintype` is either `empty` or `option α`, up to an `equiv`. -/
lemma induction_empty_option {P : Type u → Prop}
  (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
  (h_empty : P pempty)
  (h_option : ∀ {α} [fintype α], P α → P (option α))
  (α : Type u) [fintype α] : P α :=
begin
  refine induction_empty_option' _ _ _ α,
  exacts [λ α β _, of_equiv, h_empty, @h_option]
end

end fintype

/-- Auxiliary definition to show `exists_seq_of_forall_finset_exists`. -/
noncomputable def seq_of_forall_finset_exists_aux
  {α : Type*} [decidable_eq α] (P : α → Prop) (r : α → α → Prop)
  (h : ∀ (s : finset α), ∃ y, (∀ x ∈ s, P x) → (P y ∧ (∀ x ∈ s, r x y))) : ℕ → α
| n := classical.some (h (finset.image (λ (i : fin n), seq_of_forall_finset_exists_aux i)
        (finset.univ : finset (fin n))))
using_well_founded {dec_tac := `[exact i.2]}

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m < n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
lemma exists_seq_of_forall_finset_exists {α : Type*} (P : α → Prop) (r : α → α → Prop)
  (h : ∀ (s : finset α), (∀ x ∈ s, P x) → ∃ y, P y ∧ (∀ x ∈ s, r x y)) :
  ∃ (f : ℕ → α), (∀ n, P (f n)) ∧ (∀ m n, m < n → r (f m) (f n)) :=
begin
  classical,
  haveI : nonempty α,
  { rcases h ∅ (by simp) with ⟨y, hy⟩,
    exact ⟨y⟩ },
  choose! F hF using h,
  have h' : ∀ (s : finset α), ∃ y, (∀ x ∈ s, P x) → (P y ∧ (∀ x ∈ s, r x y)) := λ s, ⟨F s, hF s⟩,
  set f := seq_of_forall_finset_exists_aux P r h' with hf,
  have A : ∀ (n : ℕ), P (f n),
  { assume n,
    induction n using nat.strong_induction_on with n IH,
    have IH' : ∀ (x : fin n), P (f x) := λ n, IH n.1 n.2,
    rw [hf, seq_of_forall_finset_exists_aux],
    exact (classical.some_spec (h' (finset.image (λ (i : fin n), f i)
      (finset.univ : finset (fin n)))) (by simp [IH'])).1 },
  refine ⟨f, A, λ m n hmn, _⟩,
  nth_rewrite 1 hf,
  rw seq_of_forall_finset_exists_aux,
  apply (classical.some_spec (h' (finset.image (λ (i : fin n), f i)
    (finset.univ : finset (fin n)))) (by simp [A])).2,
  exact finset.mem_image.2 ⟨⟨m, hmn⟩, finset.mem_univ _, rfl⟩,
end

/-- Induction principle to build a sequence, by adding one point at a time satisfying a given
symmetric relation with respect to all the previously chosen points.

More precisely, Assume that, for any finite set `s`, one can find another point satisfying
some relation `r` with respect to all the points in `s`. Then one may construct a
function `f : ℕ → α` such that `r (f m) (f n)` holds whenever `m ≠ n`.
We also ensure that all constructed points satisfy a given predicate `P`. -/
lemma exists_seq_of_forall_finset_exists' {α : Type*} (P : α → Prop) (r : α → α → Prop)
  [is_symm α r]
  (h : ∀ (s : finset α), (∀ x ∈ s, P x) → ∃ y, P y ∧ (∀ x ∈ s, r x y)) :
  ∃ (f : ℕ → α), (∀ n, P (f n)) ∧ (∀ m n, m ≠ n → r (f m) (f n)) :=
begin
  rcases exists_seq_of_forall_finset_exists P r h with ⟨f, hf, hf'⟩,
  refine ⟨f, hf, λ m n hmn, _⟩,
  rcases lt_trichotomy m n with h|rfl|h,
  { exact hf' m n h },
  { exact (hmn rfl).elim },
  { apply symm,
    exact hf' n m h }
end

/-- A custom induction principle for fintypes. The base case is a subsingleton type,
and the induction step is for non-trivial types, and one can assume the hypothesis for
smaller types (via `fintype.card`).

The major premise is `fintype α`, so to use this with the `induction` tactic you have to give a name
to that instance and use that name.
-/
@[elab_as_eliminator]
lemma fintype.induction_subsingleton_or_nontrivial
  {P : Π α [fintype α], Prop} (α : Type*) [fintype α]
  (hbase : ∀ α [fintype α] [subsingleton α], by exactI P α)
  (hstep : ∀ α [fintype α] [nontrivial α],
    by exactI ∀ (ih : ∀ β [fintype β], by exactI ∀ (h : fintype.card β < fintype.card α), P β),
    P α) :
  P α :=
begin
  obtain ⟨ n, hn ⟩ : ∃ n, fintype.card α = n := ⟨fintype.card α, rfl⟩,
  unfreezingI { induction n using nat.strong_induction_on with n ih generalizing α },
  casesI (subsingleton_or_nontrivial α) with hsing hnontriv,
  { apply hbase, },
  { apply hstep,
    introsI β _ hlt,
    rw hn at hlt,
    exact (ih (fintype.card β) hlt _ rfl), }
end
