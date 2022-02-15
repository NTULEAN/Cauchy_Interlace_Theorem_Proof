/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.pairwise

/-!
# Antichains

This file defines antichains. An antichain is a set where any two distinct elements are not related.
If the relation is `(≤)`, this corresponds to incomparability and usual order antichains. If the
relation is `G.adj` for `G : simple_graph α`, this corresponds to independent sets of `G`.

## Definitions

* `is_antichain r s`: Any two elements of `s : set α` are unrelated by `r : α → α → Prop`.
* `is_strong_antichain r s`: Any two elements of `s : set α` are not related by `r : α → α → Prop`
  to a common element.
* `is_antichain.mk r s`: Turns `s` into an antichain by keeping only the "maximal" elements.
-/

open function set

variables {α β : Type*} {r r₁ r₂ : α → α → Prop} {r' : β → β → Prop} {s t : set α} {a : α}

protected lemma symmetric.compl (h : symmetric r) : symmetric rᶜ := λ x y hr hr', hr $ h hr'

/-- An antichain is a set such that no two distinct elements are related. -/
def is_antichain (r : α → α → Prop) (s : set α) : Prop := s.pairwise rᶜ

namespace is_antichain

protected lemma subset (hs : is_antichain r s) (h : t ⊆ s) : is_antichain r t := hs.mono h

lemma mono (hs : is_antichain r₁ s) (h : r₂ ≤ r₁) : is_antichain r₂ s := hs.mono' $ compl_le_compl h

lemma mono_on (hs : is_antichain r₁ s) (h : s.pairwise (λ ⦃a b⦄, r₂ a b → r₁ a b)) :
  is_antichain r₂ s :=
hs.imp_on $ h.imp $ λ a b h h₁ h₂, h₁ $ h h₂

protected lemma eq (hs : is_antichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r a b) :
  a = b :=
hs.eq ha hb $ not_not_intro h

protected lemma eq' (hs : is_antichain r s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : r b a) :
  a = b :=
(hs.eq hb ha h).symm

protected lemma is_antisymm (h : is_antichain r univ) : is_antisymm α r :=
⟨λ a b ha _, h.eq trivial trivial ha⟩

protected lemma subsingleton [is_trichotomous α r] (h : is_antichain r s) : s.subsingleton :=
begin
  rintro a ha b hb,
  obtain hab | hab | hab := trichotomous_of r a b,
  { exact h.eq ha hb hab },
  { exact hab },
  { exact h.eq' ha hb hab }
end

protected lemma flip (hs : is_antichain r s) : is_antichain (flip r) s :=
λ a ha b hb h, hs hb ha h.symm

lemma swap (hs : is_antichain r s) : is_antichain (swap r) s := hs.flip

lemma image (hs : is_antichain r s) (f : α → β) (h : ∀ ⦃a b⦄, r' (f a) (f b) → r a b) :
  is_antichain r' (f '' s) :=
begin
  rintro _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ hbc hr,
  exact hs hb hc (ne_of_apply_ne _ hbc) (h hr),
end

lemma preimage (hs : is_antichain r s) {f : β → α} (hf : injective f)
  (h : ∀ ⦃a b⦄, r' a b → r (f a) (f b)) :
  is_antichain r' (f ⁻¹' s) :=
λ b hb c hc hbc hr, hs hb hc (hf.ne hbc) $ h hr

lemma _root_.is_antichain_insert :
  is_antichain r (insert a s) ↔ is_antichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b ∧ ¬ r b a :=
set.pairwise_insert

protected lemma insert (hs : is_antichain r s) (hl : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r b a)
  (hr : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b) :
  is_antichain r (insert a s) :=
is_antichain_insert.2 ⟨hs, λ b hb hab, ⟨hr hb hab, hl hb hab⟩⟩

lemma _root_.is_antichain_insert_of_symmetric (hr : symmetric r) :
  is_antichain r (insert a s) ↔ is_antichain r s ∧ ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b :=
pairwise_insert_of_symmetric hr.compl

lemma insert_of_symmetric (hs : is_antichain r s) (hr : symmetric r)
  (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ¬ r a b) :
  is_antichain r (insert a s) :=
(is_antichain_insert_of_symmetric hr).2 ⟨hs, h⟩

end is_antichain

lemma is_antichain_singleton (a : α) (r : α → α → Prop) : is_antichain r {a} :=
pairwise_singleton _ _

lemma set.subsingleton.is_antichain (hs : s.subsingleton) (r : α → α → Prop) : is_antichain r s :=
hs.pairwise _

section preorder
variables [preorder α]

lemma is_antichain_and_least_iff : is_antichain (≤) s ∧ is_least s a ↔ s = {a} :=
⟨λ h, eq_singleton_iff_unique_mem.2 ⟨h.2.1, λ b hb, h.1.eq' hb h.2.1 (h.2.2 hb)⟩,
  by { rintro rfl, exact ⟨is_antichain_singleton _ _, is_least_singleton⟩ }⟩

lemma is_antichain_and_greatest_iff : is_antichain (≤) s ∧ is_greatest s a ↔ s = {a} :=
⟨λ h, eq_singleton_iff_unique_mem.2 ⟨h.2.1, λ b hb, h.1.eq hb h.2.1 (h.2.2 hb)⟩,
  by { rintro rfl, exact ⟨is_antichain_singleton _ _, is_greatest_singleton⟩ }⟩

lemma is_antichain.least_iff (hs : is_antichain (≤) s) : is_least s a ↔ s = {a} :=
(and_iff_right hs).symm.trans is_antichain_and_least_iff

lemma is_antichain.greatest_iff (hs : is_antichain (≤) s) : is_greatest s a ↔ s = {a} :=
(and_iff_right hs).symm.trans is_antichain_and_greatest_iff

lemma is_least.antichain_iff (hs : is_least s a) : is_antichain (≤) s ↔ s = {a} :=
(and_iff_left hs).symm.trans is_antichain_and_least_iff

lemma is_greatest.antichain_iff (hs : is_greatest s a) : is_antichain (≤) s ↔ s = {a} :=
(and_iff_left hs).symm.trans is_antichain_and_greatest_iff

lemma is_antichain.bot_mem_iff [order_bot α] (hs : is_antichain (≤) s) : ⊥ ∈ s ↔ s = {⊥} :=
is_least_bot_iff.symm.trans hs.least_iff

lemma is_antichain.top_mem_iff [order_top α] (hs : is_antichain (≤) s) : ⊤ ∈ s ↔ s = {⊤} :=
is_greatest_top_iff.symm.trans hs.greatest_iff

end preorder

/-! ### Strong antichains -/

/-- An strong (upward) antichain is a set such that no two distinct elements are related to a common
element. -/
def is_strong_antichain (r : α → α → Prop) (s : set α) : Prop :=
s.pairwise $ λ a b, ∀ c, ¬ r a c ∨ ¬ r b c

namespace is_strong_antichain

protected lemma subset (hs : is_strong_antichain r s) (h : t ⊆ s) : is_strong_antichain r t :=
hs.mono h

lemma mono (hs : is_strong_antichain r₁ s) (h : r₂ ≤ r₁) : is_strong_antichain r₂ s :=
hs.mono' $ λ a b hab c, (hab c).imp (compl_le_compl h _ _) (compl_le_compl h _ _)

lemma eq (hs : is_strong_antichain r s) {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hac : r a c)
  (hbc : r b c) :
  a = b :=
hs.eq ha hb $ λ h, false.elim $ (h c).elim (not_not_intro hac) (not_not_intro hbc)

protected lemma is_antichain [is_refl α r] (h : is_strong_antichain r s) : is_antichain r s :=
h.imp $ λ a b hab, (hab b).resolve_right (not_not_intro $ refl _)

protected lemma subsingleton [is_directed α r] (h : is_strong_antichain r s) : s.subsingleton :=
λ a ha b hb, let ⟨c, hac, hbc⟩ := directed_of r a b in h.eq ha hb hac hbc

protected lemma flip [is_symm α r] (hs : is_strong_antichain r s) :
  is_strong_antichain (flip r) s :=
λ a ha b hb h c, (hs ha hb h c).imp (mt $ symm_of r) (mt $ symm_of r)

lemma swap [is_symm α r] (hs : is_strong_antichain r s) : is_strong_antichain (swap r) s := hs.flip

lemma image (hs : is_strong_antichain r s) {f : α → β} (hf : surjective f)
  (h : ∀ a b, r' (f a) (f b) → r a b) :
  is_strong_antichain r' (f '' s) :=
begin
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab c,
  obtain ⟨c, rfl⟩ := hf c,
  exact (hs ha hb (ne_of_apply_ne _ hab) _).imp (mt $ h _ _) (mt $ h _ _),
end

lemma preimage (hs : is_strong_antichain r s) {f : β → α} (hf : injective f)
  (h : ∀ a b, r' a b → r (f a) (f b)) :
  is_strong_antichain r' (f ⁻¹' s) :=
λ a ha b hb hab c, (hs ha hb (hf.ne hab) _).imp (mt $ h _ _) (mt $ h _ _)

lemma _root_.is_strong_antichain_insert :
  is_strong_antichain r (insert a s) ↔ is_strong_antichain r s ∧
    ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬ r a c ∨ ¬ r b c :=
set.pairwise_insert_of_symmetric $ λ a b h c, (h c).symm

protected lemma insert (hs : is_strong_antichain r s)
  (h : ∀ ⦃b⦄, b ∈ s → a ≠ b → ∀ c, ¬ r a c ∨ ¬ r b c) :
  is_strong_antichain r (insert a s) :=
is_strong_antichain_insert.2 ⟨hs, h⟩

end is_strong_antichain

lemma set.subsingleton.is_strong_antichain (hs : s.subsingleton) (r : α → α → Prop) :
  is_strong_antichain r s :=
hs.pairwise _
