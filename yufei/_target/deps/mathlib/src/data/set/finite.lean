/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.finset.sort
import data.set.functor

/-!
# Finite sets

This file defines predicates `finite : set α → Prop` and `infinite : set α → Prop` and proves some
basic facts about finite sets.
-/

open set function

universes u v w x
variables {α : Type u} {β : Type v} {ι : Sort w} {γ : Type x}

namespace set

/-- A set is finite if the subtype is a fintype, i.e. there is a
  list that enumerates its members. -/
inductive finite (s : set α) : Prop
| intro : fintype s → finite

lemma finite_def {s : set α} : finite s ↔ nonempty (fintype s) := ⟨λ ⟨h⟩, ⟨h⟩, λ ⟨h⟩, ⟨h⟩⟩

/-- A set is infinite if it is not finite. -/
def infinite (s : set α) : Prop := ¬ finite s

/-- The subtype corresponding to a finite set is a finite type. Note
that because `finite` isn't a typeclass, this will not fire if it
is made into an instance -/
noncomputable def finite.fintype {s : set α} (h : finite s) : fintype s :=
classical.choice $ finite_def.1 h

/-- Get a finset from a finite set -/
noncomputable def finite.to_finset {s : set α} (h : finite s) : finset α :=
@set.to_finset _ _ h.fintype

@[simp] lemma not_infinite {s : set α} : ¬ s.infinite ↔ s.finite :=
by simp [infinite]

/-- See also `fintype_or_infinite`. -/
lemma finite_or_infinite {s : set α} : s.finite ∨ s.infinite := em _

@[simp] theorem finite.mem_to_finset {s : set α} (h : finite s) {a : α} : a ∈ h.to_finset ↔ a ∈ s :=
@mem_to_finset _ _ h.fintype _

@[simp] theorem finite.to_finset.nonempty {s : set α} (h : finite s) :
  h.to_finset.nonempty ↔ s.nonempty :=
show (∃ x, x ∈ h.to_finset) ↔ (∃ x, x ∈ s),
from exists_congr (λ _, h.mem_to_finset)

@[simp] lemma finite.coe_to_finset {s : set α} (h : finite s) : ↑h.to_finset = s :=
@set.coe_to_finset _ s h.fintype

@[simp] lemma finite.coe_sort_to_finset {s : set α} (h : finite s) :
  (h.to_finset : Type*) = s :=
by rw [← finset.coe_sort_coe _, h.coe_to_finset]

@[simp] lemma finite_empty_to_finset (h : finite (∅ : set α)) : h.to_finset = ∅ :=
by rw [← finset.coe_inj, h.coe_to_finset, finset.coe_empty]

@[simp] lemma finite.to_finset_inj {s t : set α} {hs : finite s} {ht : finite t} :
  hs.to_finset = ht.to_finset ↔ s = t :=
by simp [←finset.coe_inj]

lemma subset_to_finset_iff {s : finset α} {t : set α} (ht : finite t) :
  s ⊆ ht.to_finset ↔ ↑s ⊆ t :=
by rw [← finset.coe_subset, ht.coe_to_finset]

@[simp] lemma finite_to_finset_eq_empty_iff {s : set α} {h : finite s} :
  h.to_finset = ∅ ↔ s = ∅ :=
by simp [←finset.coe_inj]

theorem finite.exists_finset {s : set α} : finite s →
  ∃ s' : finset α, ∀ a : α, a ∈ s' ↔ a ∈ s
| ⟨h⟩ := by exactI ⟨to_finset s, λ _, mem_to_finset⟩

theorem finite.exists_finset_coe {s : set α} (hs : finite s) :
  ∃ s' : finset α, ↑s' = s :=
⟨hs.to_finset, hs.coe_to_finset⟩

/-- Finite sets can be lifted to finsets. -/
instance : can_lift (set α) (finset α) :=
{ coe := coe,
  cond := finite,
  prf := λ s hs, hs.exists_finset_coe }

theorem finite_mem_finset (s : finset α) : finite {a | a ∈ s} :=
⟨fintype.of_finset s (λ _, iff.rfl)⟩

theorem finite.of_fintype [fintype α] (s : set α) : finite s :=
by classical; exact ⟨set_fintype s⟩

theorem exists_finite_iff_finset {p : set α → Prop} :
  (∃ s, finite s ∧ p s) ↔ ∃ s : finset α, p ↑s :=
⟨λ ⟨s, hs, hps⟩, ⟨hs.to_finset, hs.coe_to_finset.symm ▸ hps⟩,
  λ ⟨s, hs⟩, ⟨↑s, finite_mem_finset s, hs⟩⟩

lemma finite.fin_embedding {s : set α} (h : finite s) : ∃ (n : ℕ) (f : fin n ↪ α), range f = s :=
⟨_, (fintype.equiv_fin (h.to_finset : set α)).symm.as_embedding, by simp⟩

lemma finite.fin_param {s : set α} (h : finite s) :
  ∃ (n : ℕ) (f : fin n → α), injective f ∧ range f = s :=
let ⟨n, f, hf⟩ := h.fin_embedding in ⟨n, f, f.injective, hf⟩

/-- Membership of a subset of a finite type is decidable.

Using this as an instance leads to potential loops with `subtype.fintype` under certain decidability
assumptions, so it should only be declared a local instance. -/
def decidable_mem_of_fintype [decidable_eq α] (s : set α) [fintype s] (a) : decidable (a ∈ s) :=
decidable_of_iff _ mem_to_finset

instance fintype_empty : fintype (∅ : set α) :=
fintype.of_finset ∅ $ by simp

theorem empty_card : fintype.card (∅ : set α) = 0 := rfl

@[simp] theorem empty_card' {h : fintype.{u} (∅ : set α)} :
  @fintype.card (∅ : set α) h = 0 :=
eq.trans (by congr) empty_card

@[simp] theorem finite_empty : @finite α ∅ := ⟨set.fintype_empty⟩

instance finite.inhabited : inhabited {s : set α // finite s} := ⟨⟨∅, finite_empty⟩⟩

/-- A `fintype` structure on `insert a s`. -/
def fintype_insert' {a : α} (s : set α) [fintype s] (h : a ∉ s) : fintype (insert a s : set α) :=
fintype.of_finset ⟨a ::ₘ s.to_finset.1,
  multiset.nodup_cons_of_nodup (by simp [h]) s.to_finset.2⟩ $ by simp

theorem card_fintype_insert' {a : α} (s : set α) [fintype s] (h : a ∉ s) :
  @fintype.card _ (fintype_insert' s h) = fintype.card s + 1 :=
by rw [fintype_insert', fintype.card_of_finset];
   simp [finset.card, to_finset]; refl

@[simp] theorem card_insert {a : α} (s : set α)
  [fintype s] (h : a ∉ s) {d : fintype.{u} (insert a s : set α)} :
  @fintype.card _ d = fintype.card s + 1 :=
by rw ← card_fintype_insert' s h; congr

lemma card_image_of_inj_on {s : set α} [fintype s]
  {f : α → β} [fintype (f '' s)] (H : ∀x∈s, ∀y∈s, f x = f y → x = y) :
  fintype.card (f '' s) = fintype.card s :=
by haveI := classical.prop_decidable; exact
calc fintype.card (f '' s) = (s.to_finset.image f).card : fintype.card_of_finset' _ (by simp)
... = s.to_finset.card : finset.card_image_of_inj_on
    (λ x hx y hy hxy, H x (mem_to_finset.1 hx) y (mem_to_finset.1 hy) hxy)
... = fintype.card s : (fintype.card_of_finset' _ (λ a, mem_to_finset)).symm

lemma card_image_of_injective (s : set α) [fintype s]
  {f : α → β} [fintype (f '' s)] (H : function.injective f) :
  fintype.card (f '' s) = fintype.card s :=
card_image_of_inj_on $ λ _ _ _ _ h, H h

section

local attribute [instance] decidable_mem_of_fintype

instance fintype_insert [decidable_eq α] (a : α) (s : set α) [fintype s] :
  fintype (insert a s : set α) :=
if h : a ∈ s then by rwa [insert_eq, union_eq_self_of_subset_left (singleton_subset_iff.2 h)]
else fintype_insert' _ h

end

@[simp] theorem finite.insert (a : α) {s : set α} : finite s → finite (insert a s)
| ⟨h⟩ := ⟨@set.fintype_insert _ (classical.dec_eq α) _ _ h⟩

lemma to_finset_insert [decidable_eq α] {a : α} {s : set α} (hs : finite s) :
  (hs.insert a).to_finset = insert a hs.to_finset :=
finset.ext $ by simp

@[simp] lemma insert_to_finset [decidable_eq α] {a : α} {s : set α} [fintype s] :
  (insert a s).to_finset = insert a s.to_finset :=
by simp [finset.ext_iff, mem_insert_iff]

@[elab_as_eliminator]
theorem finite.induction_on {C : set α → Prop} {s : set α} (h : finite s)
  (H0 : C ∅) (H1 : ∀ {a s}, a ∉ s → finite s → C s → C (insert a s)) : C s :=
let ⟨t⟩ := h in by exactI
match s.to_finset, @mem_to_finset _ s _ with
| ⟨l, nd⟩, al := begin
    change ∀ a, a ∈ l ↔ a ∈ s at al,
    clear _let_match _match t h, revert s nd al,
    refine multiset.induction_on l _ (λ a l IH, _); intros s nd al,
    { rw show s = ∅, from eq_empty_iff_forall_not_mem.2 (by simpa using al),
      exact H0 },
    { rw ← show insert a {x | x ∈ l} = s, from set.ext (by simpa using al),
      cases multiset.nodup_cons.1 nd with m nd',
      refine H1 _ ⟨finset.subtype.fintype ⟨l, nd'⟩⟩ (IH nd' (λ _, iff.rfl)),
      exact m }
  end
end

@[elab_as_eliminator]
theorem finite.dinduction_on {C : ∀s:set α, finite s → Prop} {s : set α} (h : finite s)
  (H0 : C ∅ finite_empty)
  (H1 : ∀ {a s}, a ∉ s → ∀ h : finite s, C s h → C (insert a s) (h.insert a)) :
  C s h :=
have ∀ h : finite s, C s h,
  from finite.induction_on h (λ h, H0) (λ a s has hs ih h, H1 has hs (ih _)),
this h

instance fintype_singleton (a : α) : fintype ({a} : set α) :=
unique.fintype

@[simp] theorem card_singleton (a : α) :
  fintype.card ({a} : set α) = 1 :=
fintype.card_of_subsingleton _

@[simp] theorem finite_singleton (a : α) : finite ({a} : set α) :=
⟨set.fintype_singleton _⟩

lemma subsingleton.finite {s : set α} (h : s.subsingleton) : finite s :=
h.induction_on finite_empty finite_singleton

lemma to_finset_singleton (a : α) : ({a} : set α).to_finset = {a} := rfl

lemma finite_is_top (α : Type*) [partial_order α] : finite {x : α | is_top x} :=
(subsingleton_is_top α).finite

lemma finite_is_bot (α : Type*) [partial_order α] : finite {x : α | is_bot x} :=
(subsingleton_is_bot α).finite

instance fintype_pure : ∀ a : α, fintype (pure a : set α) :=
set.fintype_singleton

theorem finite_pure (a : α) : finite (pure a : set α) :=
⟨set.fintype_pure a⟩

instance fintype_univ [fintype α] : fintype (@univ α) :=
fintype.of_equiv α $ (equiv.set.univ α).symm

theorem finite_univ [fintype α] : finite (@univ α) := ⟨set.fintype_univ⟩

/-- If `(set.univ : set α)` is finite then `α` is a finite type. -/
noncomputable def fintype_of_univ_finite (H : (univ : set α).finite ) :
  fintype α :=
@fintype.of_equiv _ (univ : set α) H.fintype (equiv.set.univ _)

lemma univ_finite_iff_nonempty_fintype :
  (univ : set α).finite ↔ nonempty (fintype α) :=
begin
  split,
  { intro h, exact ⟨fintype_of_univ_finite h⟩ },
  { rintro ⟨_i⟩, exactI finite_univ }
end

theorem infinite_univ_iff : (@univ α).infinite ↔ _root_.infinite α :=
⟨λ h₁, ⟨λ h₂, h₁ $ @finite_univ α h₂⟩, λ ⟨h₁⟩ h₂, h₁ (fintype_of_univ_finite h₂)⟩

theorem infinite_univ [h : _root_.infinite α] : infinite (@univ α) :=
infinite_univ_iff.2 h

theorem infinite_coe_iff {s : set α} : _root_.infinite s ↔ infinite s :=
⟨λ ⟨h₁⟩ h₂, h₁ h₂.fintype, λ h₁, ⟨λ h₂, h₁ ⟨h₂⟩⟩⟩

theorem infinite.to_subtype {s : set α} (h : infinite s) : _root_.infinite s :=
infinite_coe_iff.2 h

/-- Embedding of `ℕ` into an infinite set. -/
noncomputable def infinite.nat_embedding (s : set α) (h : infinite s) : ℕ ↪ s :=
by { haveI := h.to_subtype, exact infinite.nat_embedding s }

lemma infinite.exists_subset_card_eq {s : set α} (hs : infinite s) (n : ℕ) :
  ∃ t : finset α, ↑t ⊆ s ∧ t.card = n :=
⟨((finset.range n).map (hs.nat_embedding _)).map (embedding.subtype _), by simp⟩

lemma infinite.nonempty {s : set α} (h : s.infinite) : s.nonempty :=
let a := infinite.nat_embedding s h 37 in ⟨a.1, a.2⟩

instance fintype_union [decidable_eq α] (s t : set α) [fintype s] [fintype t] :
  fintype (s ∪ t : set α) :=
fintype.of_finset (s.to_finset ∪ t.to_finset) $ by simp

theorem finite.union {s t : set α} : finite s → finite t → finite (s ∪ t)
| ⟨hs⟩ ⟨ht⟩ := ⟨@set.fintype_union _ (classical.dec_eq α) _ _ hs ht⟩

lemma finite.sup {s t : set α} : finite s → finite t → finite (s ⊔ t) := finite.union

lemma infinite_of_finite_compl [_root_.infinite α] {s : set α}
  (hs : sᶜ.finite) : s.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

lemma finite.infinite_compl [_root_.infinite α] {s : set α}
  (hs : s.finite) : sᶜ.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

instance fintype_sep (s : set α) (p : α → Prop) [fintype s] [decidable_pred p] :
  fintype ({a ∈ s | p a} : set α) :=
fintype.of_finset (s.to_finset.filter p) $ by simp

instance fintype_inter (s t : set α) [fintype s] [decidable_pred (∈ t)] : fintype (s ∩ t : set α) :=
set.fintype_sep s t

/-- A `fintype` structure on a set defines a `fintype` structure on its subset. -/
def fintype_subset (s : set α) {t : set α} [fintype s] [decidable_pred (∈ t)] (h : t ⊆ s) :
  fintype t :=
by rw ← inter_eq_self_of_subset_right h; apply_instance

theorem finite.subset {s : set α} : finite s → ∀ {t : set α}, t ⊆ s → finite t
| ⟨hs⟩ t h := ⟨@set.fintype_subset _ _ _ hs (classical.dec_pred t) h⟩

@[simp] lemma finite_union {s t : set α} : finite (s ∪ t) ↔ finite s ∧ finite t :=
⟨λ h, ⟨h.subset (subset_union_left _ _), h.subset (subset_union_right _ _)⟩,
 λ ⟨hs, ht⟩, hs.union ht⟩

lemma finite.of_diff {s t : set α} (hd : finite (s \ t)) (ht : finite t) : finite s :=
(hd.union ht).subset $ subset_diff_union _ _

theorem finite.inter_of_left {s : set α} (h : finite s) (t : set α) : finite (s ∩ t) :=
h.subset (inter_subset_left _ _)

theorem finite.inter_of_right {s : set α} (h : finite s) (t : set α) : finite (t ∩ s) :=
h.subset (inter_subset_right _ _)

theorem finite.inf_of_left {s : set α} (h : finite s) (t : set α) : finite (s ⊓ t) :=
h.inter_of_left t

theorem finite.inf_of_right {s : set α} (h : finite s) (t : set α) : finite (t ⊓ s) :=
h.inter_of_right t

lemma finite.sInter {α : Type*} {s : set (set α)} {t : set α} (ht : t ∈ s)
  (hf : t.finite) : (⋂₀s).finite :=
hf.subset (sInter_subset_of_mem ht)

protected theorem infinite.mono {s t : set α} (h : s ⊆ t) : infinite s → infinite t :=
mt (λ ht, ht.subset h)

lemma infinite.diff {s t : set α} (hs : s.infinite) (ht : t.finite) :
  (s \ t).infinite :=
λ h, hs $ h.of_diff ht

@[simp] lemma infinite_union {s t : set α} : infinite (s ∪ t) ↔ infinite s ∨ infinite t :=
by simp only [infinite, finite_union, not_and_distrib]

instance fintype_image [decidable_eq β] (s : set α) (f : α → β) [fintype s] : fintype (f '' s) :=
fintype.of_finset (s.to_finset.image f) $ by simp

instance fintype_range [decidable_eq α] (f : ι → α) [fintype (plift ι)] :
  fintype (range f) :=
fintype.of_finset (finset.univ.image $ f ∘ plift.down) $
  by simp [(@equiv.plift ι).exists_congr_left]

theorem finite_range (f : ι → α) [fintype (plift ι)] : finite (range f) :=
by haveI := classical.dec_eq α; exact ⟨by apply_instance⟩

theorem finite.image {s : set α} (f : α → β) : finite s → finite (f '' s)
| ⟨h⟩ := ⟨@set.fintype_image _ _ (classical.dec_eq β) _ _ h⟩

theorem infinite_of_infinite_image (f : α → β) {s : set α} (hs : (f '' s).infinite) :
  s.infinite :=
mt (finite.image f) hs

lemma finite.dependent_image {s : set α} (hs : finite s) (F : Π i ∈ s, β) :
  finite {y : β | ∃ x (hx : x ∈ s), y = F x hx} :=
begin
  letI : fintype s := hs.fintype,
  convert finite_range (λ x : s, F x x.2),
  simp only [set_coe.exists, subtype.coe_mk, eq_comm],
end

theorem finite.of_preimage {f : α → β} {s : set β} (h : finite (f ⁻¹' s)) (hf : surjective f) :
  finite s :=
hf.image_preimage s ▸ h.image _

instance fintype_map {α β} [decidable_eq β] :
  ∀ (s : set α) (f : α → β) [fintype s], fintype (f <$> s) := set.fintype_image

theorem finite.map {α β} {s : set α} :
  ∀ (f : α → β), finite s → finite (f <$> s) := finite.image

/-- If a function `f` has a partial inverse and sends a set `s` to a set with `[fintype]` instance,
then `s` has a `fintype` structure as well. -/
def fintype_of_fintype_image (s : set α)
  {f : α → β} {g} (I : is_partial_inv f g) [fintype (f '' s)] : fintype s :=
fintype.of_finset ⟨_, @multiset.nodup_filter_map β α g _
  (@injective_of_partial_inv_right _ _ f g I) (f '' s).to_finset.2⟩ $ λ a,
begin
  suffices : (∃ b x, f x = b ∧ g b = some a ∧ x ∈ s) ↔ a ∈ s,
  by simpa [exists_and_distrib_left.symm, and.comm, and.left_comm, and.assoc],
  rw exists_swap,
  suffices : (∃ x, x ∈ s ∧ g (f x) = some a) ↔ a ∈ s, {simpa [and.comm, and.left_comm, and.assoc]},
  simp [I _, (injective_of_partial_inv I).eq_iff]
end

theorem finite_of_finite_image {s : set α} {f : α → β} (hi : set.inj_on f s) :
  finite (f '' s) → finite s | ⟨h⟩ :=
⟨@fintype.of_injective _ _ h (λ a : s, ⟨f a.1, mem_image_of_mem f a.2⟩) $
  λ a b eq, subtype.eq $ hi a.2 b.2 $ subtype.ext_iff_val.1 eq⟩

theorem finite_image_iff {s : set α} {f : α → β} (hi : inj_on f s) :
  finite (f '' s) ↔ finite s :=
⟨finite_of_finite_image hi, finite.image _⟩

theorem infinite_image_iff {s : set α} {f : α → β} (hi : inj_on f s) :
  infinite (f '' s) ↔ infinite s :=
not_congr $ finite_image_iff hi

theorem infinite_of_inj_on_maps_to {s : set α} {t : set β} {f : α → β}
  (hi : inj_on f s) (hm : maps_to f s t) (hs : infinite s) : infinite t :=
((infinite_image_iff hi).2 hs).mono (maps_to'.mp hm)

theorem infinite.exists_ne_map_eq_of_maps_to {s : set α} {t : set β} {f : α → β}
  (hs : infinite s) (hf : maps_to f s t) (ht : finite t) :
  ∃ (x ∈ s) (y ∈ s), x ≠ y ∧ f x = f y :=
begin
  contrapose! ht,
  exact infinite_of_inj_on_maps_to (λ x hx y hy, not_imp_not.1 (ht x hx y hy)) hf hs
end

theorem infinite.exists_lt_map_eq_of_maps_to [linear_order α] {s : set α} {t : set β} {f : α → β}
  (hs : infinite s) (hf : maps_to f s t) (ht : finite t) :
  ∃ (x ∈ s) (y ∈ s), x < y ∧ f x = f y :=
let ⟨x, hx, y, hy, hxy, hf⟩ := hs.exists_ne_map_eq_of_maps_to hf ht
in hxy.lt_or_lt.elim (λ hxy, ⟨x, hx, y, hy, hxy, hf⟩) (λ hyx, ⟨y, hy, x, hx, hyx, hf.symm⟩)

lemma finite.exists_lt_map_eq_of_range_subset [linear_order α] [_root_.infinite α] {t : set β}
  {f : α → β} (hf : range f ⊆ t) (ht : finite t) :
  ∃ a b, a < b ∧ f a = f b :=
begin
  rw [range_subset_iff, ←maps_univ_to] at hf,
  obtain ⟨a, -, b, -, h⟩ := (@infinite_univ α _).exists_lt_map_eq_of_maps_to hf ht,
  exact ⟨a, b, h⟩,
end

theorem infinite_range_of_injective [_root_.infinite α] {f : α → β} (hi : injective f) :
  infinite (range f) :=
by { rw [←image_univ, infinite_image_iff (inj_on_of_injective hi _)], exact infinite_univ }

theorem infinite_of_injective_forall_mem [_root_.infinite α] {s : set β} {f : α → β}
  (hi : injective f) (hf : ∀ x : α, f x ∈ s) : infinite s :=
by { rw ←range_subset_iff at hf, exact (infinite_range_of_injective hi).mono hf }

theorem finite.preimage {s : set β} {f : α → β}
  (I : set.inj_on f (f⁻¹' s)) (h : finite s) : finite (f ⁻¹' s) :=
finite_of_finite_image I (h.subset (image_preimage_subset f s))

theorem finite.preimage_embedding {s : set β} (f : α ↪ β) (h : s.finite) : (f ⁻¹' s).finite :=
finite.preimage (λ _ _ _ _ h', f.injective h') h

lemma finite_option {s : set (option α)} : finite s ↔ finite {x : α | some x ∈ s} :=
⟨λ h, h.preimage_embedding embedding.some,
  λ h, ((h.image some).insert none).subset $
    λ x, option.cases_on x (λ _, or.inl rfl) (λ x hx, or.inr $ mem_image_of_mem _ hx)⟩

instance fintype_Union [decidable_eq α] [fintype (plift ι)]
  (f : ι → set α) [∀ i, fintype (f i)] : fintype (⋃ i, f i) :=
fintype.of_finset (finset.univ.bUnion (λ i : plift ι, (f i.down).to_finset)) $ by simp

theorem finite_Union [fintype (plift ι)] {f : ι → set α} (H : ∀i, finite (f i)) :
  finite (⋃ i, f i) :=
⟨@set.fintype_Union _ _ (classical.dec_eq α) _ _ (λ i, finite.fintype (H i))⟩

/-- A union of sets with `fintype` structure over a set with `fintype` structure has a `fintype`
structure. -/
def fintype_bUnion [decidable_eq α] {ι : Type*} {s : set ι} [fintype s]
  (f : ι → set α) (H : ∀ i ∈ s, fintype (f i)) : fintype (⋃ i ∈ s, f i) :=
by rw bUnion_eq_Union; exact
@set.fintype_Union _ _ _ _ _ (by rintro ⟨i, hi⟩; exact H i hi)

instance fintype_bUnion' [decidable_eq α] {ι : Type*} {s : set ι} [fintype s]
  (f : ι → set α) [H : ∀ i, fintype (f i)] : fintype (⋃ i ∈ s, f i) :=
fintype_bUnion _ (λ i _, H i)

theorem finite.sUnion {s : set (set α)} (h : finite s) (H : ∀t∈s, finite t) : finite (⋃₀ s) :=
by rw sUnion_eq_Union; haveI := finite.fintype h;
   apply finite_Union; simpa using H

theorem finite.bUnion {α} {ι : Type*} {s : set ι} {f : Π i ∈ s, set α} :
  finite s → (∀ i ∈ s, finite (f i ‹_›)) → finite (⋃ i∈s, f i ‹_›)
| ⟨hs⟩ h := by rw [bUnion_eq_Union]; exactI finite_Union (λ i, h _ _)

instance fintype_lt_nat (n : ℕ) : fintype {i | i < n} :=
fintype.of_finset (finset.range n) $ by simp

instance fintype_le_nat (n : ℕ) : fintype {i | i ≤ n} :=
by simpa [nat.lt_succ_iff] using set.fintype_lt_nat (n+1)

lemma finite_le_nat (n : ℕ) : finite {i | i ≤ n} := ⟨set.fintype_le_nat _⟩

lemma finite_lt_nat (n : ℕ) : finite {i | i < n} := ⟨set.fintype_lt_nat _⟩

lemma infinite.exists_nat_lt {s : set ℕ} (hs : infinite s) (n : ℕ) : ∃ m ∈ s, n < m :=
let ⟨m, hm⟩ := (hs.diff $ set.finite_le_nat n).nonempty in ⟨m, by simpa using hm⟩

instance fintype_prod (s : set α) (t : set β) [fintype s] [fintype t] : fintype (s ×ˢ t : set _) :=
fintype.of_finset (s.to_finset.product t.to_finset) $ by simp

lemma finite.prod {s : set α} {t : set β} : finite s → finite t → finite (s ×ˢ t)
| ⟨hs⟩ ⟨ht⟩ := by exactI ⟨set.fintype_prod s t⟩

/-- `image2 f s t` is finitype if `s` and `t` are. -/
instance fintype_image2 [decidable_eq γ] (f : α → β → γ) (s : set α) (t : set β)
  [hs : fintype s] [ht : fintype t] : fintype (image2 f s t : set γ) :=
by { rw ← image_prod, apply set.fintype_image }

lemma finite.image2 (f : α → β → γ) {s : set α} {t : set β} (hs : finite s) (ht : finite t) :
  finite (image2 f s t) :=
by { rw ← image_prod, exact (hs.prod ht).image _ }

/-- If `s : set α` is a set with `fintype` instance and `f : α → set β` is a function such that
each `f a`, `a ∈ s`, has a `fintype` structure, then `s >>= f` has a `fintype` structure. -/
def fintype_bind {α β} [decidable_eq β] (s : set α) [fintype s]
  (f : α → set β) (H : ∀ a ∈ s, fintype (f a)) : fintype (s >>= f) :=
set.fintype_bUnion _ H

instance fintype_bind' {α β} [decidable_eq β] (s : set α) [fintype s]
  (f : α → set β) [H : ∀ a, fintype (f a)] : fintype (s >>= f) :=
fintype_bind _ _ (λ i _, H i)

theorem finite.bind {α β} {s : set α} {f : α → set β} (h : finite s) (hf : ∀ a ∈ s, finite (f a)) :
  finite (s >>= f) :=
h.bUnion hf

instance fintype_seq [decidable_eq β] (f : set (α → β)) (s : set α) [fintype f] [fintype s] :
  fintype (f.seq s) :=
by { rw seq_def, apply set.fintype_bUnion' }

instance fintype_seq' {α β : Type u} [decidable_eq β]
  (f : set (α → β)) (s : set α) [fintype f] [fintype s] :
  fintype (f <*> s) :=
set.fintype_seq f s

theorem finite.seq {f : set (α → β)} {s : set α} (hf : finite f) (hs : finite s) :
  finite (f.seq s) :=
by { rw seq_def, exact hf.bUnion (λ f _, hs.image _) }

theorem finite.seq' {α β : Type u} {f : set (α → β)} {s : set α} (hf : finite f) (hs : finite s) :
  finite (f <*> s) :=
hf.seq hs

/-- There are finitely many subsets of a given finite set -/
lemma finite.finite_subsets {α : Type u} {a : set α} (h : finite a) : finite {b | b ⊆ a} :=
⟨fintype.of_finset ((finset.powerset h.to_finset).map finset.coe_emb.1) $ λ s,
  by simpa [← @exists_finite_iff_finset α (λ t, t ⊆ a ∧ t = s), subset_to_finset_iff,
    ← and.assoc] using h.subset⟩

lemma exists_min_image [linear_order β] (s : set α) (f : α → β) (h1 : finite s) :
  s.nonempty → ∃ a ∈ s, ∀ b ∈ s, f a ≤ f b
| ⟨x, hx⟩ := by simpa only [exists_prop, finite.mem_to_finset]
  using h1.to_finset.exists_min_image f ⟨x, h1.mem_to_finset.2 hx⟩

lemma exists_max_image [linear_order β] (s : set α) (f : α → β) (h1 : finite s) :
  s.nonempty → ∃ a ∈ s, ∀ b ∈ s, f b ≤ f a
| ⟨x, hx⟩ := by simpa only [exists_prop, finite.mem_to_finset]
  using h1.to_finset.exists_max_image f ⟨x, h1.mem_to_finset.2 hx⟩

theorem exists_lower_bound_image [hα : nonempty α] [linear_order β] (s : set α) (f : α → β)
  (h : s.finite) : ∃ (a : α), ∀ b ∈ s, f a ≤ f b :=
begin
  by_cases hs : set.nonempty s,
  { exact let ⟨x₀, H, hx₀⟩ := set.exists_min_image s f h hs in ⟨x₀, λ x hx, hx₀ x hx⟩ },
  { exact nonempty.elim hα (λ a, ⟨a, λ x hx, absurd (set.nonempty_of_mem hx) hs⟩) }
end

theorem exists_upper_bound_image [hα : nonempty α] [linear_order β] (s : set α) (f : α → β)
  (h : s.finite) : ∃ (a : α), ∀ b ∈ s, f b ≤ f a :=
begin
  by_cases hs : set.nonempty s,
  { exact let ⟨x₀, H, hx₀⟩ := set.exists_max_image s f h hs in ⟨x₀, λ x hx, hx₀ x hx⟩ },
  { exact nonempty.elim hα (λ a, ⟨a, λ x hx, absurd (set.nonempty_of_mem hx) hs⟩) }
end

end set

namespace finset
variables [decidable_eq β]
variables {s : finset α}

lemma finite_to_set (s : finset α) : set.finite (↑s : set α) :=
set.finite_mem_finset s

@[simp] lemma finite_to_set_to_finset {α : Type*} (s : finset α) :
  (finite_to_set s).to_finset = s :=
by { ext, rw [set.finite.mem_to_finset, mem_coe] }

end finset

namespace set

/-- Finite product of finite sets is finite -/
lemma finite.pi {δ : Type*} [fintype δ] {κ : δ → Type*} {t : Π d, set (κ d)}
  (ht : ∀ d, (t d).finite) :
  (pi univ t).finite :=
begin
  lift t to Π d, finset (κ d) using ht,
  classical,
  rw ← fintype.coe_pi_finset,
  exact (fintype.pi_finset t).finite_to_set,
end

/-- A finite union of finsets is finite. -/
lemma union_finset_finite_of_range_finite (f : α → finset β) (h : (range f).finite) :
  (⋃ a, (f a : set β)).finite :=
begin
  rw ← bUnion_range,
  exact h.bUnion (λ y hy, y.finite_to_set)
end

lemma finite_subset_Union {s : set α} (hs : finite s)
  {ι} {t : ι → set α} (h : s ⊆ ⋃ i, t i) : ∃ I : set ι, finite I ∧ s ⊆ ⋃ i ∈ I, t i :=
begin
  casesI hs,
  choose f hf using show ∀ x : s, ∃ i, x.1 ∈ t i, {simpa [subset_def] using h},
  refine ⟨range f, finite_range f, λ x hx, _⟩,
  rw [bUnion_range, mem_Union],
  exact ⟨⟨x, hx⟩, hf _⟩
end

lemma eq_finite_Union_of_finite_subset_Union  {ι} {s : ι → set α} {t : set α} (tfin : finite t)
  (h : t ⊆ ⋃ i, s i) :
  ∃ I : set ι, (finite I) ∧ ∃ σ : {i | i ∈ I} → set α,
     (∀ i, finite (σ i)) ∧ (∀ i, σ i ⊆ s i) ∧ t = ⋃ i, σ i :=
let ⟨I, Ifin, hI⟩ := finite_subset_Union tfin h in
⟨I, Ifin, λ x, s x ∩ t,
    λ i, tfin.subset (inter_subset_right _ _),
    λ i, inter_subset_left _ _,
    begin
      ext x,
      rw mem_Union,
      split,
      { intro x_in,
        rcases mem_Union.mp (hI x_in) with ⟨i, _, ⟨hi, rfl⟩, H⟩,
        use [i, hi, H, x_in] },
      { rintros ⟨i, hi, H⟩,
        exact H }
    end⟩

/-- An increasing union distributes over finite intersection. -/
lemma Union_Inter_of_monotone {ι ι' α : Type*} [fintype ι] [linear_order ι']
  [nonempty ι'] {s : ι → ι' → set α} (hs : ∀ i, monotone (s i)) :
  (⋃ j : ι', ⋂ i : ι, s i j) = ⋂ i : ι, ⋃ j : ι', s i j :=
begin
  ext x, refine ⟨λ hx, Union_Inter_subset hx, λ hx, _⟩,
  simp only [mem_Inter, mem_Union, mem_Inter] at hx ⊢, choose j hj using hx,
  obtain ⟨j₀⟩ := show nonempty ι', by apply_instance,
  refine ⟨finset.univ.fold max j₀ j, λ i, hs i _ (hj i)⟩,
  rw [finset.fold_op_rel_iff_or (@le_max_iff _ _)],
  exact or.inr ⟨i, finset.mem_univ i, le_rfl⟩
end

lemma Union_pi_of_monotone {ι ι' : Type*} [linear_order ι'] [nonempty ι'] {α : ι → Type*}
  {I : set ι} {s : Π i, ι' → set (α i)} (hI : finite I) (hs : ∀ i ∈ I, monotone (s i)) :
  (⋃ j : ι', I.pi (λ i, s i j)) = I.pi (λ i, ⋃ j, s i j) :=
begin
  simp only [pi_def, bInter_eq_Inter, preimage_Union],
  haveI := hI.fintype,
  exact Union_Inter_of_monotone (λ i j₁ j₂ h, preimage_mono $ hs i i.2 h)
end

lemma Union_univ_pi_of_monotone {ι ι' : Type*} [linear_order ι'] [nonempty ι'] [fintype ι]
  {α : ι → Type*} {s : Π i, ι' → set (α i)} (hs : ∀ i, monotone (s i)) :
  (⋃ j : ι', pi univ (λ i, s i j)) = pi univ (λ i, ⋃ j, s i j) :=
Union_pi_of_monotone (finite.of_fintype _) (λ i _, hs i)

instance nat.fintype_Iio (n : ℕ) : fintype (Iio n) :=
fintype.of_finset (finset.range n) $ by simp

/--
If `P` is some relation between terms of `γ` and sets in `γ`,
such that every finite set `t : set γ` has some `c : γ` related to it,
then there is a recursively defined sequence `u` in `γ`
so `u n` is related to the image of `{0, 1, ..., n-1}` under `u`.

(We use this later to show sequentially compact sets
are totally bounded.)
-/
lemma seq_of_forall_finite_exists  {γ : Type*}
  {P : γ → set γ → Prop} (h : ∀ t,  finite t → ∃ c, P c t) :
  ∃ u : ℕ → γ, ∀ n, P (u n) (u '' Iio n) :=
⟨λ n, @nat.strong_rec_on' (λ _, γ) n $ λ n ih, classical.some $ h
    (range $ λ m : Iio n, ih m.1 m.2)
    (finite_range _),
λ n, begin
  classical,
  refine nat.strong_rec_on' n (λ n ih, _),
  rw nat.strong_rec_on_beta', convert classical.some_spec (h _ _),
  ext x, split,
  { rintros ⟨m, hmn, rfl⟩, exact ⟨⟨m, hmn⟩, rfl⟩ },
  { rintros ⟨⟨m, hmn⟩, rfl⟩, exact ⟨m, hmn, rfl⟩ }
end⟩

lemma finite_range_ite {p : α → Prop} [decidable_pred p] {f g : α → β} (hf : finite (range f))
  (hg : finite (range g)) : finite (range (λ x, if p x then f x else g x)) :=
(hf.union hg).subset range_ite_subset

lemma finite_range_const {c : β} : finite (range (λ x : α, c)) :=
(finite_singleton c).subset range_const_subset

lemma range_find_greatest_subset {P : α → ℕ → Prop} [∀ x, decidable_pred (P x)] {b : ℕ}:
  range (λ x, nat.find_greatest (P x) b) ⊆ ↑(finset.range (b + 1)) :=
by { rw range_subset_iff, intro x, simp [nat.lt_succ_iff, nat.find_greatest_le] }

lemma finite_range_find_greatest {P : α → ℕ → Prop} [∀ x, decidable_pred (P x)] {b : ℕ} :
  finite (range (λ x, nat.find_greatest (P x) b)) :=
(finset.range (b + 1)).finite_to_set.subset range_find_greatest_subset

lemma card_lt_card {s t : set α} [fintype s] [fintype t] (h : s ⊂ t) :
  fintype.card s < fintype.card t :=
fintype.card_lt_of_injective_not_surjective (set.inclusion h.1) (set.inclusion_injective h.1) $
  λ hst, (ssubset_iff_subset_ne.1 h).2 (eq_of_inclusion_surjective hst)

lemma card_le_of_subset {s t : set α} [fintype s] [fintype t] (hsub : s ⊆ t) :
  fintype.card s ≤ fintype.card t :=
fintype.card_le_of_injective (set.inclusion hsub) (set.inclusion_injective hsub)

lemma eq_of_subset_of_card_le {s t : set α} [fintype s] [fintype t]
   (hsub : s ⊆ t) (hcard : fintype.card t ≤ fintype.card s) : s = t :=
(eq_or_ssubset_of_subset hsub).elim id
  (λ h, absurd hcard $ not_le_of_lt $ card_lt_card h)

lemma subset_iff_to_finset_subset (s t : set α) [fintype s] [fintype t] :
  s ⊆ t ↔ s.to_finset ⊆ t.to_finset :=
by simp

@[simp, mono] lemma finite.to_finset_mono {s t : set α} {hs : finite s} {ht : finite t} :
  hs.to_finset ⊆ ht.to_finset ↔ s ⊆ t :=
begin
  split,
  { intros h x,
    rw [←finite.mem_to_finset hs, ←finite.mem_to_finset ht],
    exact λ hx, h hx },
  { intros h x,
    rw [finite.mem_to_finset hs, finite.mem_to_finset ht],
    exact λ hx, h hx }
end

@[simp, mono] lemma finite.to_finset_strict_mono {s t : set α} {hs : finite s} {ht : finite t} :
  hs.to_finset ⊂ ht.to_finset ↔ s ⊂ t :=
begin
  rw [←lt_eq_ssubset, ←finset.lt_iff_ssubset, lt_iff_le_and_ne, lt_iff_le_and_ne],
  simp
end

lemma card_range_of_injective [fintype α] {f : α → β} (hf : injective f)
  [fintype (range f)] : fintype.card (range f) = fintype.card α :=
eq.symm $ fintype.card_congr $ equiv.of_injective f hf

lemma finite.exists_maximal_wrt [partial_order β] (f : α → β) (s : set α) (h : set.finite s) :
  s.nonempty → ∃ a ∈ s, ∀ a' ∈ s, f a ≤ f a' → f a = f a' :=
begin
  classical,
  refine h.induction_on _ _,
  { exact λ h, absurd h empty_not_nonempty },
  intros a s his _ ih _,
  cases s.eq_empty_or_nonempty with h h,
  { use a, simp [h] },
  rcases ih h with ⟨b, hb, ih⟩,
  by_cases f b ≤ f a,
  { refine ⟨a, set.mem_insert _ _, λ c hc hac, le_antisymm hac _⟩,
    rcases set.mem_insert_iff.1 hc with rfl | hcs,
    { refl },
    { rwa [← ih c hcs (le_trans h hac)] } },
  { refine ⟨b, set.mem_insert_of_mem _ hb, λ c hc hbc, _⟩,
    rcases set.mem_insert_iff.1 hc with rfl | hcs,
    { exact (h hbc).elim },
    { exact ih c hcs hbc } }
end

lemma finite.card_to_finset {s : set α} [fintype s] (h : s.finite) :
  h.to_finset.card = fintype.card s :=
begin
  rw [← finset.card_attach, finset.attach_eq_univ, ← fintype.card],
  refine fintype.card_congr (equiv.set_congr _),
  ext x, show x ∈ h.to_finset ↔ x ∈ s,
  simp,
end

lemma infinite.exists_not_mem_finset {s : set α} (hs : s.infinite) (f : finset α) :
  ∃ a ∈ s, a ∉ f :=
let ⟨a, has, haf⟩ := (hs.diff f.finite_to_set).nonempty in ⟨a, has, λ h, haf $ finset.mem_coe.1 h⟩

section decidable_eq

lemma to_finset_compl {α : Type*} [fintype α] [decidable_eq α]
  (s : set α) [fintype (sᶜ : set α)] [fintype s] : sᶜ.to_finset = (s.to_finset)ᶜ :=
by ext; simp

lemma to_finset_inter {α : Type*} [decidable_eq α] (s t : set α) [fintype (s ∩ t : set α)]
  [fintype s] [fintype t] : (s ∩ t).to_finset = s.to_finset ∩ t.to_finset :=
by ext; simp

lemma to_finset_union {α : Type*} [decidable_eq α] (s t : set α) [fintype (s ∪ t : set α)]
  [fintype s] [fintype t] : (s ∪ t).to_finset = s.to_finset ∪ t.to_finset :=
by ext; simp

instance fintype_sdiff  {α : Type*} [decidable_eq α]
  (s t : set α) [fintype s] [fintype t] :
  fintype (s \ t : set α) :=
fintype.of_finset (s.to_finset \ t.to_finset) $ by simp

lemma to_finset_sdiff {α : Type*} [decidable_eq α] (s t : set α) [fintype s] [fintype t]
  [fintype (s \ t : set α)] : (s \ t).to_finset = s.to_finset \ t.to_finset :=
by ext; simp

lemma to_finset_ne_eq_erase {α : Type*} [decidable_eq α] [fintype α] (a : α)
  [fintype {x : α | x ≠ a}] : {x : α | x ≠ a}.to_finset = finset.univ.erase a :=
by ext; simp

lemma card_ne_eq [fintype α] (a : α) [fintype {x : α | x ≠ a}] :
  fintype.card {x : α | x ≠ a} = fintype.card α - 1 :=
begin
  haveI := classical.dec_eq α,
  rw [←to_finset_card, to_finset_ne_eq_erase, finset.card_erase_of_mem (finset.mem_univ _),
      finset.card_univ, nat.pred_eq_sub_one],
end

end decidable_eq

section

variables [semilattice_sup α] [nonempty α] {s : set α}

/--A finite set is bounded above.-/
protected lemma finite.bdd_above (hs : finite s) : bdd_above s :=
finite.induction_on hs bdd_above_empty $ λ a s _ _ h, h.insert a

/--A finite union of sets which are all bounded above is still bounded above.-/
lemma finite.bdd_above_bUnion {I : set β} {S : β → set α} (H : finite I) :
  (bdd_above (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_above (S i)) :=
finite.induction_on H
  (by simp only [bUnion_empty, bdd_above_empty, ball_empty_iff])
  (λ a s ha _ hs, by simp only [bUnion_insert, ball_insert_iff, bdd_above_union, hs])

end

section

variables [semilattice_inf α] [nonempty α] {s : set α}

/--A finite set is bounded below.-/
protected lemma finite.bdd_below (hs : finite s) : bdd_below s :=
@finite.bdd_above (order_dual α) _ _ _ hs

/--A finite union of sets which are all bounded below is still bounded below.-/
lemma finite.bdd_below_bUnion {I : set β} {S : β → set α} (H : finite I) :
  (bdd_below (⋃i∈I, S i)) ↔ (∀i ∈ I, bdd_below (S i)) :=
@finite.bdd_above_bUnion (order_dual α) _ _ _ _ _ H

end

end set

namespace finset

/-- A finset is bounded above. -/
protected lemma bdd_above [semilattice_sup α] [nonempty α] (s : finset α) :
  bdd_above (↑s : set α) :=
s.finite_to_set.bdd_above

/-- A finset is bounded below. -/
protected lemma bdd_below [semilattice_inf α] [nonempty α] (s : finset α) :
  bdd_below (↑s : set α) :=
s.finite_to_set.bdd_below

end finset

namespace fintype
variables [fintype α] {p q : α → Prop} [decidable_pred p] [decidable_pred q]

@[simp]
lemma card_subtype_compl : fintype.card {x // ¬ p x} = fintype.card α - fintype.card {x // p x} :=
begin
  classical,
  rw [fintype.card_of_subtype (set.to_finset pᶜ), set.to_finset_compl p, finset.card_compl,
      fintype.card_of_subtype (set.to_finset p)];
    intros; simp; refl
end

/-- If two subtypes of a fintype have equal cardinality, so do their complements. -/
lemma card_compl_eq_card_compl (h : fintype.card {x // p x} = fintype.card {x // q x}) :
  fintype.card {x // ¬ p x} = fintype.card {x // ¬ q x} :=
by simp only [card_subtype_compl, h]

end fintype

/--
If a set `s` does not contain any elements between any pair of elements `x, z ∈ s` with `x ≤ z`
(i.e if given `x, y, z ∈ s` such that `x ≤ y ≤ z`, then `y` is either `x` or `z`), then `s` is
finite.
-/
lemma set.finite_of_forall_between_eq_endpoints {α : Type*} [linear_order α] (s : set α)
  (h : ∀ (x ∈ s) (y ∈ s) (z ∈ s), x ≤ y → y ≤ z → x = y ∨ y = z) :
  set.finite s :=
begin
  by_contra hinf,
  change s.infinite at hinf,
  rcases hinf.exists_subset_card_eq 3 with ⟨t, hts, ht⟩,
  let f := t.order_iso_of_fin ht,
  let x := f 0,
  let y := f 1,
  let z := f 2,
  have := h x (hts x.2) y (hts y.2) z (hts z.2)
    (f.monotone $ by dec_trivial) (f.monotone $ by dec_trivial),
  have key₁ : (0 : fin 3) ≠ 1 := by dec_trivial,
  have key₂ : (1 : fin 3) ≠ 2 := by dec_trivial,
  cases this,
  { dsimp only [x, y] at this, exact key₁ (f.injective $ subtype.coe_injective this) },
  { dsimp only [y, z] at this, exact key₂ (f.injective $ subtype.coe_injective this) }
end
