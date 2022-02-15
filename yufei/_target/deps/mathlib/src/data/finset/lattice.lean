/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.finset.fold
import data.finset.option
import data.finset.prod
import data.multiset.lattice
import order.complete_lattice
import order.lexicographic
/-!
# Lattice operations on finsets
-/

variables {α β γ ι : Type*}

namespace finset
open multiset order_dual

/-! ### sup -/
section sup
-- TODO: define with just `[has_bot α]` where some lemmas hold without requiring `[order_bot α]`
variables [semilattice_sup α] [order_bot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : finset β) (f : β → α) : α := s.fold (⊔) ⊥ f

variables {s s₁ s₂ : finset β} {f g : β → α}

lemma sup_def : s.sup f = (s.1.map f).sup := rfl

@[simp] lemma sup_empty : (∅ : finset β).sup f = ⊥ :=
fold_empty

@[simp] lemma sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
fold_cons h

@[simp] lemma sup_insert [decidable_eq β] {b : β} : (insert b s : finset β).sup f = f b ⊔ s.sup f :=
fold_insert_idem

lemma sup_image [decidable_eq β] (s : finset γ) (f : γ → β) (g : β → α) :
  (s.image f).sup g = s.sup (g ∘ f) :=
fold_image_idem

@[simp] lemma sup_map (s : finset γ) (f : γ ↪ β) (g : β → α) :
  (s.map f).sup g = s.sup (g ∘ f) :=
fold_map

@[simp] lemma sup_singleton {b : β} : ({b} : finset β).sup f = f b :=
sup_singleton

lemma sup_union [decidable_eq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
finset.induction_on s₁ (by rw [empty_union, sup_empty, bot_sup_eq]) $ λ a s has ih,
by rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]

lemma sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g :=
begin
  refine finset.cons_induction_on s _ (λ b t _ h, _),
  { rw [sup_empty, sup_empty, sup_empty, bot_sup_eq] },
  { rw [sup_cons, sup_cons, sup_cons, h],
    exact sup_sup_sup_comm _ _ _ _ }
end

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.sup f = s₂.sup g :=
by subst hs; exact finset.fold_congr hfg

@[simp] lemma sup_le_iff {a : α} : s.sup f ≤ a ↔ (∀b ∈ s, f b ≤ a) :=
begin
  apply iff.trans multiset.sup_le,
  simp only [multiset.mem_map, and_imp, exists_imp_distrib],
  exact ⟨λ k b hb, k _ _ hb rfl, λ k a' b hb h, h ▸ k _ hb⟩,
end

@[simp] lemma sup_bUnion [decidable_eq β] (s : finset γ) (t : γ → finset β) :
  (s.bUnion t).sup f = s.sup (λ x, (t x).sup f) :=
eq_of_forall_ge_iff $ λ c, by simp [@forall_swap _ β]

lemma sup_const {s : finset β} (h : s.nonempty) (c : α) : s.sup (λ _, c) = c :=
eq_of_forall_ge_iff $ λ b, sup_le_iff.trans h.forall_const

@[simp] lemma sup_bot (s : finset β) : s.sup (λ _, ⊥) = (⊥ : α) :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact sup_empty },
  { exact sup_const hs _ }
end

lemma sup_ite (p : β → Prop) [decidable_pred p] :
  s.sup (λ i, ite (p i) (f i) (g i)) =
    (s.filter p).sup f ⊔ (s.filter (λ i, ¬ p i)).sup g :=
fold_ite _

lemma sup_le {a : α} : (∀b ∈ s, f b ≤ a) → s.sup f ≤ a :=
sup_le_iff.2

lemma le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
sup_le_iff.1 le_rfl _ hb

lemma sup_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.sup f ≤ s.sup g :=
sup_le (λ b hb, le_trans (h b hb) (le_sup hb))

lemma sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
sup_le $ assume b hb, le_sup (h hb)

@[simp] lemma sup_lt_iff [is_total α (≤)] {a : α} (ha : ⊥ < a) : s.sup f < a ↔ (∀ b ∈ s, f b < a) :=
⟨(λ hs b hb, lt_of_le_of_lt (le_sup hb) hs), finset.cons_induction_on s (λ _, ha)
  (λ c t hc, by simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using and.imp_right)⟩

@[simp] lemma le_sup_iff [is_total α (≤)] {a : α} (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b :=
⟨finset.cons_induction_on s (λ h, absurd h (not_le_of_lt ha))
  (λ c t hc ih, by simpa using @or.rec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a ≤ f b)
    (λ h, ⟨c, or.inl rfl, h⟩) (λ h, let ⟨b, hb, hle⟩ := ih h in ⟨b, or.inr hb, hle⟩)),
(λ ⟨b, hb, hle⟩, trans hle (le_sup hb))⟩

@[simp] lemma lt_sup_iff [is_total α (≤)] {a : α} : a < s.sup f ↔ ∃ b ∈ s, a < f b :=
⟨finset.cons_induction_on s (λ h, absurd h not_lt_bot)
  (λ c t hc ih, by simpa using @or.rec _ _ (∃ b, (b = c ∨ b ∈ t) ∧ a < f b)
    (λ h, ⟨c, or.inl rfl, h⟩) (λ h, let ⟨b, hb, hlt⟩ := ih h in ⟨b, or.inr hb, hlt⟩)),
(λ ⟨b, hb, hlt⟩, lt_of_lt_of_le hlt (le_sup hb))⟩

lemma sup_comm (s : finset β) (t : finset γ) (f : β → γ → α) :
  s.sup (λ b, t.sup (f b)) = t.sup (λ c, s.sup (λ b, f b c)) :=
begin
  refine eq_of_forall_ge_iff (λ a, _),
  simp_rw sup_le_iff,
  exact ⟨λ h c hc b hb, h b hb c hc, λ h b hb c hc, h c hc b hb⟩,
end

@[simp] lemma sup_attach (s : finset β) (f : β → α) : s.attach.sup (λ x, f x) = s.sup f :=
(s.attach.sup_map (function.embedding.subtype _) f).symm.trans $ congr_arg _ attach_map_val

/-- See also `finset.product_bUnion`. -/
lemma sup_product_left (s : finset β) (t : finset γ) (f : β × γ → α) :
  (s.product t).sup f = s.sup (λ i, t.sup $ λ i', f ⟨i, i'⟩) :=
begin
  refine le_antisymm _ (sup_le (λ i hi, sup_le $ λ i' hi', le_sup $ mem_product.2 ⟨hi, hi'⟩)),
  refine sup_le _,
  rintro ⟨i, i'⟩ hi,
  rw mem_product at hi,
  refine le_trans _ (le_sup hi.1),
  convert le_sup hi.2,
end

lemma sup_product_right (s : finset β) (t : finset γ) (f : β × γ → α) :
  (s.product t).sup f = t.sup (λ i', s.sup $ λ i, f ⟨i, i'⟩) :=
by rw [sup_product_left, sup_comm]

@[simp] lemma sup_erase_bot [decidable_eq α] (s : finset α) : (s.erase ⊥).sup id = s.sup id :=
begin
  refine (sup_mono (s.erase_subset _)).antisymm (finset.sup_le_iff.2 $ λ a ha, _),
  obtain rfl | ha' := eq_or_ne a ⊥,
  { exact bot_le },
  { exact le_sup (mem_erase.2 ⟨ha', ha⟩) }
end

lemma sup_sdiff_right {α β : Type*} [generalized_boolean_algebra α] (s : finset β) (f : β → α)
  (a : α) :
  s.sup (λ b, f b \ a) = s.sup f \ a :=
begin
  refine finset.cons_induction_on s _ (λ b t _ h, _),
  { rw [sup_empty, sup_empty, bot_sdiff] },
  { rw [sup_cons, sup_cons, h, sup_sdiff] }
end

lemma comp_sup_eq_sup_comp [semilattice_sup γ] [order_bot γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) :
  g (s.sup f) = s.sup (g ∘ f) :=
finset.cons_induction_on s bot (λ c t hc ih, by rw [sup_cons, sup_cons, g_sup, ih])

lemma comp_sup_eq_sup_comp_of_is_total [is_total α (≤)] {γ : Type} [semilattice_sup γ] [order_bot γ]
  (g : α → γ) (mono_g : monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
comp_sup_eq_sup_comp g mono_g.map_sup bot

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
lemma sup_coe {P : α → Prop}
  {Pbot : P ⊥} {Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@sup _ _ (subtype.semilattice_sup Psup) (subtype.order_bot Pbot) t f : α) = t.sup (λ x, f x) :=
by { rw [comp_sup_eq_sup_comp coe]; intros; refl }

@[simp] lemma sup_to_finset {α β} [decidable_eq β]
  (s : finset α) (f : α → multiset β) :
  (s.sup f).to_finset = s.sup (λ x, (f x).to_finset) :=
comp_sup_eq_sup_comp multiset.to_finset to_finset_union rfl

theorem subset_range_sup_succ (s : finset ℕ) : s ⊆ range (s.sup id).succ :=
λ n hn, mem_range.2 $ nat.lt_succ_of_le $ le_sup hn

theorem exists_nat_subset_range (s : finset ℕ) : ∃n : ℕ, s ⊆ range n :=
⟨_, s.subset_range_sup_succ⟩

lemma sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
  (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) :=
begin
  induction s using finset.cons_induction with c s hc ih,
  { exact hb, },
  { rw sup_cons,
    apply hp,
    { exact hs c (mem_cons.2 (or.inl rfl)), },
    { exact ih (λ b h, hs b (mem_cons.2 (or.inr h))), }, },
end

lemma sup_le_of_le_directed {α : Type*} [semilattice_sup α] [order_bot α] (s : set α)
  (hs : s.nonempty) (hdir : directed_on (≤) s) (t : finset α) :
  (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x, x ∈ s ∧ t.sup id ≤ x :=
begin
  classical,
  apply finset.induction_on t,
  { simpa only [forall_prop_of_true, and_true, forall_prop_of_false, bot_le, not_false_iff,
      sup_empty, forall_true_iff, not_mem_empty], },
  { intros a r har ih h,
    have incs : ↑r ⊆ ↑(insert a r), by { rw finset.coe_subset, apply finset.subset_insert, },
    -- x ∈ s is above the sup of r
    obtain ⟨x, ⟨hxs, hsx_sup⟩⟩ := ih (λ x hx, h x $ incs hx),
    -- y ∈ s is above a
    obtain ⟨y, hys, hay⟩ := h a (finset.mem_insert_self a r),
    -- z ∈ s is above x and y
    obtain ⟨z, hzs, ⟨hxz, hyz⟩⟩ := hdir x hxs y hys,
    use [z, hzs],
    rw [sup_insert, id.def, _root_.sup_le_iff],
    exact ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩, },
end

-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : subsemilattice_sup_bot`
lemma sup_mem
  (s : set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ x y ∈ s, x ⊔ y ∈ s)
  {ι : Type*} (t : finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) :
  t.sup p ∈ s :=
@sup_induction _ _ _ _ _ _ (∈ s) w₁ w₂ h

@[simp]
lemma sup_eq_bot_iff (f : β → α)
  (S : finset β) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ :=
begin
  classical,
  induction S using finset.induction with a S haS hi;
  simp [*],
end

end sup

lemma sup_eq_supr [complete_lattice β] (s : finset α) (f : α → β) : s.sup f = (⨆a∈s, f a) :=
le_antisymm
  (finset.sup_le $ assume a ha, le_supr_of_le a $ le_supr _ ha)
  (supr_le $ assume a, supr_le $ assume ha, le_sup ha)

lemma sup_id_eq_Sup [complete_lattice α] (s : finset α) : s.sup id = Sup s :=
by simp [Sup_eq_supr, sup_eq_supr]

lemma sup_eq_Sup_image [complete_lattice β] (s : finset α) (f : α → β) : s.sup f = Sup (f '' s) :=
begin
  classical,
  rw [←finset.coe_image, ←sup_id_eq_Sup, sup_image, function.comp.left_id],
end

/-! ### inf -/
section inf
-- TODO: define with just `[has_top α]` where some lemmas hold without requiring `[order_top α]`
variables [semilattice_inf α] [order_top α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : finset β) (f : β → α) : α := s.fold (⊓) ⊤ f

variables {s s₁ s₂ : finset β} {f g : β → α}

lemma inf_def : s.inf f = (s.1.map f).inf := rfl

@[simp] lemma inf_empty : (∅ : finset β).inf f = ⊤ :=
fold_empty

@[simp] lemma inf_cons {b : β} (h : b ∉ s) : (cons b s h).inf f = f b ⊓ s.inf f :=
@sup_cons (order_dual α) _ _ _ _ _ _ h

@[simp] lemma inf_insert [decidable_eq β] {b : β} : (insert b s : finset β).inf f = f b ⊓ s.inf f :=
fold_insert_idem

lemma inf_image [decidable_eq β] (s : finset γ) (f : γ → β) (g : β → α) :
  (s.image f).inf g = s.inf (g ∘ f) :=
fold_image_idem

@[simp] lemma inf_map (s : finset γ) (f : γ ↪ β) (g : β → α) :
  (s.map f).inf g = s.inf (g ∘ f) :=
fold_map

@[simp] lemma inf_singleton {b : β} : ({b} : finset β).inf f = f b :=
inf_singleton

lemma inf_union [decidable_eq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
@sup_union (order_dual α) _ _ _ _ _ _ _

lemma inf_inf : s.inf (f ⊓ g) = s.inf f ⊓ s.inf g :=
@sup_sup (order_dual α) _ _ _ _ _ _

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.inf f = s₂.inf g :=
by subst hs; exact finset.fold_congr hfg

@[simp] lemma inf_bUnion [decidable_eq β] (s : finset γ) (t : γ → finset β) :
  (s.bUnion t).inf f = s.inf (λ x, (t x).inf f) :=
@sup_bUnion (order_dual α) _ _ _ _ _ _ _ _

lemma inf_const {s : finset β} (h : s.nonempty) (c : α) : s.inf (λ _, c) = c :=
@sup_const (order_dual α) _ _ _ _ h _

@[simp] lemma inf_top (s : finset β) : s.inf (λ _, ⊤) = (⊤ : α) := @sup_bot (order_dual α) _ _ _ _

lemma le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀ b ∈ s, a ≤ f b :=
@sup_le_iff (order_dual α) _ _ _ _ _ _

lemma inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
le_inf_iff.1 le_rfl _ hb

lemma le_inf {a : α} : (∀b ∈ s, a ≤ f b) → a ≤ s.inf f :=
le_inf_iff.2

lemma inf_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.inf f ≤ s.inf g :=
le_inf (λ b hb, le_trans (inf_le hb) (h b hb))

lemma inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
le_inf $ assume b hb, inf_le (h hb)

@[simp] lemma lt_inf_iff [is_total α (≤)] {a : α} (ha : a < ⊤) : a < s.inf f ↔ (∀ b ∈ s, a < f b) :=
@sup_lt_iff (order_dual α) _ _ _ _ _ _ _ ha

@[simp] lemma inf_le_iff [is_total α (≤)] {a : α} (ha : a < ⊤) : s.inf f ≤ a ↔ (∃ b ∈ s, f b ≤ a) :=
@le_sup_iff (order_dual α) _ _ _ _ _ _ _ ha

@[simp] lemma inf_lt_iff [is_total α (≤)] {a : α} : s.inf f < a ↔ (∃ b ∈ s, f b < a) :=
@lt_sup_iff (order_dual α) _ _ _ _ _ _ _

lemma inf_attach (s : finset β) (f : β → α) : s.attach.inf (λ x, f x) = s.inf f :=
@sup_attach (order_dual α) _ _ _ _ _

lemma inf_comm (s : finset β) (t : finset γ) (f : β → γ → α) :
  s.inf (λ b, t.inf (f b)) = t.inf (λ c, s.inf (λ b, f b c)) :=
@sup_comm (order_dual α) _ _ _ _ _ _ _

lemma inf_product_left (s : finset β) (t : finset γ) (f : β × γ → α) :
  (s.product t).inf f = s.inf (λ i, t.inf $ λ i', f ⟨i, i'⟩) :=
@sup_product_left (order_dual α) _ _ _ _ _ _ _

lemma inf_product_right (s : finset β) (t : finset γ) (f : β × γ → α) :
  (s.product t).inf f = t.inf (λ i', s.inf $ λ i, f ⟨i, i'⟩) :=
@sup_product_right (order_dual α) _ _ _ _ _ _ _

@[simp] lemma inf_erase_top [decidable_eq α] (s : finset α) : (s.erase ⊤).inf id = s.inf id :=
@sup_erase_bot (order_dual α) _ _ _ _

lemma sup_sdiff_left {α β : Type*} [boolean_algebra α] (s : finset β) (f : β → α) (a : α) :
  s.sup (λ b, a \ f b) = a \ s.inf f :=
begin
  refine finset.cons_induction_on s _ (λ b t _ h, _),
  { rw [sup_empty, inf_empty, sdiff_top] },
  { rw [sup_cons, inf_cons, h, sdiff_inf] }
end

lemma inf_sdiff_left {α β : Type*} [boolean_algebra α] {s : finset β} (hs : s.nonempty) (f : β → α)
  (a : α) :
  s.inf (λ b, a \ f b) = a \ s.sup f :=
begin
  induction hs using finset.nonempty.cons_induction with b b t _ _ h,
  { rw [sup_singleton, inf_singleton] },
  { rw [sup_cons, inf_cons, h, sdiff_sup] }
end

lemma inf_sdiff_right {α β : Type*} [boolean_algebra α] {s : finset β} (hs : s.nonempty) (f : β → α)
  (a : α) :
  s.inf (λ b, f b \ a) = s.inf f \ a :=
begin
  induction hs using finset.nonempty.cons_induction with b b t _ _ h,
  { rw [inf_singleton, inf_singleton] },
  { rw [inf_cons, inf_cons, h, inf_sdiff] }
end

lemma comp_inf_eq_inf_comp [semilattice_inf γ] [order_top γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) :
  g (s.inf f) = s.inf (g ∘ f) :=
@comp_sup_eq_sup_comp (order_dual α) _ (order_dual γ) _ _ _ _ _ _ _ g_inf top

lemma comp_inf_eq_inf_comp_of_is_total [h : is_total α (≤)] {γ : Type} [semilattice_inf γ]
  [order_top γ] (g : α → γ) (mono_g : monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
comp_inf_eq_inf_comp g mono_g.map_inf top

/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
lemma inf_coe {P : α → Prop}
  {Ptop : P ⊤} {Pinf : ∀{{x y}}, P x → P y → P (x ⊓ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@inf _ _ (subtype.semilattice_inf Pinf) (subtype.order_top Ptop) t f : α) = t.inf (λ x, f x) :=
@sup_coe (order_dual α) _ _ _ _ Ptop Pinf t f

lemma inf_induction {p : α → Prop} (ht : p ⊤) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
  (hs : ∀ b ∈ s, p (f b)) : p (s.inf f) :=
@sup_induction (order_dual α) _ _ _ _ _ _ ht hp hs

lemma inf_mem
  (s : set α) (w₁ : ⊤ ∈ s) (w₂ : ∀ x y ∈ s, x ⊓ y ∈ s)
  {ι : Type*} (t : finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) :
  t.inf p ∈ s :=
@inf_induction _ _ _ _ _ _ (∈ s) w₁ w₂ h

@[simp]
lemma inf_eq_top_iff (f : β → α)
  (S : finset β) : S.inf f = ⊤ ↔ ∀ s ∈ S, f s = ⊤ :=
@finset.sup_eq_bot_iff (order_dual α) _ _ _ _ _

end inf

section distrib_lattice
variables [distrib_lattice α]

section order_bot
variables [order_bot α] {s : finset β} {f : β → α} {a : α}

lemma sup_inf_distrib_left (s : finset ι) (f : ι → α) (a : α) :
  a ⊓ s.sup f = s.sup (λ i, a ⊓ f i) :=
begin
  induction s using finset.cons_induction with i s hi h,
  { simp_rw [finset.sup_empty, inf_bot_eq] },
  { rw [sup_cons, sup_cons, inf_sup_left, h] }
end

lemma sup_inf_distrib_right (s : finset ι) (f : ι → α) (a : α) :
  s.sup f ⊓ a = s.sup (λ i, f i ⊓ a) :=
by { rw [_root_.inf_comm, s.sup_inf_distrib_left], simp_rw _root_.inf_comm }

lemma disjoint_sup_right : disjoint a (s.sup f) ↔ ∀ i ∈ s, disjoint a (f i) :=
by simp only [disjoint_iff, sup_inf_distrib_left, sup_eq_bot_iff]

lemma disjoint_sup_left : disjoint (s.sup f) a ↔ ∀ i ∈ s, disjoint (f i) a :=
by simp only [disjoint_iff, sup_inf_distrib_right, sup_eq_bot_iff]

end order_bot

section order_top
variables [order_top α]

lemma inf_sup_distrib_left (s : finset ι) (f : ι → α) (a : α) :
  a ⊔ s.inf f = s.inf (λ i, a ⊔ f i) :=
@sup_inf_distrib_left (order_dual α) _ _ _ _ _ _

lemma inf_sup_distrib_right (s : finset ι) (f : ι → α) (a : α) :
  s.inf f ⊔ a = s.inf (λ i, f i ⊔ a) :=
@sup_inf_distrib_right (order_dual α) _ _ _ _ _ _

end order_top
end distrib_lattice

lemma inf_eq_infi [complete_lattice β] (s : finset α) (f : α → β) : s.inf f = (⨅a∈s, f a) :=
@sup_eq_supr _ (order_dual β) _ _ _

lemma inf_id_eq_Inf [complete_lattice α] (s : finset α) : s.inf id = Inf s :=
@sup_id_eq_Sup (order_dual α) _ _

lemma inf_eq_Inf_image [complete_lattice β] (s : finset α) (f : α → β) : s.inf f = Inf (f '' s) :=
@sup_eq_Sup_image _ (order_dual β) _ _ _

section sup'
variables [semilattice_sup α]

lemma sup_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ (a : α), s.sup (coe ∘ f : β → with_bot α) = ↑a :=
Exists.imp (λ a, Exists.fst) (@le_sup (with_bot α) _ _ _ _ _ _ h (f b) rfl)

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `finset.sup` which does not require `s` nonempty. -/
def sup' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
option.get $ let ⟨b, hb⟩ := H in option.is_some_iff_exists.2 (sup_of_mem f hb)

variables {s : finset β} (H : s.nonempty) (f : β → α)

@[simp] lemma coe_sup' : ((s.sup' H f : α) : with_bot α) = s.sup (coe ∘ f) :=
by rw [sup', ←with_bot.some_eq_coe, option.some_get]

@[simp] lemma sup'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).nonempty} :
  (cons b s hb).sup' h f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp only [coe_sup', sup_cons, with_bot.coe_sup], }

@[simp] lemma sup'_insert [decidable_eq β] {b : β} {h : (insert b s).nonempty} :
  (insert b s).sup' h f = f b ⊔ s.sup' H f :=
by { rw ←with_bot.coe_eq_coe, simp only [coe_sup', sup_insert, with_bot.coe_sup], }

@[simp] lemma sup'_singleton {b : β} {h : ({b} : finset β).nonempty} :
  ({b} : finset β).sup' h f = f b := rfl

lemma sup'_le {a : α} (hs : ∀ b ∈ s, f b ≤ a) : s.sup' H f ≤ a :=
by { rw [←with_bot.coe_le_coe, coe_sup'], exact sup_le (λ b h, with_bot.coe_le_coe.2 $ hs b h), }

lemma le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
by { rw [←with_bot.coe_le_coe, coe_sup'], exact le_sup h, }

@[simp] lemma sup'_const (a : α) : s.sup' H (λ b, a) = a :=
begin
  apply le_antisymm,
  { apply sup'_le, intros, exact le_rfl, },
  { apply le_sup' (λ b, a) H.some_spec, }
end

@[simp] lemma sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a :=
iff.intro (λ h b hb, trans (le_sup' f hb) h) (sup'_le H f)

@[simp] lemma sup'_lt_iff [is_total α (≤)] {a : α} : s.sup' H f < a ↔ (∀ b ∈ s, f b < a) :=
begin
  rw [←with_bot.coe_lt_coe, coe_sup', sup_lt_iff (with_bot.bot_lt_coe a)],
  exact ball_congr (λ b hb, with_bot.coe_lt_coe),
end

@[simp] lemma le_sup'_iff [is_total α (≤)] {a : α} : a ≤ s.sup' H f ↔ (∃ b ∈ s, a ≤ f b) :=
begin
  rw [←with_bot.coe_le_coe, coe_sup', le_sup_iff (with_bot.bot_lt_coe a)],
  exact bex_congr (λ b hb, with_bot.coe_le_coe),
end

@[simp] lemma lt_sup'_iff [is_total α (≤)] {a : α} : a < s.sup' H f ↔ (∃ b ∈ s, a < f b) :=
begin
  rw [←with_bot.coe_lt_coe, coe_sup', lt_sup_iff],
  exact bex_congr (λ b hb, with_bot.coe_lt_coe),
end

lemma sup'_bUnion [decidable_eq β] {s : finset γ} (Hs : s.nonempty) {t : γ → finset β}
  (Ht : ∀ b, (t b).nonempty) :
  (s.bUnion t).sup' (Hs.bUnion (λ b _, Ht b)) f = s.sup' Hs (λ b, (t b).sup' (Ht b) f) :=
eq_of_forall_ge_iff $ λ c, by simp [@forall_swap _ β]

lemma comp_sup'_eq_sup'_comp [semilattice_sup γ] {s : finset β} (H : s.nonempty)
  {f : β → α} (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) :
  g (s.sup' H f) = s.sup' H (g ∘ f) :=
begin
  rw [←with_bot.coe_eq_coe, coe_sup'],
  let g' : with_bot α → with_bot γ := with_bot.rec_bot_coe ⊥ (λ x, ↑(g x)),
  show g' ↑(s.sup' H f) = s.sup (λ a, g' ↑(f a)),
  rw coe_sup',
  refine comp_sup_eq_sup_comp g' _ rfl,
  intros f₁ f₂,
  cases f₁,
  { rw [with_bot.none_eq_bot, bot_sup_eq], exact bot_sup_eq.symm, },
  { cases f₂, refl,
    exact congr_arg coe (g_sup f₁ f₂), },
end

lemma sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
  (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) :=
begin
  show @with_bot.rec_bot_coe α (λ _, Prop) true p ↑(s.sup' H f),
  rw coe_sup',
  refine sup_induction trivial _ hs,
  rintro (_|a₁) h₁ a₂ h₂,
  { rw [with_bot.none_eq_bot, bot_sup_eq], exact h₂ },
  cases a₂,
  exacts [h₁, hp a₁ h₁ a₂ h₂]
end

lemma exists_mem_eq_sup' [is_total α (≤)] : ∃ b, b ∈ s ∧ s.sup' H f = f b :=
begin
  refine H.cons_induction (λ c, _) (λ c s hc hs ih, _),
  { exact ⟨c, mem_singleton_self c, rfl⟩, },
  { rcases ih with ⟨b, hb, h'⟩,
    rw [sup'_cons hs, h'],
    cases total_of (≤) (f b) (f c) with h h,
    { exact ⟨c, mem_cons.2 (or.inl rfl), sup_eq_left.2 h⟩, },
    { exact ⟨b, mem_cons.2 (or.inr hb), sup_eq_right.2 h⟩, }, },
end

lemma sup'_mem
  (s : set α) (w : ∀ x y ∈ s, x ⊔ y ∈ s)
  {ι : Type*} (t : finset ι) (H : t.nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) :
  t.sup' H p ∈ s := sup'_induction H p w h

@[congr] lemma sup'_congr {t : finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
  s.sup' H f = t.sup' (h₁ ▸ H) g :=
begin
  subst s,
  refine eq_of_forall_ge_iff (λ c, _),
  simp only [sup'_le_iff, h₂] { contextual := tt }
end

end sup'

section inf'
variables [semilattice_inf α]

lemma inf_of_mem {s : finset β} (f : β → α) {b : β} (h : b ∈ s) :
  ∃ (a : α), s.inf (coe ∘ f : β → with_top α) = ↑a :=
@sup_of_mem (order_dual α) _ _ _ f _ h

/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `finset.inf` which does not require `s` nonempty. -/
def inf' (s : finset β) (H : s.nonempty) (f : β → α) : α :=
@sup' (order_dual α) _ _ s H f

variables {s : finset β} (H : s.nonempty) (f : β → α)

@[simp] lemma coe_inf' : ((s.inf' H f : α) : with_top α) = s.inf (coe ∘ f) :=
@coe_sup' (order_dual α) _ _ _ H f

@[simp] lemma inf'_cons {b : β} {hb : b ∉ s} {h : (cons b s hb).nonempty} :
  (cons b s hb).inf' h f = f b ⊓ s.inf' H f :=
@sup'_cons (order_dual α) _ _ _ H f _ _ _

@[simp] lemma inf'_insert [decidable_eq β] {b : β} {h : (insert b s).nonempty} :
  (insert b s).inf' h f = f b ⊓ s.inf' H f :=
@sup'_insert (order_dual α) _ _ _ H f _ _ _

@[simp] lemma inf'_singleton {b : β} {h : ({b} : finset β).nonempty} :
  ({b} : finset β).inf' h f = f b := rfl

lemma le_inf' {a : α} (hs : ∀ b ∈ s, a ≤ f b) : a ≤ s.inf' H f :=
@sup'_le (order_dual α) _ _ _ H f _ hs

lemma inf'_le {b : β} (h : b ∈ s) : s.inf' ⟨b, h⟩ f ≤ f b :=
@le_sup' (order_dual α) _ _ _ f _ h

@[simp] lemma inf'_const (a : α) : s.inf' H (λ b, a) = a :=
@sup'_const (order_dual α) _ _ _ _ _

@[simp] lemma le_inf'_iff {a : α} : a ≤ s.inf' H f ↔ ∀ b ∈ s, a ≤ f b :=
@sup'_le_iff (order_dual α) _ _ _ H f _

@[simp] lemma lt_inf'_iff [is_total α (≤)] {a : α} : a < s.inf' H f ↔ (∀ b ∈ s, a < f b) :=
@sup'_lt_iff (order_dual α) _ _ _ H f _ _

@[simp] lemma inf'_le_iff [is_total α (≤)] {a : α} : s.inf' H f ≤ a ↔ (∃ b ∈ s, f b ≤ a) :=
@le_sup'_iff (order_dual α) _ _ _ H f _ _

@[simp] lemma inf'_lt_iff [is_total α (≤)] {a : α} : s.inf' H f < a ↔ (∃ b ∈ s, f b < a) :=
@lt_sup'_iff (order_dual α) _ _ _ H f _ _

lemma inf'_bUnion [decidable_eq β] {s : finset γ} (Hs : s.nonempty) {t : γ → finset β}
  (Ht : ∀ b, (t b).nonempty) :
  (s.bUnion t).inf' (Hs.bUnion (λ b _, Ht b)) f = s.inf' Hs (λ b, (t b).inf' (Ht b) f) :=
@sup'_bUnion (order_dual α) _ _ _ _ _ _ Hs _ Ht

lemma comp_inf'_eq_inf'_comp [semilattice_inf γ] {s : finset β} (H : s.nonempty)
  {f : β → α} (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) :
  g (s.inf' H f) = s.inf' H (g ∘ f) :=
@comp_sup'_eq_sup'_comp (order_dual α) _ (order_dual γ) _ _ _ H f g g_inf

lemma inf'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊓ a₂))
  (hs : ∀ b ∈ s, p (f b)) : p (s.inf' H f) :=
@sup'_induction (order_dual α) _ _ _ H f _ hp hs

lemma exists_mem_eq_inf' [is_total α (≤)] : ∃ b, b ∈ s ∧ s.inf' H f = f b :=
@exists_mem_eq_sup' (order_dual α) _ _ _ H f _

lemma inf'_mem (s : set α) (w : ∀ x y ∈ s, x ⊓ y ∈ s)
  {ι : Type*} (t : finset ι) (H : t.nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) :
  t.inf' H p ∈ s := inf'_induction H p w h

@[congr] lemma inf'_congr {t : finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
  s.inf' H f = t.inf' (h₁ ▸ H) g :=
@sup'_congr (order_dual α) _ _ _ H _ _ _ h₁ h₂

end inf'

section sup
variables [semilattice_sup α] [order_bot α]

lemma sup'_eq_sup {s : finset β} (H : s.nonempty) (f : β → α) : s.sup' H f = s.sup f :=
le_antisymm (sup'_le H f (λ b, le_sup)) (sup_le (λ b, le_sup' f))

lemma sup_closed_of_sup_closed {s : set α} (t : finset α) (htne : t.nonempty) (h_subset : ↑t ⊆ s)
  (h : ∀ a b ∈ s, a ⊔ b ∈ s) : t.sup id ∈ s :=
sup'_eq_sup htne id ▸ sup'_induction _ _ h h_subset

lemma exists_mem_eq_sup [is_total α (≤)] (s : finset β) (h : s.nonempty) (f : β → α) :
  ∃ b, b ∈ s ∧ s.sup f = f b :=
sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

lemma coe_sup_of_nonempty {s : finset β} (h : s.nonempty) (f : β → α) :
  (↑(s.sup f) : with_bot α) = s.sup (coe ∘ f) :=
by simp only [←sup'_eq_sup h, coe_sup' h]

end sup

section inf
variables [semilattice_inf α] [order_top α]

lemma inf'_eq_inf {s : finset β} (H : s.nonempty) (f : β → α) : s.inf' H f = s.inf f :=
@sup'_eq_sup (order_dual α) _ _ _ _ H f

lemma inf_closed_of_inf_closed {s : set α} (t : finset α) (htne : t.nonempty) (h_subset : ↑t ⊆ s)
  (h : ∀ a b ∈ s, a ⊓ b ∈ s) : t.inf id ∈ s :=
@sup_closed_of_sup_closed (order_dual α) _ _ _ t htne h_subset h

lemma exists_mem_eq_inf [is_total α (≤)] (s : finset β) (h : s.nonempty) (f : β → α) :
  ∃ a, a ∈ s ∧ s.inf f = f a :=
@exists_mem_eq_sup (order_dual α) _ _ _ _ _ h f

lemma coe_inf_of_nonempty {s : finset β} (h : s.nonempty) (f : β → α):
  (↑(s.inf f) : with_top α) = s.inf (λ i, f i) :=
@coe_sup_of_nonempty (order_dual α) _ _ _ _ h f

end inf

section sup
variables {C : β → Type*} [Π (b : β), semilattice_sup (C b)] [Π (b : β), order_bot (C b)]

@[simp]
protected lemma sup_apply (s : finset α) (f : α → Π (b : β), C b) (b : β) :
  s.sup f b = s.sup (λ a, f a b) :=
comp_sup_eq_sup_comp (λ x : Π b : β, C b, x b) (λ i j, rfl) rfl

end sup

section inf
variables {C : β → Type*} [Π (b : β), semilattice_inf (C b)] [Π (b : β), order_top (C b)]

@[simp]
protected lemma inf_apply (s : finset α) (f : α → Π (b : β), C b) (b : β) :
  s.inf f b = s.inf (λ a, f a b) :=
@finset.sup_apply _ _ (λ b, order_dual (C b)) _ _ s f b

end inf

section sup'
variables {C : β → Type*} [Π (b : β), semilattice_sup (C b)]

@[simp]
protected lemma sup'_apply {s : finset α} (H : s.nonempty) (f : α → Π (b : β), C b) (b : β) :
  s.sup' H f b = s.sup' H (λ a, f a b) :=
comp_sup'_eq_sup'_comp H (λ x : Π b : β, C b, x b) (λ i j, rfl)

end sup'

section inf'
variables {C : β → Type*} [Π (b : β), semilattice_inf (C b)]

@[simp]
protected lemma inf'_apply {s : finset α} (H : s.nonempty) (f : α → Π (b : β), C b) (b : β) :
  s.inf' H f b = s.inf' H (λ a, f a b) :=
@finset.sup'_apply _ _ (λ b, order_dual (C b)) _ _ H f b

end inf'

/-! ### max and min of finite sets -/
section max_min
variables [linear_order α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max : finset α → option α :=
fold (option.lift_or_get max) none some

theorem max_eq_sup_with_bot (s : finset α) :
  s.max = @sup (with_bot α) α _ _ s some := rfl

@[simp] theorem max_empty : (∅ : finset α).max = none := rfl

@[simp] theorem max_insert {a : α} {s : finset α} :
  (insert a s).max = option.lift_or_get max (some a) s.max := fold_insert_idem

@[simp] theorem max_singleton {a : α} : finset.max {a} = some a :=
by { rw [← insert_emptyc_eq], exact max_insert }

theorem max_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.max :=
(@le_sup (with_bot α) _ _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem max_of_nonempty {s : finset α} (h : s.nonempty) : ∃ a, a ∈ s.max :=
let ⟨a, ha⟩ := h in max_of_mem ha

theorem max_eq_none {s : finset α} : s.max = none ↔ s = ∅ :=
⟨λ h, s.eq_empty_or_nonempty.elim id
  (λ H, let ⟨a, ha⟩ := max_of_nonempty H in by rw h at ha; cases ha),
  λ h, h.symm ▸ max_empty⟩

theorem mem_of_max {s : finset α} : ∀ {a : α}, a ∈ s.max → a ∈ s :=
finset.induction_on s (λ _ H, by cases H)
  (λ b s _ (ih : ∀ {a}, a ∈ s.max → a ∈ s) a (h : a ∈ (insert b s).max),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice max_choice (some b) s.max with q q;
      rw [max_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end)

theorem le_max_of_mem {s : finset α} {a b : α} (h₁ : a ∈ s) (h₂ : b ∈ s.max) : a ≤ b :=
by rcases @le_sup (with_bot α) _ _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min : finset α → option α :=
fold (option.lift_or_get min) none some

theorem min_eq_inf_with_top (s : finset α) :
  s.min = @inf (with_top α) α _ _ s some := rfl

@[simp] theorem min_empty : (∅ : finset α).min = none := rfl

@[simp] theorem min_insert {a : α} {s : finset α} :
  (insert a s).min = option.lift_or_get min (some a) s.min :=
fold_insert_idem

@[simp] theorem min_singleton {a : α} : finset.min {a} = some a :=
by { rw ← insert_emptyc_eq, exact min_insert }

theorem min_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.min :=
(@inf_le (with_top α) _ _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem min_of_nonempty {s : finset α} (h : s.nonempty) : ∃ a, a ∈ s.min :=
let ⟨a, ha⟩ := h in min_of_mem ha

theorem min_eq_none {s : finset α} : s.min = none ↔ s = ∅ :=
⟨λ h, s.eq_empty_or_nonempty.elim id
  (λ H, let ⟨a, ha⟩ := min_of_nonempty H in by rw h at ha; cases ha),
  λ h, h.symm ▸ min_empty⟩

theorem mem_of_min {s : finset α} : ∀ {a : α}, a ∈ s.min → a ∈ s :=
@mem_of_max (order_dual α) _ s

theorem min_le_of_mem {s : finset α} {a b : α} (h₁ : b ∈ s) (h₂ : a ∈ s.min) : a ≤ b :=
by rcases @inf_le (with_top α) _ _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

/-- Given a nonempty finset `s` in a linear order `α `, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `option α`. -/
def min' (s : finset α) (H : s.nonempty) : α :=
@option.get _ s.min $
  let ⟨k, hk⟩ := H in
  let ⟨b, hb⟩ := min_of_mem hk in by simp at hb; simp [hb]

/-- Given a nonempty finset `s` in a linear order `α `, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `option α`. -/
def max' (s : finset α) (H : s.nonempty) : α :=
@option.get _ s.max $
  let ⟨k, hk⟩ := H in
  let ⟨b, hb⟩ := max_of_mem hk in by simp at hb; simp [hb]

variables (s : finset α) (H : s.nonempty)

theorem min'_mem : s.min' H ∈ s := mem_of_min $ by simp [min']

theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x := min_le_of_mem H2 $ option.get_mem _

theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H := H2 _ $ min'_mem _ _

theorem is_least_min' : is_least ↑s (s.min' H) := ⟨min'_mem _ _, min'_le _⟩

@[simp] lemma le_min'_iff {x} : x ≤ s.min' H ↔ ∀ y ∈ s, x ≤ y :=
le_is_glb_iff (is_least_min' s H).is_glb

/-- `{a}.min' _` is `a`. -/
@[simp] lemma min'_singleton (a : α) :
  ({a} : finset α).min' (singleton_nonempty _) = a :=
by simp [min']

theorem max'_mem : s.max' H ∈ s := mem_of_max $ by simp [max']

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ := le_max_of_mem H2 $ option.get_mem _

theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x := H2 _ $ max'_mem _ _

theorem is_greatest_max' : is_greatest ↑s (s.max' H) := ⟨max'_mem _ _, le_max' _⟩

@[simp] lemma max'_le_iff {x} : s.max' H ≤ x ↔ ∀ y ∈ s, y ≤ x :=
is_lub_le_iff (is_greatest_max' s H).is_lub

@[simp] lemma max'_lt_iff {x} : s.max' H < x ↔ ∀ y ∈ s, y < x :=
⟨λ Hlt y hy, (s.le_max' y hy).trans_lt Hlt, λ H, H _ $ s.max'_mem _⟩

@[simp] lemma lt_min'_iff {x} : x < s.min' H ↔ ∀ y ∈ s, x < y :=
@max'_lt_iff (order_dual α) _ _ H _

lemma max'_eq_sup' : s.max' H = s.sup' H id :=
eq_of_forall_ge_iff $ λ a, (max'_le_iff _ _).trans (sup'_le_iff _ _).symm

lemma min'_eq_inf' : s.min' H = s.inf' H id :=
@max'_eq_sup' (order_dual α) _ s H

/-- `{a}.max' _` is `a`. -/
@[simp] lemma max'_singleton (a : α) :
  ({a} : finset α).max' (singleton_nonempty _) = a :=
by simp [max']

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
  s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
is_glb_lt_is_lub_of_ne (s.is_least_min' _).is_glb (s.is_greatest_max' _).is_lub H1 H2 H3

/--
If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
lemma min'_lt_max'_of_card (h₂ : 1 < card s) :
  s.min' (finset.card_pos.mp $ lt_trans zero_lt_one h₂) <
  s.max' (finset.card_pos.mp $ lt_trans zero_lt_one h₂) :=
begin
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩,
  exact s.min'_lt_max' ha hb hab
end

lemma max'_eq_of_dual_min' {s : finset α} (hs : s.nonempty) :
  max' s hs = of_dual (min' (image to_dual s) (nonempty.image hs to_dual)) :=
begin
  rw [of_dual, to_dual, equiv.coe_fn_mk, equiv.coe_fn_symm_mk, id.def],
  simp_rw (@image_id (order_dual α) (s : finset (order_dual α))),
  refl,
end

lemma min'_eq_of_dual_max' {s : finset α} (hs : s.nonempty) :
  min' s hs = of_dual (max' (image to_dual s) (nonempty.image hs to_dual)) :=
begin
  rw [of_dual, to_dual, equiv.coe_fn_mk, equiv.coe_fn_symm_mk, id.def],
  simp_rw (@image_id (order_dual α) (s : finset (order_dual α))),
  refl,
end

@[simp] lemma of_dual_max_eq_min_of_dual {a b : α} :
  of_dual (max a b) = min (of_dual a) (of_dual b) := rfl

@[simp] lemma of_dual_min_eq_max_of_dual {a b : α} :
  of_dual (min a b) = max (of_dual a) (of_dual b) := rfl

lemma max'_subset {s t : finset α} (H : s.nonempty) (hst : s ⊆ t) :
  s.max' H ≤ t.max' (H.mono hst) :=
le_max' _ _ (hst (s.max'_mem H))

lemma min'_subset {s t : finset α} (H : s.nonempty) (hst : s ⊆ t) :
  t.min' (H.mono hst) ≤ s.min' H :=
min'_le _ _ (hst (s.min'_mem H))

lemma max'_insert (a : α) (s : finset α) (H : s.nonempty) :
  (insert a s).max' (s.insert_nonempty a) = max (s.max' H) a :=
(is_greatest_max' _ _).unique $
  by { rw [coe_insert, max_comm], exact (is_greatest_max' _ _).insert _ }

lemma min'_insert (a : α) (s : finset α) (H : s.nonempty) :
  (insert a s).min' (s.insert_nonempty a) = min (s.min' H) a :=
(is_least_min' _ _).unique $
  by { rw [coe_insert, min_comm], exact (is_least_min' _ _).insert _ }

lemma lt_max'_of_mem_erase_max' [decidable_eq α] {a : α} (ha : a ∈ s.erase (s.max' H)) :
  a < s.max' H :=
lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) $ ne_of_mem_of_not_mem ha $ not_mem_erase _ _

lemma min'_lt_of_mem_erase_min' [decidable_eq α] {a : α} (ha : a ∈ s.erase (s.min' H)) :
  s.min' H < a :=
@lt_max'_of_mem_erase_max' (order_dual α) _ s H _ a ha

@[simp] lemma max'_image [linear_order β]
  {f : α → β} (hf : monotone f) (s : finset α) (h : (s.image f).nonempty) :
  (s.image f).max' h = f (s.max' ((nonempty.image_iff f).mp h)) :=
begin
  refine le_antisymm (max'_le _ _ _ (λ y hy, _))
    (le_max' _ _ (mem_image.mpr ⟨_, max'_mem _ _, rfl⟩)),
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy,
  exact hf (le_max' _ _ hx)
end

@[simp] lemma min'_image [linear_order β]
  {f : α → β} (hf : monotone f) (s : finset α) (h : (s.image f).nonempty) :
  (s.image f).min' h = f (s.min' ((nonempty.image_iff f).mp h)) :=
begin
  refine le_antisymm (min'_le _ _ (mem_image.mpr ⟨_, min'_mem _ _, rfl⟩))
    (le_min' _ _ _ (λ y hy, _)),
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hy,
  exact hf (min'_le _ _ hx)
end

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_eliminator]
lemma induction_on_max [decidable_eq α] {p : finset α → Prop} (s : finset α) (h0 : p ∅)
  (step : ∀ a s, (∀ x ∈ s, x < a) → p s → p (insert a s)) : p s :=
begin
  induction s using finset.strong_induction_on with s ihs,
  rcases s.eq_empty_or_nonempty with rfl|hne,
  { exact h0 },
  { have H : s.max' hne ∈ s, from max'_mem s hne,
    rw ← insert_erase H,
    exact step _ _ (λ x, s.lt_max'_of_mem_erase_max' hne) (ihs _ $ erase_ssubset H) }
end

/-- Induction principle for `finset`s in a linearly ordered type: a predicate is true on all
`s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_eliminator]
lemma induction_on_min [decidable_eq α] {p : finset α → Prop} (s : finset α) (h0 : p ∅)
  (step : ∀ a s, (∀ x ∈ s, a < x) → p s → p (insert a s)) : p s :=
@induction_on_max (order_dual α) _ _ _ s h0 step

end max_min

section max_min_induction_value

variables [linear_order α] [linear_order β]

/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_eliminator]
lemma induction_on_max_value [decidable_eq ι] (f : ι → α)
  {p : finset ι → Prop} (s : finset ι) (h0 : p ∅)
  (step : ∀ a s, a ∉ s → (∀ x ∈ s, f x ≤ f a) → p s → p (insert a s)) : p s :=
begin
  induction s using finset.strong_induction_on with s ihs,
  rcases (s.image f).eq_empty_or_nonempty with hne|hne,
  { simp only [image_eq_empty] at hne,
    simp only [hne, h0] },
  { have H : (s.image f).max' hne ∈ (s.image f), from max'_mem (s.image f) hne,
    simp only [mem_image, exists_prop] at H,
    rcases H with ⟨a, has, hfa⟩,
    rw ← insert_erase has,
    refine step _ _ (not_mem_erase a s) (λ x hx, _) (ihs _ $ erase_ssubset has),
    rw hfa,
    exact le_max' _ _ (mem_image_of_mem _ $ mem_of_mem_erase hx) }
end

/-- Induction principle for `finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : finset α` provided that:

* it is true on the empty `finset`,
* for every `s : finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_eliminator]
lemma induction_on_min_value [decidable_eq ι] (f : ι → α)
  {p : finset ι → Prop} (s : finset ι) (h0 : p ∅)
  (step : ∀ a s, a ∉ s → (∀ x ∈ s, f a ≤ f x) → p s → p (insert a s)) : p s :=
@induction_on_max_value (order_dual α) ι _ _ _ _ s h0 step

end max_min_induction_value

section exists_max_min

variables [linear_order α]
lemma exists_max_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
begin
  cases max_of_nonempty (h.image f) with y hy,
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩,
  exact ⟨x, hx, λ x' hx', le_max_of_mem (mem_image_of_mem f hx') hy⟩,
end

lemma exists_min_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
@exists_max_image (order_dual α) β _ s f h

end exists_max_min
end finset

namespace multiset

lemma map_finset_sup [decidable_eq α] [decidable_eq β]
  (s : finset γ) (f : γ → multiset β) (g : β → α) (hg : function.injective g) :
  map g (s.sup f) = s.sup (map g ∘ f) :=
finset.comp_sup_eq_sup_comp _ (λ _ _, map_union hg) (map_zero _)

lemma count_finset_sup [decidable_eq β] (s : finset α) (f : α → multiset β) (b : β) :
  count b (s.sup f) = s.sup (λa, count b (f a)) :=
begin
  letI := classical.dec_eq α,
  refine s.induction _ _,
  { exact count_zero _ },
  { assume i s his ih,
    rw [finset.sup_insert, sup_eq_union, count_union, finset.sup_insert, ih],
    refl }
end

lemma mem_sup {α β} [decidable_eq β] {s : finset α} {f : α → multiset β}
  {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
begin
  classical,
  apply s.induction_on,
  { simp },
  { intros a s has hxs,
    rw [finset.sup_insert, multiset.sup_eq_union, multiset.mem_union],
    split,
    { intro hxi,
      cases hxi with hf hf,
      { refine ⟨a, _, hf⟩,
        simp only [true_or, eq_self_iff_true, finset.mem_insert] },
      { rcases hxs.mp hf with ⟨v, hv, hfv⟩,
        refine ⟨v, _, hfv⟩,
        simp only [hv, or_true, finset.mem_insert] } },
    { rintros ⟨v, hv, hfv⟩,
      rw [finset.mem_insert] at hv,
      rcases hv with rfl | hv,
      { exact or.inl hfv },
      { refine or.inr (hxs.mpr ⟨v, hv, hfv⟩) } } },
end

end multiset

namespace finset

lemma mem_sup {α β} [decidable_eq β] {s : finset α} {f : α → finset β}
  {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
begin
  change _ ↔ ∃ v ∈ s, x ∈ (f v).val,
  rw [←multiset.mem_sup, ←multiset.mem_to_finset, sup_to_finset],
  simp_rw [val_to_finset],
end

lemma sup_eq_bUnion {α β} [decidable_eq β] (s : finset α) (t : α → finset β) :
  s.sup t = s.bUnion t :=
by { ext, rw [mem_sup, mem_bUnion], }

@[simp] lemma sup_singleton'' [decidable_eq α] (s : finset β) (f : β → α) :
  s.sup (λ b, {f b}) = s.image f :=
by { ext a, rw [mem_sup, mem_image], simp only [mem_singleton, eq_comm] }

@[simp] lemma sup_singleton' [decidable_eq α] (s : finset α) : s.sup singleton = s :=
(s.sup_singleton'' _).trans image_id

end finset

section lattice
variables {ι' : Sort*} [complete_lattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
lemma supr_eq_supr_finset (s : ι → α) :
  (⨆i, s i) = (⨆t:finset ι, ⨆i∈t, s i) :=
begin
  classical,
  exact le_antisymm
    (supr_le $ assume b, le_supr_of_le {b} $ le_supr_of_le b $ le_supr_of_le
      (by simp) $ le_rfl)
    (supr_le $ assume t, supr_le $ assume b, supr_le $ assume hb, le_supr _ _)
end

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
lemma supr_eq_supr_finset' (s : ι' → α) :
  (⨆i, s i) = (⨆t:finset (plift ι'), ⨆i∈t, s (plift.down i)) :=
by rw [← supr_eq_supr_finset, ← equiv.plift.surjective.supr_comp]; refl

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
lemma infi_eq_infi_finset (s : ι → α) :
  (⨅i, s i) = (⨅t:finset ι, ⨅i∈t, s i) :=
@supr_eq_supr_finset (order_dual α) _ _ _

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨅ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
lemma infi_eq_infi_finset' (s : ι' → α) :
  (⨅i, s i) = (⨅t:finset (plift ι'), ⨅i∈t, s (plift.down i)) :=
@supr_eq_supr_finset' (order_dual α) _ _ _

end lattice

namespace set
variables {ι' : Sort*}

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
lemma Union_eq_Union_finset (s : ι → set α) :
  (⋃i, s i) = (⋃t:finset ι, ⋃i∈t, s i) :=
supr_eq_supr_finset s

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
lemma Union_eq_Union_finset' (s : ι' → set α) :
  (⋃i, s i) = (⋃t:finset (plift ι'), ⋃i∈t, s (plift.down i)) :=
supr_eq_supr_finset' s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
lemma Inter_eq_Inter_finset (s : ι → set α) :
  (⋂i, s i) = (⋂t:finset ι, ⋂i∈t, s i) :=
infi_eq_infi_finset s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
lemma Inter_eq_Inter_finset' (s : ι' → set α) :
  (⋂i, s i) = (⋂t:finset (plift ι'), ⋂i∈t, s (plift.down i)) :=
infi_eq_infi_finset' s

end set

namespace finset

open function

/-! ### Interaction with big lattice/set operations -/

section lattice

lemma supr_coe [has_Sup β] (f : α → β) (s : finset α) :
  (⨆ x ∈ (↑s : set α), f x) = ⨆ x ∈ s, f x :=
rfl

lemma infi_coe [has_Inf β] (f : α → β) (s : finset α) :
  (⨅ x ∈ (↑s : set α), f x) = ⨅ x ∈ s, f x :=
rfl

variables [complete_lattice β]

theorem supr_singleton (a : α) (s : α → β) : (⨆ x ∈ ({a} : finset α), s x) = s a :=
by simp

theorem infi_singleton (a : α) (s : α → β) : (⨅ x ∈ ({a} : finset α), s x) = s a :=
by simp

lemma supr_option_to_finset (o : option α) (f : α → β) :
  (⨆ x ∈ o.to_finset, f x) = ⨆ x ∈ o, f x :=
by simp

lemma infi_option_to_finset (o : option α) (f : α → β) :
  (⨅ x ∈ o.to_finset, f x) = ⨅ x ∈ o, f x :=
@supr_option_to_finset _ (order_dual β) _ _ _

variables [decidable_eq α]

theorem supr_union {f : α → β} {s t : finset α} :
  (⨆ x ∈ s ∪ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
by simp [supr_or, supr_sup_eq]

theorem infi_union {f : α → β} {s t : finset α} :
  (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ (⨅ x ∈ t, f x) :=
@supr_union α (order_dual β) _ _ _ _ _

lemma supr_insert (a : α) (s : finset α) (t : α → β) :
  (⨆ x ∈ insert a s, t x) = t a ⊔ (⨆ x ∈ s, t x) :=
by { rw insert_eq, simp only [supr_union, finset.supr_singleton] }

lemma infi_insert (a : α) (s : finset α) (t : α → β) :
  (⨅ x ∈ insert a s, t x) = t a ⊓ (⨅ x ∈ s, t x) :=
@supr_insert α (order_dual β)  _ _ _ _ _

lemma supr_finset_image {f : γ → α} {g : α → β} {s : finset γ} :
  (⨆ x ∈ s.image f, g x) = (⨆ y ∈ s, g (f y)) :=
by rw [← supr_coe, coe_image, supr_image, supr_coe]

lemma sup_finset_image {β γ : Type*} [semilattice_sup β] [order_bot β]
  (f : γ → α) (g : α → β) (s : finset γ) :
  (s.image f).sup g = s.sup (g ∘ f) :=
begin
  classical,
  induction s using finset.induction_on with a s' ha ih; simp *
end

lemma infi_finset_image {f : γ → α} {g : α → β} {s : finset γ} :
  (⨅ x ∈ s.image f, g x) = (⨅ y ∈ s, g (f y)) :=
by rw [← infi_coe, coe_image, infi_image, infi_coe]

lemma supr_insert_update {x : α} {t : finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨆ (i ∈ insert x t), function.update f x s i) = (s ⊔ ⨆ (i ∈ t), f i) :=
begin
  simp only [finset.supr_insert, update_same],
  rcongr i hi, apply update_noteq, rintro rfl, exact hx hi
end

lemma infi_insert_update {x : α} {t : finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨅ (i ∈ insert x t), update f x s i) = (s ⊓ ⨅ (i ∈ t), f i) :=
@supr_insert_update α (order_dual β) _ _ _ _ f _ hx

lemma supr_bUnion (s : finset γ) (t : γ → finset α) (f : α → β) :
  (⨆ y ∈ s.bUnion t, f y) = ⨆ (x ∈ s) (y ∈ t x), f y :=
by simp [@supr_comm _ α, supr_and]

lemma infi_bUnion (s : finset γ) (t : γ → finset α) (f : α → β) :
  (⨅ y ∈ s.bUnion t, f y) = ⨅ (x ∈ s) (y ∈ t x), f y :=
@supr_bUnion _ (order_dual β) _ _ _ _ _ _

end lattice

theorem set_bUnion_coe (s : finset α) (t : α → set β) :
  (⋃ x ∈ (↑s : set α), t x) = ⋃ x ∈ s, t x :=
rfl

theorem set_bInter_coe (s : finset α) (t : α → set β) :
  (⋂ x ∈ (↑s : set α), t x) = ⋂ x ∈ s, t x :=
rfl

theorem set_bUnion_singleton (a : α) (s : α → set β) :
  (⋃ x ∈ ({a} : finset α), s x) = s a :=
supr_singleton a s

theorem set_bInter_singleton (a : α) (s : α → set β) :
  (⋂ x ∈ ({a} : finset α), s x) = s a :=
infi_singleton a s

@[simp] lemma set_bUnion_preimage_singleton (f : α → β) (s : finset β) :
  (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' s :=
set.bUnion_preimage_singleton f s

lemma set_bUnion_option_to_finset (o : option α) (f : α → set β) :
  (⋃ x ∈ o.to_finset, f x) = ⋃ x ∈ o, f x :=
supr_option_to_finset o f

lemma set_bInter_option_to_finset (o : option α) (f : α → set β) :
  (⋂ x ∈ o.to_finset, f x) = ⋂ x ∈ o, f x :=
infi_option_to_finset o f

lemma subset_set_bUnion_of_mem {s : finset α} {f : α → set β} {x : α} (h : x ∈ s) :
  f x ⊆ ⋃ (y ∈ s), f y :=
show f x ≤ (⨆ y ∈ s, f y), from le_supr_of_le x $ le_supr _ h

variables [decidable_eq α]

lemma set_bUnion_union (s t : finset α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

lemma set_bInter_inter (s t : finset α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
infi_union

lemma set_bUnion_insert (a : α) (s : finset α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
supr_insert a s t

lemma set_bInter_insert (a : α) (s : finset α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
infi_insert a s t

lemma set_bUnion_finset_image {f : γ → α} {g : α → set β} {s : finset γ} :
  (⋃x ∈ s.image f, g x) = (⋃y ∈ s, g (f y)) :=
supr_finset_image

lemma set_bInter_finset_image {f : γ → α} {g : α → set β} {s : finset γ} :
  (⋂ x ∈ s.image f, g x) = (⋂ y ∈ s, g (f y)) :=
infi_finset_image

lemma set_bUnion_insert_update {x : α} {t : finset α} (f : α → set β) {s : set β} (hx : x ∉ t) :
  (⋃ (i ∈ insert x t), @update _ _ _ f x s i) = (s ∪ ⋃ (i ∈ t), f i) :=
supr_insert_update f hx

lemma set_bInter_insert_update {x : α} {t : finset α} (f : α → set β) {s : set β} (hx : x ∉ t) :
  (⋂ (i ∈ insert x t), @update _ _ _ f x s i) = (s ∩ ⋂ (i ∈ t), f i) :=
infi_insert_update f hx

lemma set_bUnion_bUnion (s : finset γ) (t : γ → finset α) (f : α → set β) :
  (⋃ y ∈ s.bUnion t, f y) = ⋃ (x ∈ s) (y ∈ t x), f y :=
supr_bUnion s t f

lemma set_bInter_bUnion (s : finset γ) (t : γ → finset α) (f : α → set β) :
  (⋂ y ∈ s.bUnion t, f y) = ⋂ (x ∈ s) (y ∈ t x), f y :=
infi_bUnion s t f

end finset
