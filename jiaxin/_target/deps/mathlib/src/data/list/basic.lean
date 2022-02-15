/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import data.nat.basic

/-!
# Basic properties of lists
-/

open function nat (hiding one_pos)

namespace list
universes u v w x
variables {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

attribute [inline] list.head

instance : is_left_id (list α) has_append.append [] :=
⟨ nil_append ⟩

instance : is_right_id (list α) has_append.append [] :=
⟨ append_nil ⟩

instance : is_associative (list α) has_append.append :=
⟨ append_assoc ⟩

theorem cons_ne_nil (a : α) (l : list α) : a::l ≠ [].

theorem cons_ne_self (a : α) (l : list α) : a::l ≠ l :=
mt (congr_arg length) (nat.succ_ne_self _)

theorem head_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → h₁ = h₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pheq)

theorem tail_eq_of_cons_eq {h₁ h₂ : α} {t₁ t₂ : list α} :
      (h₁::t₁) = (h₂::t₂) → t₁ = t₂ :=
assume Peq, list.no_confusion Peq (assume Pheq Pteq, Pteq)

@[simp] theorem cons_injective {a : α} : injective (cons a) :=
assume l₁ l₂, assume Pe, tail_eq_of_cons_eq Pe

theorem cons_inj (a : α) {l l' : list α} : a::l = a::l' ↔ l = l' :=
cons_injective.eq_iff

theorem exists_cons_of_ne_nil {l : list α} (h : l ≠ nil) : ∃ b L, l = b :: L :=
by { induction l with c l',  contradiction,  use [c,l'], }

/-! ### mem -/

theorem mem_singleton_self (a : α) : a ∈ [a] := mem_cons_self _ _

theorem eq_of_mem_singleton {a b : α} : a ∈ [b] → a = b :=
assume : a ∈ [b], or.elim (eq_or_mem_of_mem_cons this)
  (assume : a = b, this)
  (assume : a ∈ [], absurd this (not_mem_nil a))

@[simp] theorem mem_singleton {a b : α} : a ∈ [b] ↔ a = b :=
⟨eq_of_mem_singleton, or.inl⟩

theorem mem_of_mem_cons_of_mem {a b : α} {l : list α} : a ∈ b::l → b ∈ l → a ∈ l :=
assume ainbl binl, or.elim (eq_or_mem_of_mem_cons ainbl)
  (assume : a = b, begin subst a, exact binl end)
  (assume : a ∈ l, this)

theorem _root_.decidable.list.eq_or_ne_mem_of_mem [decidable_eq α]
  {a b : α} {l : list α} (h : a ∈ b :: l) : a = b ∨ (a ≠ b ∧ a ∈ l) :=
decidable.by_cases or.inl $ assume : a ≠ b, h.elim or.inl $ assume h, or.inr ⟨this, h⟩

theorem eq_or_ne_mem_of_mem {a b : α} {l : list α} : a ∈ b :: l → a = b ∨ (a ≠ b ∧ a ∈ l) :=
by classical; exact decidable.list.eq_or_ne_mem_of_mem

theorem not_mem_append {a : α} {s t : list α} (h₁ : a ∉ s) (h₂ : a ∉ t) : a ∉ s ++ t :=
mt mem_append.1 $ not_or_distrib.2 ⟨h₁, h₂⟩

theorem ne_nil_of_mem {a : α} {l : list α} (h : a ∈ l) : l ≠ [] :=
by intro e; rw e at h; cases h

theorem mem_split {a : α} {l : list α} (h : a ∈ l) : ∃ s t : list α, l = s ++ a :: t :=
begin
  induction l with b l ih, {cases h}, rcases h with rfl | h,
  { exact ⟨[], l, rfl⟩ },
  { rcases ih h with ⟨s, t, rfl⟩,
    exact ⟨b::s, t, rfl⟩ }
end

theorem mem_of_ne_of_mem {a y : α} {l : list α} (h₁ : a ≠ y) (h₂ : a ∈ y :: l) : a ∈ l :=
or.elim (eq_or_mem_of_mem_cons h₂) (λe, absurd e h₁) (λr, r)

theorem ne_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ≠ b :=
assume nin aeqb, absurd (or.inl aeqb) nin

theorem not_mem_of_not_mem_cons {a b : α} {l : list α} : a ∉ b::l → a ∉ l :=
assume nin nainl, absurd (or.inr nainl) nin

theorem not_mem_cons_of_ne_of_not_mem {a y : α} {l : list α} : a ≠ y → a ∉ l → a ∉ y::l :=
assume p1 p2, not.intro (assume Pain, absurd (eq_or_mem_of_mem_cons Pain) (not_or p1 p2))

theorem ne_and_not_mem_of_not_mem_cons {a y : α} {l : list α} : a ∉ y::l → a ≠ y ∧ a ∉ l :=
assume p, and.intro (ne_of_not_mem_cons p) (not_mem_of_not_mem_cons p)

@[simp] theorem mem_map {f : α → β} {b : β} {l : list α} : b ∈ map f l ↔ ∃ a, a ∈ l ∧ f a = b :=
begin
  -- This proof uses no axioms, that's why it's longer that `induction`; simp [...]
  induction l with a l ihl,
  { split, { rintro ⟨_⟩ }, { rintro ⟨a, ⟨_⟩, _⟩ } },
  { refine (or_congr eq_comm ihl).trans _,
    split,
    { rintro (h|⟨c, hcl, h⟩),
      exacts [⟨a, or.inl rfl, h⟩, ⟨c, or.inr hcl, h⟩] },
    { rintro ⟨c, (hc|hc), h⟩,
      exacts [or.inl $ (congr_arg f hc.symm).trans h, or.inr ⟨c, hc, h⟩] } }
end

alias mem_map ↔ list.exists_of_mem_map _

theorem mem_map_of_mem (f : α → β) {a : α} {l : list α} (h : a ∈ l) : f a ∈ map f l :=
mem_map.2 ⟨a, h, rfl⟩

theorem mem_map_of_injective {f : α → β} (H : injective f) {a : α} {l : list α} :
  f a ∈ map f l ↔ a ∈ l :=
⟨λ m, let ⟨a', m', e⟩ := exists_of_mem_map m in H e ▸ m', mem_map_of_mem _⟩

lemma forall_mem_map_iff {f : α → β} {l : list α} {P : β → Prop} :
  (∀ i ∈ l.map f, P i) ↔ ∀ j ∈ l, P (f j) :=
begin
  split,
  { assume H j hj,
    exact H (f j) (mem_map_of_mem f hj) },
  { assume H i hi,
    rcases mem_map.1 hi with ⟨j, hj, ji⟩,
    rw ← ji,
    exact H j hj }
end

@[simp] lemma map_eq_nil {f : α → β} {l : list α} : list.map f l = [] ↔ l = [] :=
⟨by cases l; simp only [forall_prop_of_true, map, forall_prop_of_false, not_false_iff],
  λ h, h.symm ▸ rfl⟩

@[simp] theorem mem_join {a : α} : ∀ {L : list (list α)}, a ∈ join L ↔ ∃ l, l ∈ L ∧ a ∈ l
| []       := ⟨false.elim, λ⟨_, h, _⟩, false.elim h⟩
| (c :: L) := by simp only [join, mem_append, @mem_join L, mem_cons_iff, or_and_distrib_right,
  exists_or_distrib, exists_eq_left]

theorem exists_of_mem_join {a : α} {L : list (list α)} : a ∈ join L → ∃ l, l ∈ L ∧ a ∈ l :=
mem_join.1

theorem mem_join_of_mem {a : α} {L : list (list α)} {l} (lL : l ∈ L) (al : a ∈ l) : a ∈ join L :=
mem_join.2 ⟨l, lL, al⟩

@[simp]
theorem mem_bind {b : β} {l : list α} {f : α → list β} : b ∈ list.bind l f ↔ ∃ a ∈ l, b ∈ f a :=
iff.trans mem_join
  ⟨λ ⟨l', h1, h2⟩, let ⟨a, al, fa⟩ := exists_of_mem_map h1 in ⟨a, al, fa.symm ▸ h2⟩,
  λ ⟨a, al, bfa⟩, ⟨f a, mem_map_of_mem _ al, bfa⟩⟩

theorem exists_of_mem_bind {b : β} {l : list α} {f : α → list β} :
  b ∈ list.bind l f → ∃ a ∈ l, b ∈ f a :=
mem_bind.1

theorem mem_bind_of_mem {b : β} {l : list α} {f : α → list β} {a} (al : a ∈ l) (h : b ∈ f a) :
  b ∈ list.bind l f :=
mem_bind.2 ⟨a, al, h⟩

lemma bind_map {g : α → list β} {f : β → γ} :
  ∀(l : list α), list.map f (l.bind g) = l.bind (λa, (g a).map f)
| [] := rfl
| (a::l) := by simp only [cons_bind, map_append, bind_map l]

lemma map_bind (g : β → list γ) (f : α → β) :
  ∀ l : list α, (list.map f l).bind g = l.bind (λ a, g (f a))
| [] := rfl
| (a::l) := by simp only [cons_bind, map_cons, map_bind l]

/-- If each element of a list can be lifted to some type, then the whole list can be lifted to this
type. -/
instance [h : can_lift α β] : can_lift (list α) (list β) :=
{ coe := list.map h.coe,
  cond := λ l, ∀ x ∈ l, can_lift.cond β x,
  prf  := λ l H,
    begin
      induction l with a l ihl, { exact ⟨[], rfl⟩ },
      rcases ihl (λ x hx, H x (or.inr hx)) with ⟨l, rfl⟩,
      rcases can_lift.prf a (H a (or.inl rfl)) with ⟨a, rfl⟩,
      exact ⟨a :: l, rfl⟩
    end}

/-! ### length -/

theorem length_eq_zero {l : list α} : length l = 0 ↔ l = [] :=
⟨eq_nil_of_length_eq_zero, λ h, h.symm ▸ rfl⟩

@[simp] lemma length_singleton (a : α) : length [a] = 1 := rfl

theorem length_pos_of_mem {a : α} : ∀ {l : list α}, a ∈ l → 0 < length l
| (b::l) _ := zero_lt_succ _

theorem exists_mem_of_length_pos : ∀ {l : list α}, 0 < length l → ∃ a, a ∈ l
| (b::l) _ := ⟨b, mem_cons_self _ _⟩

theorem length_pos_iff_exists_mem {l : list α} : 0 < length l ↔ ∃ a, a ∈ l :=
⟨exists_mem_of_length_pos, λ ⟨a, h⟩, length_pos_of_mem h⟩

theorem ne_nil_of_length_pos {l : list α} : 0 < length l → l ≠ [] :=
λ h1 h2, lt_irrefl 0 ((length_eq_zero.2 h2).subst h1)

theorem length_pos_of_ne_nil {l : list α} : l ≠ [] → 0 < length l :=
λ h, pos_iff_ne_zero.2 $ λ h0, h $ length_eq_zero.1 h0

theorem length_pos_iff_ne_nil {l : list α} : 0 < length l ↔ l ≠ [] :=
⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

lemma exists_mem_of_ne_nil (l : list α) (h : l ≠ []) : ∃ x, x ∈ l :=
exists_mem_of_length_pos (length_pos_of_ne_nil h)

theorem length_eq_one {l : list α} : length l = 1 ↔ ∃ a, l = [a] :=
⟨match l with [a], _ := ⟨a, rfl⟩ end, λ ⟨a, e⟩, e.symm ▸ rfl⟩

lemma exists_of_length_succ {n} :
  ∀ l : list α, l.length = n + 1 → ∃ h t, l = h :: t
| [] H := absurd H.symm $ succ_ne_zero n
| (h :: t) H := ⟨h, t, rfl⟩

@[simp] lemma length_injective_iff : injective (list.length : list α → ℕ) ↔ subsingleton α :=
begin
  split,
  { intro h, refine ⟨λ x y, _⟩, suffices : [x] = [y], { simpa using this }, apply h, refl },
  { intros hα l1 l2 hl, induction l1 generalizing l2; cases l2,
    { refl }, { cases hl }, { cases hl },
    congr, exactI subsingleton.elim _ _, apply l1_ih, simpa using hl }
end

@[simp] lemma length_injective [subsingleton α] : injective (length : list α → ℕ) :=
length_injective_iff.mpr $ by apply_instance

lemma length_eq_two {l : list α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
⟨match l with [a, b], _ := ⟨a, b, rfl⟩ end, λ ⟨a, b, e⟩, e.symm ▸ rfl⟩

lemma length_eq_three {l : list α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
⟨match l with [a, b, c], _ := ⟨a, b, c, rfl⟩ end, λ ⟨a, b, c, e⟩, e.symm ▸ rfl⟩

/-! ### set-theoretic notation of lists -/

lemma empty_eq : (∅ : list α) = [] := by refl
lemma singleton_eq (x : α) : ({x} : list α) = [x] := rfl
lemma insert_neg [decidable_eq α] {x : α} {l : list α} (h : x ∉ l) :
  has_insert.insert x l = x :: l :=
if_neg h
lemma insert_pos [decidable_eq α] {x : α} {l : list α} (h : x ∈ l) :
  has_insert.insert x l = l :=
if_pos h
lemma doubleton_eq [decidable_eq α] {x y : α} (h : x ≠ y) : ({x, y} : list α) = [x, y] :=
by { rw [insert_neg, singleton_eq], rwa [singleton_eq, mem_singleton] }

/-! ### bounded quantifiers over lists -/

theorem forall_mem_nil (p : α → Prop) : ∀ x ∈ @nil α, p x.

theorem forall_mem_cons : ∀ {p : α → Prop} {a : α} {l : list α},
  (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x :=
ball_cons

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : list α}
    (h : ∀ x ∈ a :: l, p x) :
  ∀ x ∈ l, p x :=
(forall_mem_cons.1 h).2

theorem forall_mem_singleton {p : α → Prop} {a : α} : (∀ x ∈ [a], p x) ↔ p a :=
by simp only [mem_singleton, forall_eq]

theorem forall_mem_append {p : α → Prop} {l₁ l₂ : list α} :
  (∀ x ∈ l₁ ++ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
by simp only [mem_append, or_imp_distrib, forall_and_distrib]

theorem not_exists_mem_nil (p : α → Prop) : ¬ ∃ x ∈ @nil α, p x.

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : list α) (h : p a) :
  ∃ x ∈ a :: l, p x :=
bex.intro a (mem_cons_self _ _) h

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ l, p x) :
  ∃ x ∈ a :: l, p x :=
bex.elim h (λ x xl px, bex.intro x (mem_cons_of_mem _ xl) px)

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : list α} (h : ∃ x ∈ a :: l, p x) :
  p a ∨ ∃ x ∈ l, p x :=
bex.elim h (λ x xal px,
  or.elim (eq_or_mem_of_mem_cons xal)
    (assume : x = a, begin rw ←this, left, exact px end)
    (assume : x ∈ l, or.inr (bex.intro x this px)))

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : list α) :
  (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
iff.intro or_exists_of_exists_mem_cons
  (assume h, or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists)

/-! ### list subset -/

theorem subset_def {l₁ l₂ : list α} : l₁ ⊆ l₂ ↔ ∀ ⦃a : α⦄, a ∈ l₁ → a ∈ l₂ := iff.rfl

theorem subset_append_of_subset_left (l l₁ l₂ : list α) : l ⊆ l₁ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_left _ _

theorem subset_append_of_subset_right (l l₁ l₂ : list α) : l ⊆ l₂ → l ⊆ l₁++l₂ :=
λ s, subset.trans s $ subset_append_right _ _

@[simp] theorem cons_subset {a : α} {l m : list α} :
  a::l ⊆ m ↔ a ∈ m ∧ l ⊆ m :=
by simp only [subset_def, mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq]

theorem cons_subset_of_subset_of_mem {a : α} {l m : list α}
  (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : list α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
  l₁ ++ l₂ ⊆ l :=
λ a h, (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

@[simp] theorem append_subset_iff {l₁ l₂ l : list α} :
  l₁ ++ l₂ ⊆ l ↔ l₁ ⊆ l ∧ l₂ ⊆ l :=
begin
  split,
  { intro h, simp only [subset_def] at *, split; intros; simp* },
  { rintro ⟨h1, h2⟩, apply append_subset_of_subset_of_subset h1 h2 }
end

theorem eq_nil_of_subset_nil : ∀ {l : list α}, l ⊆ [] → l = []
| []     s := rfl
| (a::l) s := false.elim $ s $ mem_cons_self a l

theorem eq_nil_iff_forall_not_mem {l : list α} : l = [] ↔ ∀ a, a ∉ l :=
show l = [] ↔ l ⊆ [], from ⟨λ e, e ▸ subset.refl _, eq_nil_of_subset_nil⟩

theorem map_subset {l₁ l₂ : list α} (f : α → β) (H : l₁ ⊆ l₂) : map f l₁ ⊆ map f l₂ :=
λ x, by simp only [mem_map, not_and, exists_imp_distrib, and_imp]; exact λ a h e, ⟨a, H h, e⟩

theorem map_subset_iff {l₁ l₂ : list α} (f : α → β) (h : injective f) :
  map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ :=
begin
  refine ⟨_, map_subset f⟩, intros h2 x hx,
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩,
  cases h hxx', exact hx'
end

/-! ### append -/

lemma append_eq_has_append {L₁ L₂ : list α} : list.append L₁ L₂ = L₁ ++ L₂ := rfl

@[simp] lemma singleton_append {x : α} {l : list α} : [x] ++ l = x :: l := rfl

theorem append_ne_nil_of_ne_nil_left (s t : list α) : s ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

theorem append_ne_nil_of_ne_nil_right (s t : list α) : t ≠ [] → s ++ t ≠ [] :=
by induction s; intros; contradiction

@[simp] lemma append_eq_nil {p q : list α} : (p ++ q) = [] ↔ p = [] ∧ q = [] :=
by cases p; simp only [nil_append, cons_append, eq_self_iff_true, true_and, false_and]

@[simp] lemma nil_eq_append_iff {a b : list α} : [] = a ++ b ↔ a = [] ∧ b = [] :=
by rw [eq_comm, append_eq_nil]

lemma append_eq_cons_iff {a b c : list α} {x : α} :
  a ++ b = x :: c ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) :=
by cases a; simp only [and_assoc, @eq_comm _ c, nil_append, cons_append, eq_self_iff_true,
  true_and, false_and, exists_false, false_or, or_false, exists_and_distrib_left, exists_eq_left']

lemma cons_eq_append_iff {a b c : list α} {x : α} :
  (x :: c : list α) = a ++ b ↔ (a = [] ∧ b = x :: c) ∨ (∃a', a = x :: a' ∧ c = a' ++ b) :=
by rw [eq_comm, append_eq_cons_iff]

lemma append_eq_append_iff {a b c d : list α} :
  a ++ b = c ++ d ↔ (∃a', c = a ++ a' ∧ b = a' ++ d) ∨ (∃c', a = c ++ c' ∧ d = c' ++ b) :=
begin
  induction a generalizing c,
  case nil { rw nil_append, split,
    { rintro rfl, left, exact ⟨_, rfl, rfl⟩ },
    { rintro (⟨a', rfl, rfl⟩ | ⟨a', H, rfl⟩), {refl}, {rw [← append_assoc, ← H], refl} } },
  case cons : a as ih
  { cases c,
    { simp only [cons_append, nil_append, false_and, exists_false, false_or, exists_eq_left'],
      exact eq_comm },
    { simp only [cons_append, @eq_comm _ a, ih, and_assoc, and_or_distrib_left,
        exists_and_distrib_left] } }
end

@[simp] theorem take_append_drop : ∀ (n : ℕ) (l : list α), take n l ++ drop n l = l
| 0        a         := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := congr_arg (cons x) $ take_append_drop n xs

-- TODO(Leo): cleanup proof after arith dec proc
theorem append_inj :
  ∀ {s₁ s₂ t₁ t₂ : list α}, s₁ ++ t₁ = s₂ ++ t₂ → length s₁ = length s₂ → s₁ = s₂ ∧ t₁ = t₂
| []      []      t₁ t₂ h hl := ⟨rfl, h⟩
| (a::s₁) []      t₁ t₂ h hl := list.no_confusion $ eq_nil_of_length_eq_zero hl
| []      (b::s₂) t₁ t₂ h hl := list.no_confusion $ eq_nil_of_length_eq_zero hl.symm
| (a::s₁) (b::s₂) t₁ t₂ h hl := list.no_confusion h $ λab hap,
  let ⟨e1, e2⟩ := @append_inj s₁ s₂ t₁ t₂ hap (succ.inj hl) in
  by rw [ab, e1, e2]; exact ⟨rfl, rfl⟩

theorem append_inj_right {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length s₁ = length s₂) : t₁ = t₂ :=
(append_inj h hl).right

theorem append_inj_left {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length s₁ = length s₂) : s₁ = s₂ :=
(append_inj h hl).left

theorem append_inj' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂) (hl : length t₁ = length t₂) :
  s₁ = s₂ ∧ t₁ = t₂ :=
append_inj h $ @nat.add_right_cancel _ (length t₁) _ $
let hap := congr_arg length h in by simp only [length_append] at hap; rwa [← hl] at hap

theorem append_inj_right' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length t₁ = length t₂) : t₁ = t₂ :=
(append_inj' h hl).right

theorem append_inj_left' {s₁ s₂ t₁ t₂ : list α} (h : s₁ ++ t₁ = s₂ ++ t₂)
  (hl : length t₁ = length t₂) : s₁ = s₂ :=
(append_inj' h hl).left

theorem append_left_cancel {s t₁ t₂ : list α} (h : s ++ t₁ = s ++ t₂) : t₁ = t₂ :=
append_inj_right h rfl

theorem append_right_cancel {s₁ s₂ t : list α} (h : s₁ ++ t = s₂ ++ t) : s₁ = s₂ :=
append_inj_left' h rfl

theorem append_right_injective (s : list α) : function.injective (λ t, s ++ t) :=
λ t₁ t₂, append_left_cancel

theorem append_right_inj {t₁ t₂ : list α} (s) : s ++ t₁ = s ++ t₂ ↔ t₁ = t₂ :=
(append_right_injective s).eq_iff

theorem append_left_injective (t : list α) : function.injective (λ s, s ++ t) :=
λ s₁ s₂, append_right_cancel

theorem append_left_inj {s₁ s₂ : list α} (t) : s₁ ++ t = s₂ ++ t ↔ s₁ = s₂ :=
(append_left_injective t).eq_iff

theorem map_eq_append_split {f : α → β} {l : list α} {s₁ s₂ : list β}
  (h : map f l = s₁ ++ s₂) : ∃ l₁ l₂, l = l₁ ++ l₂ ∧ map f l₁ = s₁ ∧ map f l₂ = s₂ :=
begin
  have := h, rw [← take_append_drop (length s₁) l] at this ⊢,
  rw map_append at this,
  refine ⟨_, _, rfl, append_inj this _⟩,
  rw [length_map, length_take, min_eq_left],
  rw [← length_map f l, h, length_append],
  apply nat.le_add_right
end

/-! ### repeat -/

@[simp] theorem repeat_succ (a : α) (n) : repeat a (n + 1) = a :: repeat a n := rfl

theorem mem_repeat {a b : α} : ∀ {n}, b ∈ repeat a n ↔ n ≠ 0 ∧ b = a
| 0 := by simp
| (n + 1) := by simp [mem_repeat]

theorem eq_of_mem_repeat {a b : α} {n} (h :  b ∈ repeat a n) : b = a :=
(mem_repeat.1 h).2

theorem eq_repeat_of_mem {a : α} : ∀ {l : list α}, (∀ b ∈ l, b = a) → l = repeat a l.length
| []     H := rfl
| (b::l) H := by cases forall_mem_cons.1 H with H₁ H₂;
  unfold length repeat; congr; [exact H₁, exact eq_repeat_of_mem H₂]

theorem eq_repeat' {a : α} {l : list α} : l = repeat a l.length ↔ ∀ b ∈ l, b = a :=
⟨λ h, h.symm ▸ λ b, eq_of_mem_repeat, eq_repeat_of_mem⟩

theorem eq_repeat {a : α} {n} {l : list α} : l = repeat a n ↔ length l = n ∧ ∀ b ∈ l, b = a :=
⟨λ h, h.symm ▸ ⟨length_repeat _ _, λ b, eq_of_mem_repeat⟩,
 λ ⟨e, al⟩, e ▸ eq_repeat_of_mem al⟩

theorem repeat_add (a : α) (m n) : repeat a (m + n) = repeat a m ++ repeat a n :=
by induction m; simp only [*, zero_add, succ_add, repeat]; split; refl

theorem repeat_subset_singleton (a : α) (n) : repeat a n ⊆ [a] :=
λ b h, mem_singleton.2 (eq_of_mem_repeat h)

@[simp] theorem map_const (l : list α) (b : β) : map (function.const α b) l = repeat b l.length :=
by induction l; [refl, simp only [*, map]]; split; refl

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) :
  b₁ = b₂ :=
by rw map_const at h; exact eq_of_mem_repeat h

@[simp] theorem map_repeat (f : α → β) (a : α) (n) : map f (repeat a n) = repeat (f a) n :=
by induction n; [refl, simp only [*, repeat, map]]; split; refl

@[simp] theorem tail_repeat (a : α) (n) : tail (repeat a n) = repeat a n.pred :=
by cases n; refl

@[simp] theorem join_repeat_nil (n : ℕ) : join (repeat [] n) = @nil α :=
by induction n; [refl, simp only [*, repeat, join, append_nil]]

lemma repeat_left_injective {n : ℕ} (hn : n ≠ 0) :
  function.injective (λ a : α, repeat a n) :=
λ a b h, (eq_repeat.1 h).2 _ $ mem_repeat.2 ⟨hn, rfl⟩

lemma repeat_left_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
  repeat a n = repeat b n ↔ a = b :=
(repeat_left_injective hn).eq_iff

@[simp] lemma repeat_left_inj' {a b : α} :
  ∀ {n}, repeat a n = repeat b n ↔ n = 0 ∨ a = b
| 0 := by simp
| (n + 1) := (repeat_left_inj n.succ_ne_zero).trans $ by simp only [n.succ_ne_zero, false_or]

lemma repeat_right_injective (a : α) : function.injective (repeat a) :=
function.left_inverse.injective (length_repeat a)

@[simp] lemma repeat_right_inj {a : α} {n m : ℕ} :
  repeat a n = repeat a m ↔ n = m :=
(repeat_right_injective a).eq_iff

/-! ### pure -/

@[simp] theorem mem_pure {α} (x y : α) :
  x ∈ (pure y : list α) ↔ x = y := by simp! [pure,list.ret]

/-! ### bind -/

@[simp] theorem bind_eq_bind {α β} (f : α → list β) (l : list α) :
  l >>= f = l.bind f := rfl

-- TODO: duplicate of a lemma in core
theorem bind_append (f : α → list β) (l₁ l₂ : list α) :
  (l₁ ++ l₂).bind f = l₁.bind f ++ l₂.bind f :=
append_bind _ _ _

@[simp] theorem bind_singleton (f : α → list β) (x : α) : [x].bind f = f x :=
append_nil (f x)

@[simp] theorem bind_singleton' (l : list α) : l.bind (λ x, [x]) = l := bind_pure l

theorem map_eq_bind {α β} (f : α → β) (l : list α) : map f l = l.bind (λ x, [f x]) :=
by { transitivity, rw [← bind_singleton' l, bind_map], refl }

theorem bind_assoc {α β} (l : list α) (f : α → list β) (g : β → list γ) :
  (l.bind f).bind g = l.bind (λ x, (f x).bind g) :=
by induction l; simp *

/-! ### concat -/

theorem concat_nil (a : α) : concat [] a = [a] := rfl

theorem concat_cons (a b : α) (l : list α) : concat (a :: l) b = a :: concat l b := rfl

@[simp] theorem concat_eq_append (a : α) (l : list α) : concat l a = l ++ [a] :=
by induction l; simp only [*, concat]; split; refl

theorem init_eq_of_concat_eq {a : α} {l₁ l₂ : list α} : concat l₁ a = concat l₂ a → l₁ = l₂ :=
begin
  intro h,
  rw [concat_eq_append, concat_eq_append] at h,
  exact append_right_cancel h
end

theorem last_eq_of_concat_eq {a b : α} {l : list α} : concat l a = concat l b → a = b :=
begin
  intro h,
  rw [concat_eq_append, concat_eq_append] at h,
  exact head_eq_of_cons_eq (append_left_cancel h)
end

theorem concat_ne_nil (a : α) (l : list α) : concat l a ≠ [] :=
by simp

theorem concat_append (a : α) (l₁ l₂ : list α) : concat l₁ a ++ l₂ = l₁ ++ a :: l₂ :=
by simp

theorem length_concat (a : α) (l : list α) : length (concat l a) = succ (length l) :=
by simp only [concat_eq_append, length_append, length]

theorem append_concat (a : α) (l₁ l₂ : list α) : l₁ ++ concat l₂ a = concat (l₁ ++ l₂) a :=
by simp

/-! ### reverse -/

@[simp] theorem reverse_nil : reverse (@nil α) = [] := rfl

local attribute [simp] reverse_core

@[simp] theorem reverse_cons (a : α) (l : list α) : reverse (a::l) = reverse l ++ [a] :=
have aux : ∀ l₁ l₂, reverse_core l₁ l₂ ++ [a] = reverse_core l₁ (l₂ ++ [a]),
by intro l₁; induction l₁; intros; [refl, simp only [*, reverse_core, cons_append]],
(aux l nil).symm

theorem reverse_core_eq (l₁ l₂ : list α) : reverse_core l₁ l₂ = reverse l₁ ++ l₂ :=
by induction l₁ generalizing l₂; [refl, simp only [*, reverse_core, reverse_cons, append_assoc]];
  refl

theorem reverse_cons' (a : α) (l : list α) : reverse (a::l) = concat (reverse l) a :=
by simp only [reverse_cons, concat_eq_append]

@[simp] theorem reverse_singleton (a : α) : reverse [a] = [a] := rfl

@[simp] theorem reverse_append (s t : list α) : reverse (s ++ t) = (reverse t) ++ (reverse s) :=
by induction s; [rw [nil_append, reverse_nil, append_nil],
simp only [*, cons_append, reverse_cons, append_assoc]]

theorem reverse_concat (l : list α) (a : α) : reverse (concat l a) = a :: reverse l :=
by rw [concat_eq_append, reverse_append, reverse_singleton, singleton_append]

@[simp] theorem reverse_reverse (l : list α) : reverse (reverse l) = l :=
by induction l; [refl, simp only [*, reverse_cons, reverse_append]]; refl

@[simp] theorem reverse_involutive : involutive (@reverse α) :=
λ l, reverse_reverse l

@[simp] theorem reverse_injective : injective (@reverse α) :=
reverse_involutive.injective

@[simp] theorem reverse_inj {l₁ l₂ : list α} : reverse l₁ = reverse l₂ ↔ l₁ = l₂ :=
reverse_injective.eq_iff

lemma reverse_eq_iff {l l' : list α} :
  l.reverse = l' ↔ l = l'.reverse :=
reverse_involutive.eq_iff

@[simp] theorem reverse_eq_nil {l : list α} : reverse l = [] ↔ l = [] :=
@reverse_inj _ l []

theorem concat_eq_reverse_cons (a : α) (l : list α) : concat l a = reverse (a :: reverse l) :=
by simp only [concat_eq_append, reverse_cons, reverse_reverse]

@[simp] theorem length_reverse (l : list α) : length (reverse l) = length l :=
by induction l; [refl, simp only [*, reverse_cons, length_append, length]]

@[simp] theorem map_reverse (f : α → β) (l : list α) : map f (reverse l) = reverse (map f l) :=
by induction l; [refl, simp only [*, map, reverse_cons, map_append]]

theorem map_reverse_core (f : α → β) (l₁ l₂ : list α) :
  map f (reverse_core l₁ l₂) = reverse_core (map f l₁) (map f l₂) :=
by simp only [reverse_core_eq, map_append, map_reverse]

@[simp] theorem mem_reverse {a : α} {l : list α} : a ∈ reverse l ↔ a ∈ l :=
by induction l; [refl, simp only [*, reverse_cons, mem_append, mem_singleton, mem_cons_iff,
  not_mem_nil, false_or, or_false, or_comm]]

@[simp] theorem reverse_repeat (a : α) (n) : reverse (repeat a n) = repeat a n :=
eq_repeat.2 ⟨by simp only [length_reverse, length_repeat],
  λ b h, eq_of_mem_repeat (mem_reverse.1 h)⟩

/-! ### empty -/

attribute [simp] list.empty

lemma empty_iff_eq_nil {l : list α} : l.empty ↔ l = [] :=
list.cases_on l (by simp) (by simp)

/-! ### init -/

@[simp] theorem length_init : ∀ (l : list α), length (init l) = length l - 1
| [] := rfl
| [a] := rfl
| (a :: b :: l) :=
begin
  rw init,
  simp only [add_left_inj, length, succ_add_sub_one],
  exact length_init (b :: l)
end

/-! ### last -/

@[simp] theorem last_cons {a : α} {l : list α} :
  ∀ (h₁ : a :: l ≠ nil) (h₂ : l ≠ nil), last (a :: l) h₁ = last l h₂ :=
by {induction l; intros, contradiction, reflexivity}

@[simp] theorem last_append {a : α} (l : list α) (h : l ++ [a] ≠ []) : last (l ++ [a]) h = a :=
by induction l;
  [refl, simp only [cons_append, last_cons _ (λ H, cons_ne_nil _ _ (append_eq_nil.1 H).2), *]]

theorem last_concat {a : α} (l : list α) (h : concat l a ≠ []) : last (concat l a) h = a :=
by simp only [concat_eq_append, last_append]

@[simp] theorem last_singleton (a : α) (h : [a] ≠ []) : last [a] h = a := rfl

@[simp] theorem last_cons_cons (a₁ a₂ : α) (l : list α) (h : a₁::a₂::l ≠ []) :
  last (a₁::a₂::l) h = last (a₂::l) (cons_ne_nil a₂ l) := rfl

theorem init_append_last : ∀ {l : list α} (h : l ≠ []), init l ++ [last l h] = l
| [] h := absurd rfl h
| [a] h := rfl
| (a::b::l) h :=
begin
  rw [init, cons_append, last_cons (cons_ne_nil _ _) (cons_ne_nil _ _)],
  congr,
  exact init_append_last (cons_ne_nil b l)
end

theorem last_congr {l₁ l₂ : list α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
  last l₁ h₁ = last l₂ h₂ :=
by subst l₁

theorem last_mem : ∀ {l : list α} (h : l ≠ []), last l h ∈ l
| [] h := absurd rfl h
| [a] h := or.inl rfl
| (a::b::l) h := or.inr $ by { rw [last_cons_cons], exact last_mem (cons_ne_nil b l) }

lemma last_repeat_succ (a m : ℕ) :
  (repeat a m.succ).last (ne_nil_of_length_eq_succ
  (show (repeat a m.succ).length = m.succ, by rw length_repeat)) = a :=
begin
  induction m with k IH,
  { simp },
  { simpa only [repeat_succ, last] }
end

/-! ### last' -/

@[simp] theorem last'_is_none :
  ∀ {l : list α}, (last' l).is_none ↔ l = []
| [] := by simp
| [a] := by simp
| (a::b::l) := by simp [@last'_is_none (b::l)]

@[simp] theorem last'_is_some : ∀ {l : list α}, l.last'.is_some ↔ l ≠ []
| [] := by simp
| [a] := by simp
| (a::b::l) := by simp [@last'_is_some (b::l)]

theorem mem_last'_eq_last : ∀ {l : list α} {x : α}, x ∈ l.last' → ∃ h, x = last l h
| [] x hx := false.elim $ by simpa using hx
| [a] x hx := have a = x, by simpa using hx, this ▸ ⟨cons_ne_nil a [], rfl⟩
| (a::b::l) x hx :=
  begin
    rw last' at hx,
    rcases mem_last'_eq_last hx with ⟨h₁, h₂⟩,
    use cons_ne_nil _ _,
    rwa [last_cons]
  end

theorem last'_eq_last_of_ne_nil : ∀ {l : list α} (h : l ≠ []), l.last' = some (l.last h)
| [] h := (h rfl).elim
| [a] _ := by {unfold last, unfold last'}
| (a::b::l) _ := @last'_eq_last_of_ne_nil (b::l) (cons_ne_nil _ _)

theorem mem_last'_cons {x y : α} : ∀ {l : list α} (h : x ∈ l.last'), x ∈ (y :: l).last'
| [] _ := by contradiction
| (a::l) h := h

theorem mem_of_mem_last' {l : list α} {a : α} (ha : a ∈ l.last') : a ∈ l :=
let ⟨h₁, h₂⟩ := mem_last'_eq_last ha in h₂.symm ▸ last_mem _

theorem init_append_last' : ∀ {l : list α} (a ∈ l.last'), init l ++ [a] = l
| [] a ha := (option.not_mem_none a ha).elim
| [a] _ rfl := rfl
| (a :: b :: l) c hc := by { rw [last'] at hc, rw [init, cons_append, init_append_last' _ hc] }

theorem ilast_eq_last' [inhabited α] : ∀ l : list α, l.ilast = l.last'.iget
| [] := by simp [ilast, arbitrary]
| [a] := rfl
| [a, b] := rfl
| [a, b, c] := rfl
| (a :: b :: c :: l) := by simp [ilast, ilast_eq_last' (c :: l)]

@[simp] theorem last'_append_cons : ∀ (l₁ : list α) (a : α) (l₂ : list α),
  last' (l₁ ++ a :: l₂) = last' (a :: l₂)
| [] a l₂ := rfl
| [b] a l₂ := rfl
| (b::c::l₁) a l₂ := by rw [cons_append, cons_append, last', ← cons_append, last'_append_cons]

@[simp] theorem last'_cons_cons (x y : α) (l : list α) :
  last' (x :: y :: l) = last' (y :: l) := rfl

theorem last'_append_of_ne_nil (l₁ : list α) : ∀ {l₂ : list α} (hl₂ : l₂ ≠ []),
  last' (l₁ ++ l₂) = last' l₂
| [] hl₂ := by contradiction
| (b::l₂) _ := last'_append_cons l₁ b l₂

/-! ### head(') and tail -/

theorem head_eq_head' [inhabited α] (l : list α) : head l = (head' l).iget :=
by cases l; refl

theorem mem_of_mem_head' {x : α} : ∀ {l : list α}, x ∈ l.head' → x ∈ l
| [] h := (option.not_mem_none _ h).elim
| (a::l) h := by { simp only [head', option.mem_def] at h, exact h ▸ or.inl rfl }

@[simp] theorem head_cons [inhabited α] (a : α) (l : list α) : head (a::l) = a := rfl

@[simp] theorem tail_nil : tail (@nil α) = [] := rfl

@[simp] theorem tail_cons (a : α) (l : list α) : tail (a::l) = l := rfl

@[simp] theorem head_append [inhabited α] (t : list α) {s : list α} (h : s ≠ []) :
  head (s ++ t) = head s :=
by {induction s, contradiction, refl}

theorem head'_append {s t : list α} {x : α} (h : x ∈ s.head') :
  x ∈ (s ++ t).head' :=
by { cases s, contradiction, exact h }

theorem tail_append_singleton_of_ne_nil {a : α} {l : list α} (h : l ≠ nil) :
  tail (l ++ [a]) = tail l ++ [a] :=
by { induction l,  contradiction, rw [tail,cons_append,tail], }

theorem cons_head'_tail : ∀ {l : list α} {a : α} (h : a ∈ head' l), a :: tail l = l
| [] a h := by contradiction
| (b::l) a h := by { simp at h, simp [h] }

theorem head_mem_head' [inhabited α] : ∀ {l : list α} (h : l ≠ []), head l ∈ head' l
| [] h := by contradiction
| (a::l) h := rfl

theorem cons_head_tail [inhabited α] {l : list α} (h : l ≠ []) : (head l)::(tail l) = l :=
cons_head'_tail (head_mem_head' h)

lemma head_mem_self [inhabited α] {l : list α} (h : l ≠ nil) : l.head ∈ l :=
begin
  have h' := mem_cons_self l.head l.tail,
  rwa cons_head_tail h at h',
end

@[simp] theorem head'_map (f : α → β) (l) : head' (map f l) = (head' l).map f := by cases l; refl

lemma tail_append_of_ne_nil (l l' : list α) (h : l ≠ []) :
  (l ++ l').tail = l.tail ++ l' :=
begin
  cases l,
  { contradiction },
  { simp }
end

@[simp]
lemma nth_le_tail (l : list α) (i) (h : i < l.tail.length)
  (h' : i + 1 < l.length := by simpa [←lt_tsub_iff_right] using h) :
  l.tail.nth_le i h = l.nth_le (i + 1) h' :=
begin
  cases l,
  { cases h, },
  { simpa }
end

/-! ### Induction from the right -/

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_eliminator] def reverse_rec_on {C : list α → Sort*}
  (l : list α) (H0 : C [])
  (H1 : ∀ (l : list α) (a : α), C l → C (l ++ [a])) : C l :=
begin
  rw ← reverse_reverse l,
  induction reverse l,
  { exact H0 },
  { rw reverse_cons, exact H1 _ _ ih }
end

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
def bidirectional_rec {C : list α → Sort*}
    (H0 : C []) (H1 : ∀ (a : α), C [a])
    (Hn : ∀ (a : α) (l : list α) (b : α), C l → C (a :: (l ++ [b]))) : ∀ l, C l
| [] := H0
| [a] := H1 a
| (a :: b :: l) :=
let l' := init (b :: l), b' := last (b :: l) (cons_ne_nil _ _) in
have length l' < length (a :: b :: l), by { change _ < length l + 2, simp },
begin
  rw ←init_append_last (cons_ne_nil b l),
  have : C l', from bidirectional_rec l',
  exact Hn a l' b' ‹C l'›
end
using_well_founded { rel_tac := λ _ _, `[exact ⟨_, measure_wf list.length⟩] }

/-- Like `bidirectional_rec`, but with the list parameter placed first. -/
@[elab_as_eliminator] def bidirectional_rec_on {C : list α → Sort*}
    (l : list α) (H0 : C []) (H1 : ∀ (a : α), C [a])
    (Hn : ∀ (a : α) (l : list α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
bidirectional_rec H0 H1 Hn l

/-! ### sublists -/

@[simp] theorem nil_sublist : Π (l : list α), [] <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons _ _ a (nil_sublist l)

@[refl, simp] theorem sublist.refl : Π (l : list α), l <+ l
| []       := sublist.slnil
| (a :: l) := sublist.cons2 _ _ a (sublist.refl l)

@[trans] theorem sublist.trans {l₁ l₂ l₃ : list α} (h₁ : l₁ <+ l₂) (h₂ : l₂ <+ l₃) : l₁ <+ l₃ :=
sublist.rec_on h₂ (λ_ s, s)
  (λl₂ l₃ a h₂ IH l₁ h₁, sublist.cons _ _ _ (IH l₁ h₁))
  (λl₂ l₃ a h₂ IH l₁ h₁, @sublist.cases_on _ (λl₁ l₂', l₂' = a :: l₂ → l₁ <+ a :: l₃) _ _ h₁
    (λ_, nil_sublist _)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ :=
      sublist.cons _ _ _ (IH _ h₁) end)
    (λl₁ l₂' a' h₁' e, match a', l₂', e, h₁' with ._, ._, rfl, h₁ :=
      sublist.cons2 _ _ _ (IH _ h₁) end) rfl)
  l₁ h₁

@[simp] theorem sublist_cons (a : α) (l : list α) : l <+ a::l :=
sublist.cons _ _ _ (sublist.refl l)

theorem sublist_of_cons_sublist {a : α} {l₁ l₂ : list α} : a::l₁ <+ l₂ → l₁ <+ l₂ :=
sublist.trans (sublist_cons a l₁)

theorem sublist.cons_cons {l₁ l₂ : list α} (a : α) (s : l₁ <+ l₂) : a::l₁ <+ a::l₂ :=
sublist.cons2 _ _ _ s

@[simp] theorem sublist_append_left : Π (l₁ l₂ : list α), l₁ <+ l₁++l₂
| []      l₂ := nil_sublist _
| (a::l₁) l₂ := (sublist_append_left l₁ l₂).cons_cons _

@[simp] theorem sublist_append_right : Π (l₁ l₂ : list α), l₂ <+ l₁++l₂
| []      l₂ := sublist.refl _
| (a::l₁) l₂ := sublist.cons _ _ _ (sublist_append_right l₁ l₂)

theorem sublist_cons_of_sublist (a : α) {l₁ l₂ : list α} : l₁ <+ l₂ → l₁ <+ a::l₂ :=
sublist.cons _ _ _

theorem sublist_append_of_sublist_left {l l₁ l₂ : list α} (s : l <+ l₁) : l <+ l₁++l₂ :=
s.trans $ sublist_append_left _ _

theorem sublist_append_of_sublist_right {l l₁ l₂ : list α} (s : l <+ l₂) : l <+ l₁++l₂ :=
s.trans $ sublist_append_right _ _

theorem sublist_of_cons_sublist_cons {l₁ l₂ : list α} : ∀ {a : α}, a::l₁ <+ a::l₂ → l₁ <+ l₂
| ._ (sublist.cons  ._ ._ a s) := sublist_of_cons_sublist s
| ._ (sublist.cons2 ._ ._ a s) := s

theorem cons_sublist_cons_iff {l₁ l₂ : list α} {a : α} : a::l₁ <+ a::l₂ ↔ l₁ <+ l₂ :=
⟨sublist_of_cons_sublist_cons, sublist.cons_cons _⟩

@[simp] theorem append_sublist_append_left {l₁ l₂ : list α} : ∀ l, l++l₁ <+ l++l₂ ↔ l₁ <+ l₂
| []     := iff.rfl
| (a::l) := cons_sublist_cons_iff.trans (append_sublist_append_left l)

theorem sublist.append_right {l₁ l₂ : list α} (h : l₁ <+ l₂) (l) : l₁++l <+ l₂++l :=
begin
  induction h with _ _ a _ ih _ _ a _ ih,
  { refl },
  { apply sublist_cons_of_sublist a ih },
  { apply ih.cons_cons a }
end

theorem sublist_or_mem_of_sublist {l l₁ l₂ : list α} {a : α} (h : l <+ l₁ ++ a::l₂) :
  l <+ l₁ ++ l₂ ∨ a ∈ l :=
begin
  induction l₁ with b l₁ IH generalizing l,
  { cases h, { left, exact ‹l <+ l₂› }, { right, apply mem_cons_self } },
  { cases h with _ _ _ h _ _ _ h,
    { exact or.imp_left (sublist_cons_of_sublist _) (IH h) },
    { exact (IH h).imp (sublist.cons_cons _) (mem_cons_of_mem _) } }
end

theorem sublist.reverse {l₁ l₂ : list α} (h : l₁ <+ l₂) : l₁.reverse <+ l₂.reverse :=
begin
  induction h with _ _ _ _ ih _ _ a _ ih, {refl},
  { rw reverse_cons, exact sublist_append_of_sublist_left ih },
  { rw [reverse_cons, reverse_cons], exact ih.append_right [a] }
end

@[simp] theorem reverse_sublist_iff {l₁ l₂ : list α} : l₁.reverse <+ l₂.reverse ↔ l₁ <+ l₂ :=
⟨λ h, l₁.reverse_reverse ▸ l₂.reverse_reverse ▸ h.reverse, sublist.reverse⟩

@[simp] theorem append_sublist_append_right {l₁ l₂ : list α} (l) : l₁++l <+ l₂++l ↔ l₁ <+ l₂ :=
⟨λ h, by simpa only [reverse_append, append_sublist_append_left, reverse_sublist_iff]
  using h.reverse,
 λ h, h.append_right l⟩

theorem sublist.append {l₁ l₂ r₁ r₂ : list α}
  (hl : l₁ <+ l₂) (hr : r₁ <+ r₂) : l₁ ++ r₁ <+ l₂ ++ r₂ :=
(hl.append_right _).trans ((append_sublist_append_left _).2 hr)

theorem sublist.subset : Π {l₁ l₂ : list α}, l₁ <+ l₂ → l₁ ⊆ l₂
| ._ ._ sublist.slnil             b h := h
| ._ ._ (sublist.cons  l₁ l₂ a s) b h := mem_cons_of_mem _ (sublist.subset s h)
| ._ ._ (sublist.cons2 l₁ l₂ a s) b h :=
  match eq_or_mem_of_mem_cons h with
  | or.inl h := h ▸ mem_cons_self _ _
  | or.inr h := mem_cons_of_mem _ (sublist.subset s h)
  end

@[simp] theorem singleton_sublist {a : α} {l} : [a] <+ l ↔ a ∈ l :=
⟨λ h, h.subset (mem_singleton_self _), λ h,
let ⟨s, t, e⟩ := mem_split h in e.symm ▸
  ((nil_sublist _).cons_cons _ ).trans (sublist_append_right _ _)⟩

theorem eq_nil_of_sublist_nil {l : list α} (s : l <+ []) : l = [] :=
eq_nil_of_subset_nil $ s.subset

@[simp] theorem sublist_nil_iff_eq_nil {l : list α} : l <+ [] ↔ l = [] :=
⟨eq_nil_of_sublist_nil, λ H, H ▸ sublist.refl _⟩

@[simp] theorem repeat_sublist_repeat (a : α) {m n} : repeat a m <+ repeat a n ↔ m ≤ n :=
⟨λ h, by simpa only [length_repeat] using length_le_of_sublist h,
 λ h, by induction h; [refl, simp only [*, repeat_succ, sublist.cons]] ⟩

theorem eq_of_sublist_of_length_eq : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → length l₁ = length l₂ → l₁ = l₂
| ._ ._ sublist.slnil             h := rfl
| ._ ._ (sublist.cons  l₁ l₂ a s) h :=
  absurd (length_le_of_sublist s) $ not_le_of_gt $ by rw h; apply lt_succ_self
| ._ ._ (sublist.cons2 l₁ l₂ a s) h :=
  by rw [length, length] at h; injection h with h; rw eq_of_sublist_of_length_eq s h

theorem eq_of_sublist_of_length_le {l₁ l₂ : list α} (s : l₁ <+ l₂) (h : length l₂ ≤ length l₁) :
  l₁ = l₂ :=
eq_of_sublist_of_length_eq s (le_antisymm (length_le_of_sublist s) h)

theorem sublist.antisymm {l₁ l₂ : list α} (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
eq_of_sublist_of_length_le s₁ (length_le_of_sublist s₂)

instance decidable_sublist [decidable_eq α] : ∀ (l₁ l₂ : list α), decidable (l₁ <+ l₂)
| []      l₂      := is_true $ nil_sublist _
| (a::l₁) []      := is_false $ λh, list.no_confusion $ eq_nil_of_sublist_nil h
| (a::l₁) (b::l₂) :=
  if h : a = b then
    decidable_of_decidable_of_iff (decidable_sublist l₁ l₂) $
      by rw [← h]; exact ⟨sublist.cons_cons _, sublist_of_cons_sublist_cons⟩
  else decidable_of_decidable_of_iff (decidable_sublist (a::l₁) l₂)
    ⟨sublist_cons_of_sublist _, λs, match a, l₁, s, h with
    | a, l₁, sublist.cons ._ ._ ._ s', h := s'
    | ._, ._, sublist.cons2 t ._ ._ s', h := absurd rfl h
    end⟩

/-! ### index_of -/

section index_of
variable [decidable_eq α]

@[simp] theorem index_of_nil (a : α) : index_of a [] = 0 := rfl

theorem index_of_cons (a b : α) (l : list α) :
  index_of a (b::l) = if a = b then 0 else succ (index_of a l) := rfl

theorem index_of_cons_eq {a b : α} (l : list α) : a = b → index_of a (b::l) = 0 :=
assume e, if_pos e

@[simp] theorem index_of_cons_self (a : α) (l : list α) : index_of a (a::l) = 0 :=
index_of_cons_eq _ rfl

@[simp, priority 990]
theorem index_of_cons_ne {a b : α} (l : list α) : a ≠ b → index_of a (b::l) = succ (index_of a l) :=
assume n, if_neg n

theorem index_of_eq_length {a : α} {l : list α} : index_of a l = length l ↔ a ∉ l :=
begin
  induction l with b l ih,
  { exact iff_of_true rfl (not_mem_nil _) },
  simp only [length, mem_cons_iff, index_of_cons], split_ifs,
  { exact iff_of_false (by rintro ⟨⟩) (λ H, H $ or.inl h) },
  { simp only [h, false_or], rw ← ih, exact succ_inj' }
end

@[simp, priority 980]
theorem index_of_of_not_mem {l : list α} {a : α} : a ∉ l → index_of a l = length l :=
index_of_eq_length.2

theorem index_of_le_length {a : α} {l : list α} : index_of a l ≤ length l :=
begin
  induction l with b l ih, {refl},
  simp only [length, index_of_cons],
  by_cases h : a = b, {rw if_pos h, exact nat.zero_le _},
  rw if_neg h, exact succ_le_succ ih
end

theorem index_of_lt_length {a} {l : list α} : index_of a l < length l ↔ a ∈ l :=
⟨λh, decidable.by_contradiction $ λ al, ne_of_lt h $ index_of_eq_length.2 al,
λal, lt_of_le_of_ne index_of_le_length $ λ h, index_of_eq_length.1 h al⟩

end index_of

/-! ### nth element -/

theorem nth_le_of_mem : ∀ {a} {l : list α}, a ∈ l → ∃ n h, nth_le l n h = a
| a (_ :: l) (or.inl rfl) := ⟨0, succ_pos _, rfl⟩
| a (b :: l) (or.inr m)   :=
  let ⟨n, h, e⟩ := nth_le_of_mem m in ⟨n+1, succ_lt_succ h, e⟩

theorem nth_le_nth : ∀ {l : list α} {n} h, nth l n = some (nth_le l n h)
| (a :: l) 0     h := rfl
| (a :: l) (n+1) h := @nth_le_nth l n _

theorem nth_len_le : ∀ {l : list α} {n}, length l ≤ n → nth l n = none
| []       n     h := rfl
| (a :: l) (n+1) h := nth_len_le (le_of_succ_le_succ h)

theorem nth_eq_some {l : list α} {n a} : nth l n = some a ↔ ∃ h, nth_le l n h = a :=
⟨λ e,
  have h : n < length l, from lt_of_not_ge $ λ hn,
    by rw nth_len_le hn at e; contradiction,
  ⟨h, by rw nth_le_nth h at e;
    injection e with e; apply nth_le_mem⟩,
λ ⟨h, e⟩, e ▸ nth_le_nth _⟩

@[simp]
theorem nth_eq_none_iff : ∀ {l : list α} {n}, nth l n = none ↔ length l ≤ n :=
begin
  intros, split,
  { intro h, by_contradiction h',
    have h₂ : ∃ h, l.nth_le n h = l.nth_le n (lt_of_not_ge h') := ⟨lt_of_not_ge h', rfl⟩,
    rw [← nth_eq_some, h] at h₂, cases h₂ },
  { solve_by_elim [nth_len_le] },
end

theorem nth_of_mem {a} {l : list α} (h : a ∈ l) : ∃ n, nth l n = some a :=
let ⟨n, h, e⟩ := nth_le_of_mem h in ⟨n, by rw [nth_le_nth, e]⟩

theorem nth_le_mem : ∀ (l : list α) n h, nth_le l n h ∈ l
| (a :: l) 0     h := mem_cons_self _ _
| (a :: l) (n+1) h := mem_cons_of_mem _ (nth_le_mem l _ _)

theorem nth_mem {l : list α} {n a} (e : nth l n = some a) : a ∈ l :=
let ⟨h, e⟩ := nth_eq_some.1 e in e ▸ nth_le_mem _ _ _

theorem mem_iff_nth_le {a} {l : list α} : a ∈ l ↔ ∃ n h, nth_le l n h = a :=
⟨nth_le_of_mem, λ ⟨n, h, e⟩, e ▸ nth_le_mem _ _ _⟩

theorem mem_iff_nth {a} {l : list α} : a ∈ l ↔ ∃ n, nth l n = some a :=
mem_iff_nth_le.trans $ exists_congr $ λ n, nth_eq_some.symm

lemma nth_zero (l : list α) : l.nth 0 = l.head' := by cases l; refl

lemma nth_injective {α : Type u} {xs : list α} {i j : ℕ}
  (h₀ : i < xs.length)
  (h₁ : nodup xs)
  (h₂ : xs.nth i = xs.nth j) : i = j :=
begin
  induction xs with x xs generalizing i j,
  { cases h₀ },
  { cases i; cases j,
    case nat.zero nat.zero
    { refl },
    case nat.succ nat.succ
    { congr, cases h₁,
      apply xs_ih;
      solve_by_elim [lt_of_succ_lt_succ] },
    iterate 2
    { dsimp at h₂,
      cases h₁ with _ _ h h',
      cases h x _ rfl,
      rw mem_iff_nth,
      exact ⟨_, h₂.symm⟩ <|>
        exact ⟨_, h₂⟩ } },
end

@[simp] theorem nth_map (f : α → β) : ∀ l n, nth (map f l) n = (nth l n).map f
| []       n     := rfl
| (a :: l) 0     := rfl
| (a :: l) (n+1) := nth_map l n

theorem nth_le_map (f : α → β) {l n} (H1 H2) : nth_le (map f l) n H1 = f (nth_le l n H2) :=
option.some.inj $ by rw [← nth_le_nth, nth_map, nth_le_nth]; refl

/-- A version of `nth_le_map` that can be used for rewriting. -/
theorem nth_le_map_rev (f : α → β) {l n} (H) :
  f (nth_le l n H) = nth_le (map f l) n ((length_map f l).symm ▸ H) :=
(nth_le_map f _ _).symm

@[simp] theorem nth_le_map' (f : α → β) {l n} (H) :
  nth_le (map f l) n H = f (nth_le l n (length_map f l ▸ H)) :=
nth_le_map f _ _

/-- If one has `nth_le L i hi` in a formula and `h : L = L'`, one can not `rw h` in the formula as
`hi` gives `i < L.length` and not `i < L'.length`. The lemma `nth_le_of_eq` can be used to make
such a rewrite, with `rw (nth_le_of_eq h)`. -/
lemma nth_le_of_eq {L L' : list α} (h : L = L') {i : ℕ} (hi : i < L.length) :
  nth_le L i hi = nth_le L' i (h ▸ hi) :=
by { congr, exact h}

@[simp] lemma nth_le_singleton (a : α) {n : ℕ} (hn : n < 1) :
  nth_le [a] n hn = a :=
have hn0 : n = 0 := le_zero_iff.1 (le_of_lt_succ hn),
by subst hn0; refl

lemma nth_le_zero [inhabited α] {L : list α} (h : 0 < L.length) :
  L.nth_le 0 h = L.head :=
by { cases L, cases h, simp, }

lemma nth_le_append : ∀ {l₁ l₂ : list α} {n : ℕ} (hn₁) (hn₂),
  (l₁ ++ l₂).nth_le n hn₁ = l₁.nth_le n hn₂
| []     _ n     hn₁ hn₂  := (nat.not_lt_zero _ hn₂).elim
| (a::l) _ 0     hn₁ hn₂ := rfl
| (a::l) _ (n+1) hn₁ hn₂ := by simp only [nth_le, cons_append];
                         exact nth_le_append _ _

lemma nth_le_append_right_aux {l₁ l₂ : list α} {n : ℕ}
  (h₁ : l₁.length ≤ n) (h₂ : n < (l₁ ++ l₂).length) : n - l₁.length < l₂.length :=
begin
  rw list.length_append at h₂,
  convert (tsub_lt_tsub_iff_right h₁).mpr h₂,
  simp,
end

lemma nth_le_append_right : ∀ {l₁ l₂ : list α} {n : ℕ} (h₁ : l₁.length ≤ n) (h₂),
  (l₁ ++ l₂).nth_le n h₂ = l₂.nth_le (n - l₁.length) (nth_le_append_right_aux h₁ h₂)
| []       _ n     h₁ h₂ := rfl
| (a :: l) _ (n+1) h₁ h₂ :=
  begin
    dsimp,
    conv { to_rhs, congr, skip,
      rw [tsub_add_eq_tsub_tsub, tsub_right_comm, add_tsub_cancel_right], },
    rw nth_le_append_right (nat.lt_succ_iff.mp h₁),
  end

@[simp] lemma nth_le_repeat (a : α) {n m : ℕ} (h : m < (list.repeat a n).length) :
  (list.repeat a n).nth_le m h = a :=
eq_of_mem_repeat (nth_le_mem _ _ _)

lemma nth_append {l₁ l₂ : list α} {n : ℕ} (hn : n < l₁.length) :
  (l₁ ++ l₂).nth n = l₁.nth n :=
have hn' : n < (l₁ ++ l₂).length := lt_of_lt_of_le hn
  (by rw length_append; exact nat.le_add_right _ _),
by rw [nth_le_nth hn, nth_le_nth hn', nth_le_append]

lemma nth_append_right {l₁ l₂ : list α} {n : ℕ} (hn : l₁.length ≤ n) :
  (l₁ ++ l₂).nth n = l₂.nth (n - l₁.length) :=
begin
  by_cases hl : n < (l₁ ++ l₂).length,
  { rw [nth_le_nth hl, nth_le_nth, nth_le_append_right hn] },
  { rw [nth_len_le (le_of_not_lt hl), nth_len_le],
    rw [not_lt, length_append] at hl,
    exact le_tsub_of_add_le_left hl }
end

lemma last_eq_nth_le : ∀ (l : list α) (h : l ≠ []),
  last l h = l.nth_le (l.length - 1) (nat.sub_lt (length_pos_of_ne_nil h) one_pos)
| [] h := rfl
| [a] h := by rw [last_singleton, nth_le_singleton]
| (a :: b :: l) h := by { rw [last_cons, last_eq_nth_le (b :: l)],
                          refl, exact cons_ne_nil b l }

@[simp] lemma nth_concat_length : ∀ (l : list α) (a : α), (l ++ [a]).nth l.length = some a
| []     a := rfl
| (b::l) a := by rw [cons_append, length_cons, nth, nth_concat_length]

lemma nth_le_cons_length (x : α) (xs : list α) (n : ℕ) (h : n = xs.length) :
  (x :: xs).nth_le n (by simp [h]) = (x :: xs).last (cons_ne_nil x xs) :=
begin
  rw last_eq_nth_le,
  congr,
  simp [h]
end

@[ext]
theorem ext : ∀ {l₁ l₂ : list α}, (∀n, nth l₁ n = nth l₂ n) → l₁ = l₂
| []      []       h := rfl
| (a::l₁) []       h := by have h0 := h 0; contradiction
| []      (a'::l₂) h := by have h0 := h 0; contradiction
| (a::l₁) (a'::l₂) h := by have h0 : some a = some a' := h 0; injection h0 with aa;
    simp only [aa, ext (λn, h (n+1))]; split; refl

theorem ext_le {l₁ l₂ : list α} (hl : length l₁ = length l₂)
  (h : ∀n h₁ h₂, nth_le l₁ n h₁ = nth_le l₂ n h₂) : l₁ = l₂ :=
ext $ λn, if h₁ : n < length l₁
  then by rw [nth_le_nth, nth_le_nth, h n h₁ (by rwa [← hl])]
  else let h₁ := le_of_not_gt h₁ in by { rw [nth_len_le h₁, nth_len_le], rwa [←hl], }

@[simp] theorem index_of_nth_le [decidable_eq α] {a : α} :
  ∀ {l : list α} h, nth_le l (index_of a l) h = a
| (b::l) h := by by_cases h' : a = b;
  simp only [h', if_pos, if_false, index_of_cons, nth_le, @index_of_nth_le l]

@[simp] theorem index_of_nth [decidable_eq α] {a : α} {l : list α} (h : a ∈ l) :
  nth l (index_of a l) = some a :=
by rw [nth_le_nth, index_of_nth_le (index_of_lt_length.2 h)]

theorem nth_le_reverse_aux1 :
  ∀ (l r : list α) (i h1 h2), nth_le (reverse_core l r) (i + length l) h1 = nth_le r i h2
| []       r i := λh1 h2, rfl
| (a :: l) r i :=
  by rw (show i + length (a :: l) = i + 1 + length l, from add_right_comm i (length l) 1);
    exact λh1 h2, nth_le_reverse_aux1 l (a :: r) (i+1) h1 (succ_lt_succ h2)

lemma index_of_inj [decidable_eq α] {l : list α} {x y : α}
  (hx : x ∈ l) (hy : y ∈ l) : index_of x l = index_of y l ↔ x = y :=
⟨λ h, have nth_le l (index_of x l) (index_of_lt_length.2 hx) =
        nth_le l (index_of y l) (index_of_lt_length.2 hy),
      by simp only [h],
    by simpa only [index_of_nth_le],
  λ h, by subst h⟩

theorem nth_le_reverse_aux2 : ∀ (l r : list α) (i : nat) (h1) (h2),
  nth_le (reverse_core l r) (length l - 1 - i) h1 = nth_le l i h2
| []       r i     h1 h2 := absurd h2 (nat.not_lt_zero _)
| (a :: l) r 0     h1 h2 := begin
    have aux := nth_le_reverse_aux1 l (a :: r) 0,
    rw zero_add at aux,
    exact aux _ (zero_lt_succ _)
  end
| (a :: l) r (i+1) h1 h2 := begin
    have aux := nth_le_reverse_aux2 l (a :: r) i,
    have heq := calc length (a :: l) - 1 - (i + 1)
          = length l - (1 + i) : by rw add_comm; refl
      ... = length l - 1 - i   : by rw ← tsub_add_eq_tsub_tsub,
    rw [← heq] at aux,
    apply aux
  end

@[simp] theorem nth_le_reverse (l : list α) (i : nat) (h1 h2) :
  nth_le (reverse l) (length l - 1 - i) h1 = nth_le l i h2 :=
nth_le_reverse_aux2 _ _ _ _ _

lemma nth_le_reverse' (l : list α) (n : ℕ) (hn : n < l.reverse.length) (hn') :
  l.reverse.nth_le n hn = l.nth_le (l.length - 1 - n) hn' :=
begin
  rw eq_comm,
  convert nth_le_reverse l.reverse _ _ _ using 1,
  { simp },
  { simpa }
end

lemma eq_cons_of_length_one {l : list α} (h : l.length = 1) :
  l = [l.nth_le 0 (h.symm ▸ zero_lt_one)] :=
begin
  refine ext_le (by convert h) (λ n h₁ h₂, _),
  simp only [nth_le_singleton],
  congr,
  exact eq_bot_iff.mpr (nat.lt_succ_iff.mp h₂)
end

lemma modify_nth_tail_modify_nth_tail {f g : list α → list α} (m : ℕ) :
  ∀n (l:list α), (l.modify_nth_tail f n).modify_nth_tail g (m + n) =
    l.modify_nth_tail (λl, (f l).modify_nth_tail g m) n
| 0     l      := rfl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (list.cons a) (modify_nth_tail_modify_nth_tail n l)

lemma modify_nth_tail_modify_nth_tail_le
  {f g : list α → list α} (m n : ℕ) (l : list α) (h : n ≤ m) :
  (l.modify_nth_tail f n).modify_nth_tail g m =
    l.modify_nth_tail (λl, (f l).modify_nth_tail g (m - n)) n :=
begin
  rcases le_iff_exists_add.1 h with ⟨m, rfl⟩,
  rw [add_tsub_cancel_left, add_comm, modify_nth_tail_modify_nth_tail]
end

lemma modify_nth_tail_modify_nth_tail_same {f g : list α → list α} (n : ℕ) (l:list α) :
  (l.modify_nth_tail f n).modify_nth_tail g n = l.modify_nth_tail (g ∘ f) n :=
by rw [modify_nth_tail_modify_nth_tail_le n n l (le_refl n), tsub_self]; refl

lemma modify_nth_tail_id :
  ∀n (l:list α), l.modify_nth_tail id n = l
| 0     l      := rfl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (list.cons a) (modify_nth_tail_id n l)

theorem remove_nth_eq_nth_tail : ∀ n (l : list α), remove_nth l n = modify_nth_tail tail n l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (a::l) := congr_arg (cons _) (remove_nth_eq_nth_tail _ _)

theorem update_nth_eq_modify_nth (a : α) : ∀ n (l : list α),
  update_nth l n a = modify_nth (λ _, a) n l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (b::l) := congr_arg (cons _) (update_nth_eq_modify_nth _ _)

theorem modify_nth_eq_update_nth (f : α → α) : ∀ n (l : list α),
  modify_nth f n l = ((λ a, update_nth l n (f a)) <$> nth l n).get_or_else l
| 0     l      := by cases l; refl
| (n+1) []     := rfl
| (n+1) (b::l) := (congr_arg (cons b)
  (modify_nth_eq_update_nth n l)).trans $ by cases nth l n; refl

theorem nth_modify_nth (f : α → α) : ∀ n (l : list α) m,
  nth (modify_nth f n l) m = (λ a, if n = m then f a else a) <$> nth l m
| n     l      0     := by cases l; cases n; refl
| n     []     (m+1) := by cases n; refl
| 0     (a::l) (m+1) := by cases nth l m; refl
| (n+1) (a::l) (m+1) := (nth_modify_nth n l m).trans $
  by cases nth l m with b; by_cases n = m;
  simp only [h, if_pos, if_true, if_false, option.map_none, option.map_some, mt succ.inj,
    not_false_iff]

theorem modify_nth_tail_length (f : list α → list α) (H : ∀ l, length (f l) = length l) :
  ∀ n l, length (modify_nth_tail f n l) = length l
| 0     l      := H _
| (n+1) []     := rfl
| (n+1) (a::l) := @congr_arg _ _ _ _ (+1) (modify_nth_tail_length _ _)

@[simp] theorem modify_nth_length (f : α → α) :
  ∀ n l, length (modify_nth f n l) = length l :=
modify_nth_tail_length _ (λ l, by cases l; refl)

@[simp] theorem update_nth_length (l : list α) (n) (a : α) :
  length (update_nth l n a) = length l :=
by simp only [update_nth_eq_modify_nth, modify_nth_length]

@[simp] theorem nth_modify_nth_eq (f : α → α) (n) (l : list α) :
  nth (modify_nth f n l) n = f <$> nth l n :=
by simp only [nth_modify_nth, if_pos]

@[simp] theorem nth_modify_nth_ne (f : α → α) {m n} (l : list α) (h : m ≠ n) :
  nth (modify_nth f m l) n = nth l n :=
by simp only [nth_modify_nth, if_neg h, id_map']

theorem nth_update_nth_eq (a : α) (n) (l : list α) :
  nth (update_nth l n a) n = (λ _, a) <$> nth l n :=
by simp only [update_nth_eq_modify_nth, nth_modify_nth_eq]

theorem nth_update_nth_of_lt (a : α) {n} {l : list α} (h : n < length l) :
  nth (update_nth l n a) n = some a :=
by rw [nth_update_nth_eq, nth_le_nth h]; refl

theorem nth_update_nth_ne (a : α) {m n} (l : list α) (h : m ≠ n) :
  nth (update_nth l m a) n = nth l n :=
by simp only [update_nth_eq_modify_nth, nth_modify_nth_ne _ _ h]

@[simp] lemma update_nth_nil (n : ℕ) (a : α) : [].update_nth n a = [] := rfl

@[simp] lemma update_nth_succ (x : α) (xs : list α) (n : ℕ) (a : α) :
  (x :: xs).update_nth n.succ a = x :: xs.update_nth n a := rfl

lemma update_nth_comm (a b : α) : Π {n m : ℕ} (l : list α) (h : n ≠ m),
  (l.update_nth n a).update_nth m b = (l.update_nth m b).update_nth n a
| _ _ [] _ := by simp
| 0 0 (x :: t) h := absurd rfl h
| (n + 1) 0 (x :: t) h := by simp [list.update_nth]
| 0 (m + 1) (x :: t) h := by simp [list.update_nth]
| (n + 1) (m + 1) (x :: t) h := by { simp only [update_nth, true_and, eq_self_iff_true],
  exact update_nth_comm t (λ h', h $ nat.succ_inj'.mpr h'), }

@[simp] lemma nth_le_update_nth_eq (l : list α) (i : ℕ) (a : α)
  (h : i < (l.update_nth i a).length) : (l.update_nth i a).nth_le i h = a :=
by rw [← option.some_inj, ← nth_le_nth, nth_update_nth_eq, nth_le_nth]; simp * at *

@[simp] lemma nth_le_update_nth_of_ne {l : list α} {i j : ℕ} (h : i ≠ j) (a : α)
  (hj : j < (l.update_nth i a).length) :
  (l.update_nth i a).nth_le j hj = l.nth_le j (by simpa using hj) :=
by rw [← option.some_inj, ← list.nth_le_nth, list.nth_update_nth_ne _ _ h, list.nth_le_nth]

lemma mem_or_eq_of_mem_update_nth : ∀ {l : list α} {n : ℕ} {a b : α}
  (h : a ∈ l.update_nth n b), a ∈ l ∨ a = b
| []     n     a b h := false.elim h
| (c::l) 0     a b h := ((mem_cons_iff _ _ _).1 h).elim
  or.inr (or.inl ∘ mem_cons_of_mem _)
| (c::l) (n+1) a b h := ((mem_cons_iff _ _ _).1 h).elim
  (λ h, h ▸ or.inl (mem_cons_self _ _))
  (λ h, (mem_or_eq_of_mem_update_nth h).elim
    (or.inl ∘ mem_cons_of_mem _) or.inr)

section insert_nth
variable {a : α}

@[simp] lemma insert_nth_zero (s : list α) (x : α) : insert_nth 0 x s = x :: s := rfl

@[simp] lemma insert_nth_succ_nil (n : ℕ) (a : α) : insert_nth (n + 1) a [] = [] := rfl

@[simp] lemma insert_nth_succ_cons (s : list α) (hd x : α) (n : ℕ) :
  insert_nth (n + 1) x (hd :: s) = hd :: (insert_nth n x s) := rfl

lemma length_insert_nth : ∀n as, n ≤ length as → length (insert_nth n a as) = length as + 1
| 0     as       h := rfl
| (n+1) []       h := (nat.not_succ_le_zero _ h).elim
| (n+1) (a'::as) h := congr_arg nat.succ $ length_insert_nth n as (nat.le_of_succ_le_succ h)

lemma remove_nth_insert_nth (n:ℕ) (l : list α) : (l.insert_nth n a).remove_nth n = l :=
by rw [remove_nth_eq_nth_tail, insert_nth, modify_nth_tail_modify_nth_tail_same];
from modify_nth_tail_id _ _

lemma insert_nth_remove_nth_of_ge : ∀n m as, n < length as → n ≤ m →
  insert_nth m a (as.remove_nth n) = (as.insert_nth (m + 1) a).remove_nth n
| 0     0     []      has _   := (lt_irrefl _ has).elim
| 0     0     (a::as) has hmn := by simp [remove_nth, insert_nth]
| 0     (m+1) (a::as) has hmn := rfl
| (n+1) (m+1) (a::as) has hmn :=
  congr_arg (cons a) $
    insert_nth_remove_nth_of_ge n m as (nat.lt_of_succ_lt_succ has) (nat.le_of_succ_le_succ hmn)

lemma insert_nth_remove_nth_of_le : ∀n m as, n < length as → m ≤ n →
  insert_nth m a (as.remove_nth n) = (as.insert_nth m a).remove_nth (n + 1)
| n       0       (a :: as) has hmn := rfl
| (n + 1) (m + 1) (a :: as) has hmn :=
  congr_arg (cons a) $
    insert_nth_remove_nth_of_le n m as (nat.lt_of_succ_lt_succ has) (nat.le_of_succ_le_succ hmn)

lemma insert_nth_comm (a b : α) :
  ∀(i j : ℕ) (l : list α) (h : i ≤ j) (hj : j ≤ length l),
    (l.insert_nth i a).insert_nth (j + 1) b = (l.insert_nth j b).insert_nth i a
| 0       j     l      := by simp [insert_nth]
| (i + 1) 0     l      := assume h, (nat.not_lt_zero _ h).elim
| (i + 1) (j+1) []     := by simp
| (i + 1) (j+1) (c::l) :=
  assume h₀ h₁,
  by simp [insert_nth];
    exact insert_nth_comm i j l (nat.le_of_succ_le_succ h₀) (nat.le_of_succ_le_succ h₁)

lemma mem_insert_nth {a b : α} : ∀ {n : ℕ} {l : list α} (hi : n ≤ l.length),
  a ∈ l.insert_nth n b ↔ a = b ∨ a ∈ l
| 0     as       h := iff.rfl
| (n+1) []       h := (nat.not_succ_le_zero _ h).elim
| (n+1) (a'::as) h := begin
  dsimp [list.insert_nth],
  erw [list.mem_cons_iff, mem_insert_nth (nat.le_of_succ_le_succ h), list.mem_cons_iff,
    ← or.assoc, or_comm (a = a'), or.assoc]
end

lemma inj_on_insert_nth_index_of_not_mem (l : list α) (x : α) (hx : x ∉ l) :
  set.inj_on (λ k, insert_nth k x l) {n | n ≤ l.length} :=
begin
  induction l with hd tl IH,
  { intros n hn m hm h,
    simp only [set.mem_singleton_iff, set.set_of_eq_eq_singleton, length, nonpos_iff_eq_zero]
      at hn hm,
    simp [hn, hm] },
  { intros n hn m hm h,
    simp only [length, set.mem_set_of_eq] at hn hm,
    simp only [mem_cons_iff, not_or_distrib] at hx,
    cases n;
    cases m,
    { refl },
    { simpa [hx.left] using h },
    { simpa [ne.symm hx.left] using h },
    { simp only [true_and, eq_self_iff_true, insert_nth_succ_cons] at h,
      rw nat.succ_inj',
      refine IH hx.right _ _ h,
      { simpa [nat.succ_le_succ_iff] using hn },
      { simpa [nat.succ_le_succ_iff] using hm } } }
end

lemma insert_nth_of_length_lt (l : list α) (x : α) (n : ℕ) (h : l.length < n) :
  insert_nth n x l = l :=
begin
  induction l with hd tl IH generalizing n,
  { cases n,
    { simpa using h },
    { simp } },
  { cases n,
    { simpa using h },
    { simp only [nat.succ_lt_succ_iff, length] at h,
      simpa using IH _ h } }
end

@[simp] lemma insert_nth_length_self (l : list α) (x : α) :
  insert_nth l.length x l = l ++ [x] :=
begin
  induction l with hd tl IH,
  { simp },
  { simpa using IH }
end

lemma length_le_length_insert_nth (l : list α) (x : α) (n : ℕ) :
  l.length ≤ (insert_nth n x l).length :=
begin
  cases le_or_lt n l.length with hn hn,
  { rw length_insert_nth _ _ hn,
    exact (nat.lt_succ_self _).le },
  { rw insert_nth_of_length_lt _ _ _ hn }
end

lemma length_insert_nth_le_succ (l : list α) (x : α) (n : ℕ) :
  (insert_nth n x l).length ≤ l.length + 1 :=
begin
  cases le_or_lt n l.length with hn hn,
  { rw length_insert_nth _ _ hn },
  { rw insert_nth_of_length_lt _ _ _ hn,
    exact (nat.lt_succ_self _).le }
end

lemma nth_le_insert_nth_of_lt (l : list α) (x : α) (n k : ℕ) (hn : k < n)
  (hk : k < l.length)
  (hk' : k < (insert_nth n x l).length := hk.trans_le (length_le_length_insert_nth _ _ _)):
  (insert_nth n x l).nth_le k hk' = l.nth_le k hk :=
begin
  induction n with n IH generalizing k l,
  { simpa using hn },
  { cases l with hd tl,
    { simp },
    { cases k,
      { simp },
      { rw nat.succ_lt_succ_iff at hn,
        simpa using IH _ _ hn _ } } }
end

@[simp] lemma nth_le_insert_nth_self (l : list α) (x : α) (n : ℕ)
  (hn : n ≤ l.length) (hn' : n < (insert_nth n x l).length :=
    by rwa [length_insert_nth _ _ hn, nat.lt_succ_iff]) :
  (insert_nth n x l).nth_le n hn' = x :=
begin
  induction l with hd tl IH generalizing n,
  { simp only [length, nonpos_iff_eq_zero] at hn,
    simp [hn] },
  { cases n,
    { simp },
    { simp only [nat.succ_le_succ_iff, length] at hn,
      simpa using IH _ hn } }
end

lemma nth_le_insert_nth_add_succ (l : list α) (x : α) (n k : ℕ)
  (hk' : n + k < l.length)
  (hk : n + k + 1 < (insert_nth n x l).length :=
    by rwa [length_insert_nth _ _ (le_self_add.trans hk'.le), nat.succ_lt_succ_iff]) :
  (insert_nth n x l).nth_le (n + k + 1) hk = nth_le l (n + k) hk' :=
begin
  induction l with hd tl IH generalizing n k,
  { simpa using hk' },
  { cases n,
    { simpa },
    { simpa [succ_add] using IH _ _ _ } }
end

lemma insert_nth_injective (n : ℕ) (x : α) : function.injective (insert_nth n x) :=
begin
  induction n with n IH,
  { have : insert_nth 0 x = cons x := funext (λ _, rfl),
    simp [this] },
  { rintros (_|⟨a, as⟩) (_|⟨b, bs⟩) h;
    simpa [IH.eq_iff] using h <|> refl }
end

end insert_nth

/-! ### map -/

@[simp] lemma map_nil (f : α → β) : map f [] = [] := rfl

theorem map_eq_foldr (f : α → β) (l : list α) :
  map f l = foldr (λ a bs, f a :: bs) [] l :=
by induction l; simp *

lemma map_congr {f g : α → β} : ∀ {l : list α}, (∀ x ∈ l, f x = g x) → map f l = map g l
| []     _ := rfl
| (a::l) h := let ⟨h₁, h₂⟩ := forall_mem_cons.1 h in
  by rw [map, map, h₁, map_congr h₂]

lemma map_eq_map_iff {f g : α → β} {l : list α} : map f l = map g l ↔ (∀ x ∈ l, f x = g x) :=
begin
  refine ⟨_, map_congr⟩, intros h x hx,
  rw [mem_iff_nth_le] at hx, rcases hx with ⟨n, hn, rfl⟩,
  rw [nth_le_map_rev f, nth_le_map_rev g], congr, exact h
end

theorem map_concat (f : α → β) (a : α) (l : list α) : map f (concat l a) = concat (map f l) (f a) :=
by induction l; [refl, simp only [*, concat_eq_append, cons_append, map, map_append]]; split; refl

@[simp] theorem map_id'' (l : list α) : map (λ x, x) l = l :=
map_id _

theorem map_id' {f : α → α} (h : ∀ x, f x = x) (l : list α) : map f l = l :=
by simp [show f = id, from funext h]

theorem eq_nil_of_map_eq_nil {f : α → β} {l : list α} (h : map f l = nil) : l = nil :=
eq_nil_of_length_eq_zero $ by rw [← length_map f l, h]; refl

@[simp] theorem map_join (f : α → β) (L : list (list α)) :
  map f (join L) = join (map (map f) L) :=
by induction L; [refl, simp only [*, join, map, map_append]]

theorem bind_ret_eq_map (f : α → β) (l : list α) :
  l.bind (list.ret ∘ f) = map f l :=
by unfold list.bind; induction l; simp only [map, join, list.ret, cons_append, nil_append, *];
  split; refl

@[simp] theorem map_eq_map {α β} (f : α → β) (l : list α) : f <$> l = map f l := rfl

@[simp] theorem map_tail (f : α → β) (l) : map f (tail l) = tail (map f l) :=
by cases l; refl

@[simp] theorem map_injective_iff {f : α → β} : injective (map f) ↔ injective f :=
begin
  split; intros h x y hxy,
  { suffices : [x] = [y], { simpa using this }, apply h, simp [hxy] },
  { induction y generalizing x, simpa using hxy,
    cases x, simpa using hxy, simp at hxy, simp [y_ih hxy.2, h hxy.1] }
end

/--
A single `list.map` of a composition of functions is equal to
composing a `list.map` with another `list.map`, fully applied.
This is the reverse direction of `list.map_map`.
-/
lemma comp_map (h : β → γ) (g : α → β) (l : list α) :
  map (h ∘ g) l = map h (map g l) := (map_map _ _ _).symm

/--
Composing a `list.map` with another `list.map` is equal to
a single `list.map` of composed functions.
-/
@[simp] lemma map_comp_map (g : β → γ) (f : α → β) :
  map g ∘ map f = map (g ∘ f) :=
by { ext l, rw comp_map }

theorem map_filter_eq_foldr (f : α → β) (p : α → Prop) [decidable_pred p] (as : list α) :
  map f (filter p as) = foldr (λ a bs, if p a then f a :: bs else bs) [] as :=
by { induction as, { refl }, { simp! [*, apply_ite (map f)] } }

lemma last_map (f : α → β) {l : list α} (hl : l ≠ []) :
  (l.map f).last (mt eq_nil_of_map_eq_nil hl) = f (l.last hl) :=
begin
  induction l with l_ih l_tl l_ih,
  { apply (hl rfl).elim },
  { cases l_tl,
    { simp },
    { simpa using l_ih } }
end

/-! ### map₂ -/

theorem nil_map₂ (f : α → β → γ) (l : list β) : map₂ f [] l = [] :=
by cases l; refl

theorem map₂_nil (f : α → β → γ) (l : list α) : map₂ f l [] = [] :=
by cases l; refl

@[simp] theorem map₂_flip (f : α → β → γ) :
  ∀ as bs, map₂ (flip f) bs as = map₂ f as bs
| [] [] := rfl
| [] (b :: bs) := rfl
| (a :: as) [] := rfl
| (a :: as) (b :: bs) := by { simp! [map₂_flip], refl }

/-! ### take, drop -/
@[simp] theorem take_zero (l : list α) : take 0 l = [] := rfl

@[simp] theorem take_nil : ∀ n, take n [] = ([] : list α)
| 0     := rfl
| (n+1) := rfl

theorem take_cons (n) (a : α) (l : list α) : take (succ n) (a::l) = a :: take n l := rfl

@[simp] theorem take_length : ∀ (l : list α), take (length l) l = l
| []     := rfl
| (a::l) := begin change a :: (take (length l) l) = a :: l, rw take_length end

theorem take_all_of_le : ∀ {n} {l : list α}, length l ≤ n → take n l = l
| 0     []     h := rfl
| 0     (a::l) h := absurd h (not_le_of_gt (zero_lt_succ _))
| (n+1) []     h := rfl
| (n+1) (a::l) h :=
  begin
    change a :: take n l = a :: l,
    rw [take_all_of_le (le_of_succ_le_succ h)]
  end

@[simp] theorem take_left : ∀ l₁ l₂ : list α, take (length l₁) (l₁ ++ l₂) = l₁
| []      l₂ := rfl
| (a::l₁) l₂ := congr_arg (cons a) (take_left l₁ l₂)

theorem take_left' {l₁ l₂ : list α} {n} (h : length l₁ = n) :
  take n (l₁ ++ l₂) = l₁ :=
by rw ← h; apply take_left

theorem take_take : ∀ (n m) (l : list α), take n (take m l) = take (min n m) l
| n         0        l      := by rw [min_zero, take_zero, take_nil]
| 0         m        l      := by rw [zero_min, take_zero, take_zero]
| (succ n)  (succ m) nil    := by simp only [take_nil]
| (succ n)  (succ m) (a::l) := by simp only [take, min_succ_succ, take_take n m l]; split; refl

theorem take_repeat (a : α) : ∀ (n m : ℕ), take n (repeat a m) = repeat a (min n m)
| n        0        := by simp
| 0        m        := by simp
| (succ n) (succ m) := by simp [min_succ_succ, take_repeat]

lemma map_take {α β : Type*} (f : α → β) :
  ∀ (L : list α) (i : ℕ), (L.take i).map f = (L.map f).take i
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [map_take], }

/-- Taking the first `n` elements in `l₁ ++ l₂` is the same as appending the first `n` elements
of `l₁` to the first `n - l₁.length` elements of `l₂`. -/
lemma take_append_eq_append_take {l₁ l₂ : list α} {n : ℕ} :
  take n (l₁ ++ l₂) = take n l₁ ++ take (n - l₁.length) l₂ :=
begin
  induction l₁ generalizing n, { simp },
  cases n, { simp }, simp *
end

lemma take_append_of_le_length {l₁ l₂ : list α} {n : ℕ} (h : n ≤ l₁.length) :
  (l₁ ++ l₂).take n = l₁.take n :=
by simp [take_append_eq_append_take, tsub_eq_zero_iff_le.mpr h]

/-- Taking the first `l₁.length + i` elements in `l₁ ++ l₂` is the same as appending the first
`i` elements of `l₂` to `l₁`. -/
lemma take_append {l₁ l₂ : list α} (i : ℕ) :
  take (l₁.length + i) (l₁ ++ l₂) = l₁ ++ (take i l₂) :=
by simp [take_append_eq_append_take, take_all_of_le le_self_add]

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the big list to the small list. -/
lemma nth_le_take (L : list α) {i j : ℕ} (hi : i < L.length) (hj : i < j) :
  nth_le L i hi = nth_le (L.take j) i (by { rw length_take, exact lt_min hj hi }) :=
by { rw nth_le_of_eq (take_append_drop j L).symm hi, exact nth_le_append _ _ }

/-- The `i`-th element of a list coincides with the `i`-th element of any of its prefixes of
length `> i`. Version designed to rewrite from the small list to the big list. -/
lemma nth_le_take' (L : list α) {i j : ℕ} (hi : i < (L.take j).length) :
  nth_le (L.take j) i hi = nth_le L i (lt_of_lt_of_le hi (by simp [le_refl])) :=
by { simp at hi, rw nth_le_take L _ hi.1 }

lemma nth_take {l : list α} {n m : ℕ} (h : m < n) :
  (l.take n).nth m = l.nth m :=
begin
  induction n with n hn generalizing l m,
  { simp only [nat.nat_zero_eq_zero] at h,
    exact absurd h (not_lt_of_le m.zero_le) },
  { cases l with hd tl,
    { simp only [take_nil] },
    { cases m,
      { simp only [nth, take] },
      { simpa only using hn (nat.lt_of_succ_lt_succ h) } } },
end

@[simp] lemma nth_take_of_succ {l : list α} {n : ℕ} :
  (l.take (n + 1)).nth n = l.nth n :=
nth_take (nat.lt_succ_self n)

lemma take_succ {l : list α} {n : ℕ} :
  l.take (n + 1) = l.take n ++ (l.nth n).to_list :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [option.to_list, nth, take_nil, append_nil]},
  { cases n,
    { simp only [option.to_list, nth, eq_self_iff_true, and_self, take, nil_append] },
    { simp only [hl, cons_append, nth, eq_self_iff_true, and_self, take] } }
end

@[simp] lemma take_eq_nil_iff {l : list α} {k : ℕ} :
  l.take k = [] ↔ l = [] ∨ k = 0 :=
by { cases l; cases k; simp [nat.succ_ne_zero] }

lemma init_eq_take (l : list α) : l.init = l.take l.length.pred :=
begin
  cases l with x l,
  { simp [init] },
  { induction l with hd tl hl generalizing x,
    { simp [init], },
    { simp [init, hl] } }
end

lemma init_take {n : ℕ} {l : list α} (h : n < l.length) :
  (l.take n).init = l.take n.pred :=
by simp [init_eq_take, min_eq_left_of_lt h, take_take, pred_le]

@[simp] lemma init_cons_of_ne_nil {α : Type*} {x : α} :
  ∀ {l : list α} (h : l ≠ []), (x :: l).init = x :: l.init
| []       h := false.elim (h rfl)
| (a :: l) _ := by simp [init]

@[simp] lemma init_append_of_ne_nil {α : Type*} {l : list α} :
  ∀ (l' : list α) (h : l ≠ []), (l' ++ l).init = l' ++ l.init
| []        _ := by simp only [nil_append]
| (a :: l') h := by simp [append_ne_nil_of_ne_nil_right l' l h, init_append_of_ne_nil l' h]

@[simp] lemma drop_eq_nil_of_le {l : list α} {k : ℕ} (h : l.length ≤ k) :
  l.drop k = [] :=
by simpa [←length_eq_zero] using tsub_eq_zero_iff_le.mpr h

lemma drop_eq_nil_iff_le {l : list α} {k : ℕ} :
  l.drop k = [] ↔ l.length ≤ k :=
begin
  refine ⟨λ h, _, drop_eq_nil_of_le⟩,
  induction k with k hk generalizing l,
  { simp only [drop] at h,
    simp [h] },
  { cases l,
    { simp },
    { simp only [drop] at h,
      simpa [nat.succ_le_succ_iff] using hk h } }
end

lemma tail_drop (l : list α) (n : ℕ) : (l.drop n).tail = l.drop (n + 1) :=
begin
  induction l with hd tl hl generalizing n,
  { simp },
  { cases n,
    { simp },
    { simp [hl] } }
end

lemma cons_nth_le_drop_succ {l : list α} {n : ℕ} (hn : n < l.length) :
  l.nth_le n hn :: l.drop (n + 1) = l.drop n :=
begin
  induction l with hd tl hl generalizing n,
  { exact absurd n.zero_le (not_le_of_lt (by simpa using hn)) },
  { cases n,
    { simp },
    { simp only [nat.succ_lt_succ_iff, list.length] at hn,
      simpa [list.nth_le, list.drop] using hl hn } }
end

theorem drop_nil : ∀ n, drop n [] = ([] : list α) :=
λ _, drop_eq_nil_of_le (nat.zero_le _)

@[simp] theorem drop_one : ∀ l : list α, drop 1 l = tail l
| []       := rfl
| (a :: l) := rfl

theorem drop_add : ∀ m n (l : list α), drop (m + n) l = drop m (drop n l)
| m 0     l      := rfl
| m (n+1) []     := (drop_nil _).symm
| m (n+1) (a::l) := drop_add m n _

@[simp] theorem drop_left : ∀ l₁ l₂ : list α, drop (length l₁) (l₁ ++ l₂) = l₂
| []      l₂ := rfl
| (a::l₁) l₂ := drop_left l₁ l₂

theorem drop_left' {l₁ l₂ : list α} {n} (h : length l₁ = n) :
  drop n (l₁ ++ l₂) = l₂ :=
by rw ← h; apply drop_left

theorem drop_eq_nth_le_cons : ∀ {n} {l : list α} h,
  drop n l = nth_le l n h :: drop (n+1) l
| 0     (a::l) h := rfl
| (n+1) (a::l) h := @drop_eq_nth_le_cons n _ _

@[simp] lemma drop_length (l : list α) : l.drop l.length = [] :=
calc l.drop l.length = (l ++ []).drop l.length : by simp
                 ... = [] : drop_left _ _

/-- Dropping the elements up to `n` in `l₁ ++ l₂` is the same as dropping the elements up to `n`
in `l₁`, dropping the elements up to `n - l₁.length` in `l₂`, and appending them. -/
lemma drop_append_eq_append_drop {l₁ l₂ : list α} {n : ℕ} :
  drop n (l₁ ++ l₂) = drop n l₁ ++ drop (n - l₁.length) l₂ :=
begin
  induction l₁ generalizing n, { simp },
  cases n, { simp }, simp *
end

lemma drop_append_of_le_length {l₁ l₂ : list α} {n : ℕ} (h : n ≤ l₁.length) :
  (l₁ ++ l₂).drop n = l₁.drop n ++ l₂ :=
by simp [drop_append_eq_append_drop, tsub_eq_zero_iff_le.mpr h]

/-- Dropping the elements up to `l₁.length + i` in `l₁ + l₂` is the same as dropping the elements
up to `i` in `l₂`. -/
lemma drop_append {l₁ l₂ : list α} (i : ℕ) :
  drop (l₁.length + i) (l₁ ++ l₂) = drop i l₂ :=
by simp [drop_append_eq_append_drop, take_all_of_le le_self_add]

/-- The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the big list to the small list. -/
lemma nth_le_drop (L : list α) {i j : ℕ} (h : i + j < L.length) :
  nth_le L (i + j) h = nth_le (L.drop i) j
begin
  have A : i < L.length := lt_of_le_of_lt (nat.le.intro rfl) h,
  rw (take_append_drop i L).symm at h,
  simpa only [le_of_lt A, min_eq_left, add_lt_add_iff_left, length_take, length_append] using h
end :=
begin
  have A : length (take i L) = i, by simp [le_of_lt (lt_of_le_of_lt (nat.le.intro rfl) h)],
  rw [nth_le_of_eq (take_append_drop i L).symm h, nth_le_append_right];
  simp [A]
end

/--  The `i + j`-th element of a list coincides with the `j`-th element of the list obtained by
dropping the first `i` elements. Version designed to rewrite from the small list to the big list. -/
lemma nth_le_drop' (L : list α) {i j : ℕ} (h : j < (L.drop i).length) :
  nth_le (L.drop i) j h = nth_le L (i + j) (lt_tsub_iff_left.mp ((length_drop i L) ▸ h)) :=
by rw nth_le_drop

lemma nth_drop (L : list α) (i j : ℕ) :
  nth (L.drop i) j = nth L (i + j) :=
begin
  ext,
  simp only [nth_eq_some, nth_le_drop', option.mem_def],
  split;
  exact λ ⟨h, ha⟩, ⟨by simpa [lt_tsub_iff_left] using h, ha⟩
end

@[simp] theorem drop_drop (n : ℕ) : ∀ (m) (l : list α), drop n (drop m l) = drop (n + m) l
| m     []     := by simp
| 0     l      := by simp
| (m+1) (a::l) :=
  calc drop n (drop (m + 1) (a :: l)) = drop n (drop m l) : rfl
    ... = drop (n + m) l : drop_drop m l
    ... = drop (n + (m + 1)) (a :: l) : rfl

theorem drop_take : ∀ (m : ℕ) (n : ℕ) (l : list α),
  drop m (take (m + n) l) = take n (drop m l)
| 0     n _      := by simp
| (m+1) n nil    := by simp
| (m+1) n (_::l) :=
  have h: m + 1 + n = (m+n) + 1, by ac_refl,
  by simpa [take_cons, h] using drop_take m n l

lemma map_drop {α β : Type*} (f : α → β) :
  ∀ (L : list α) (i : ℕ), (L.drop i).map f = (L.map f).drop i
| [] i := by simp
| L 0 := by simp
| (h :: t) (n+1) := by { dsimp, rw [map_drop], }

theorem modify_nth_tail_eq_take_drop (f : list α → list α) (H : f [] = []) :
  ∀ n l, modify_nth_tail f n l = take n l ++ f (drop n l)
| 0     l      := rfl
| (n+1) []     := H.symm
| (n+1) (b::l) := congr_arg (cons b) (modify_nth_tail_eq_take_drop n l)

theorem modify_nth_eq_take_drop (f : α → α) :
  ∀ n l, modify_nth f n l = take n l ++ modify_head f (drop n l) :=
modify_nth_tail_eq_take_drop _ rfl

theorem modify_nth_eq_take_cons_drop (f : α → α) {n l} (h) :
  modify_nth f n l = take n l ++ f (nth_le l n h) :: drop (n+1) l :=
by rw [modify_nth_eq_take_drop, drop_eq_nth_le_cons h]; refl

theorem update_nth_eq_take_cons_drop (a : α) {n l} (h : n < length l) :
  update_nth l n a = take n l ++ a :: drop (n+1) l :=
by rw [update_nth_eq_modify_nth, modify_nth_eq_take_cons_drop _ h]

lemma reverse_take {α} {xs : list α} (n : ℕ)
  (h : n ≤ xs.length) :
  xs.reverse.take n = (xs.drop (xs.length - n)).reverse :=
begin
  induction xs generalizing n;
    simp only [reverse_cons, drop, reverse_nil, zero_tsub, length, take_nil],
  cases h.lt_or_eq_dec with h' h',
  { replace h' := le_of_succ_le_succ h',
    rwa [take_append_of_le_length, xs_ih _ h'],
    rw [show xs_tl.length + 1 - n = succ (xs_tl.length - n), from _, drop],
    { rwa [succ_eq_add_one, ← tsub_add_eq_add_tsub] },
    { rwa length_reverse } },
  { subst h', rw [length, tsub_self, drop],
    suffices : xs_tl.length + 1 = (xs_tl.reverse ++ [xs_hd]).length,
      by rw [this, take_length, reverse_cons],
    rw [length_append, length_reverse], refl }
end

@[simp] lemma update_nth_eq_nil (l : list α) (n : ℕ) (a : α) : l.update_nth n a = [] ↔ l = [] :=
by cases l; cases n; simp only [update_nth]

section take'
variable [inhabited α]

@[simp] theorem take'_length : ∀ n l, length (@take' α _ n l) = n
| 0     l := rfl
| (n+1) l := congr_arg succ (take'_length _ _)

@[simp] theorem take'_nil : ∀ n, take' n (@nil α) = repeat default n
| 0     := rfl
| (n+1) := congr_arg (cons _) (take'_nil _)

theorem take'_eq_take : ∀ {n} {l : list α},
  n ≤ length l → take' n l = take n l
| 0     l      h := rfl
| (n+1) (a::l) h := congr_arg (cons _) $
  take'_eq_take $ le_of_succ_le_succ h

@[simp] theorem take'_left (l₁ l₂ : list α) : take' (length l₁) (l₁ ++ l₂) = l₁ :=
(take'_eq_take (by simp only [length_append, nat.le_add_right])).trans (take_left _ _)

theorem take'_left' {l₁ l₂ : list α} {n} (h : length l₁ = n) :
  take' n (l₁ ++ l₂) = l₁ :=
by rw ← h; apply take'_left

end take'

/-! ### foldl, foldr -/

lemma foldl_ext (f g : α → β → α) (a : α)
  {l : list β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
  foldl f a l = foldl g a l :=
begin
  induction l with hd tl ih generalizing a, {refl},
  unfold foldl,
  rw [ih (λ a b bin, H a b $ mem_cons_of_mem _ bin), H a hd (mem_cons_self _ _)]
end

lemma foldr_ext (f g : α → β → β) (b : β)
  {l : list α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
  foldr f b l = foldr g b l :=
begin
  induction l with hd tl ih, {refl},
  simp only [mem_cons_iff, or_imp_distrib, forall_and_distrib, forall_eq] at H,
  simp only [foldr, ih H.2, H.1]
end

@[simp] theorem foldl_nil (f : α → β → α) (a : α) : foldl f a [] = a := rfl

@[simp] theorem foldl_cons (f : α → β → α) (a : α) (b : β) (l : list β) :
  foldl f a (b::l) = foldl f (f a b) l := rfl

@[simp] theorem foldr_nil (f : α → β → β) (b : β) : foldr f b [] = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  foldr f b (a::l) = f a (foldr f b l) := rfl

@[simp] theorem foldl_append (f : α → β → α) :
  ∀ (a : α) (l₁ l₂ : list β), foldl f a (l₁++l₂) = foldl f (foldl f a l₁) l₂
| a []      l₂ := rfl
| a (b::l₁) l₂ := by simp only [cons_append, foldl_cons, foldl_append (f a b) l₁ l₂]

@[simp] theorem foldr_append (f : α → β → β) :
  ∀ (b : β) (l₁ l₂ : list α), foldr f b (l₁++l₂) = foldr f (foldr f b l₂) l₁
| b []      l₂ := rfl
| b (a::l₁) l₂ := by simp only [cons_append, foldr_cons, foldr_append b l₁ l₂]

@[simp] theorem foldl_join (f : α → β → α) :
  ∀ (a : α) (L : list (list β)), foldl f a (join L) = foldl (foldl f) a L
| a []     := rfl
| a (l::L) := by simp only [join, foldl_append, foldl_cons, foldl_join (foldl f a l) L]

@[simp] theorem foldr_join (f : α → β → β) :
  ∀ (b : β) (L : list (list α)), foldr f b (join L) = foldr (λ l b, foldr f b l) b L
| a []     := rfl
| a (l::L) := by simp only [join, foldr_append, foldr_join a L, foldr_cons]

theorem foldl_reverse (f : α → β → α) (a : α) (l : list β) :
  foldl f a (reverse l) = foldr (λx y, f y x) a l :=
by induction l; [refl, simp only [*, reverse_cons, foldl_append, foldl_cons, foldl_nil, foldr]]

theorem foldr_reverse (f : α → β → β) (a : β) (l : list α) :
  foldr f a (reverse l) = foldl (λx y, f y x) a l :=
let t := foldl_reverse (λx y, f y x) a (reverse l) in
by rw reverse_reverse l at t; rwa t

@[simp] theorem foldr_eta : ∀ (l : list α), foldr cons [] l = l
| []     := rfl
| (x::l) := by simp only [foldr_cons, foldr_eta l]; split; refl

@[simp] theorem reverse_foldl {l : list α} : reverse (foldl (λ t h, h :: t) [] l) = l :=
by rw ←foldr_reverse; simp

@[simp] theorem foldl_map (g : β → γ) (f : α → γ → α) (a : α) (l : list β) :
  foldl f a (map g l) = foldl (λx y, f x (g y)) a l :=
by revert a; induction l; intros; [refl, simp only [*, map, foldl]]

@[simp] theorem foldr_map (g : β → γ) (f : γ → α → α) (a : α) (l : list β) :
  foldr f a (map g l) = foldr (f ∘ g) a l :=
by revert a; induction l; intros; [refl, simp only [*, map, foldr]]

theorem foldl_map' {α β: Type u} (g : α → β) (f : α → α → α) (f' : β → β → β)
  (a : α) (l : list α) (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
  list.foldl f' (g a) (l.map g) = g (list.foldl f a l) :=
begin
  induction l generalizing a,
  { simp }, { simp [l_ih, h] }
end

theorem foldr_map' {α β: Type u} (g : α → β) (f : α → α → α) (f' : β → β → β)
  (a : α) (l : list α) (h : ∀ x y, f' (g x) (g y) = g (f x y)) :
  list.foldr f' (g a) (l.map g) = g (list.foldr f a l) :=
begin
  induction l generalizing a,
  { simp }, { simp [l_ih, h] }
end

theorem foldl_hom (l : list γ) (f : α → β) (op : α → γ → α) (op' : β → γ → β) (a : α)
  (h : ∀a x, f (op a x) = op' (f a) x) : foldl op' (f a) l = f (foldl op a l) :=
eq.symm $ by { revert a, induction l; intros; [refl, simp only [*, foldl]] }

theorem foldr_hom (l : list γ) (f : α → β) (op : γ → α → α) (op' : γ → β → β) (a : α)
  (h : ∀x a, f (op x a) = op' x (f a)) : foldr op' (f a) l = f (foldr op a l) :=
by { revert a, induction l; intros; [refl, simp only [*, foldr]] }

lemma foldl_hom₂ (l : list ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β) (op₃ : γ → ι → γ)
  (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
  foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
eq.symm $ by { revert a b, induction l; intros; [refl, simp only [*, foldl]] }

lemma foldr_hom₂ (l : list ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β) (op₃ : ι → γ → γ)
  (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
  foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) :=
by { revert a, induction l; intros; [refl, simp only [*, foldr]] }

lemma injective_foldl_comp {α : Type*} {l : list (α → α)} {f : α → α}
  (hl : ∀ f ∈ l, function.injective f) (hf : function.injective f):
  function.injective (@list.foldl (α → α) (α → α) function.comp f l) :=
begin
  induction l generalizing f,
  { exact hf },
  { apply l_ih (λ _ h, hl _ (list.mem_cons_of_mem _ h)),
    apply function.injective.comp hf,
    apply hl _ (list.mem_cons_self _ _) }
end

/-- Induction principle for values produced by a `foldr`: if a property holds
for the seed element `b : β` and for all incremental `op : α → β → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldr_rec_on {C : β → Sort*} (l : list α) (op : α → β → β) (b : β) (hb : C b)
  (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op a b)) :
  C (foldr op b l) :=
begin
  induction l with hd tl IH,
  { exact hb },
  { refine hl _ _ hd (mem_cons_self hd tl),
    refine IH _,
    intros y hy x hx,
    exact hl y hy x (mem_cons_of_mem hd hx) }
end

/-- Induction principle for values produced by a `foldl`: if a property holds
for the seed element `b : β` and for all incremental `op : β → α → β`
performed on the elements `(a : α) ∈ l`. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
def foldl_rec_on {C : β → Sort*} (l : list α) (op : β → α → β) (b : β) (hb : C b)
  (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ l), C (op b a)) :
  C (foldl op b l) :=
begin
  induction l with hd tl IH generalizing b,
  { exact hb },
  { refine IH _ _ _,
    { intros y hy x hx,
      exact hl y hy x (mem_cons_of_mem hd hx) },
    { exact hl b hb hd (mem_cons_self hd tl) } }
end

@[simp] lemma foldr_rec_on_nil {C : β → Sort*} (op : α → β → β) (b) (hb : C b) (hl) :
  foldr_rec_on [] op b hb hl = hb := rfl

@[simp] lemma foldr_rec_on_cons {C : β → Sort*} (x : α) (l : list α)
  (op : α → β → β) (b) (hb : C b)
  (hl : ∀ (b : β) (hb : C b) (a : α) (ha : a ∈ (x :: l)), C (op a b)) :
  foldr_rec_on (x :: l) op b hb hl = hl _ (foldr_rec_on l op b hb
    (λ b hb a ha, hl b hb a (mem_cons_of_mem _ ha))) x (mem_cons_self _ _) := rfl

@[simp] lemma foldl_rec_on_nil {C : β → Sort*} (op : β → α → β) (b) (hb : C b) (hl) :
  foldl_rec_on [] op b hb hl = hb := rfl

/- scanl -/

section scanl

variables {f : β → α → β} {b : β} {a : α} {l : list α}

lemma length_scanl :
  ∀ a l, length (scanl f a l) = l.length + 1
| a [] := rfl
| a (x :: l) := by erw [length_cons, length_cons, length_scanl]

@[simp] lemma scanl_nil (b : β) : scanl f b nil = [b] := rfl

@[simp] lemma scanl_cons :
  scanl f b (a :: l) = [b] ++ scanl f (f b a) l :=
by simp only [scanl, eq_self_iff_true, singleton_append, and_self]

@[simp] lemma nth_zero_scanl : (scanl f b l).nth 0 = some b :=
begin
  cases l,
  { simp only [nth, scanl_nil] },
  { simp only [nth, scanl_cons, singleton_append] }
end

@[simp] lemma nth_le_zero_scanl {h : 0 < (scanl f b l).length} :
  (scanl f b l).nth_le 0 h = b :=
begin
  cases l,
  { simp only [nth_le, scanl_nil] },
  { simp only [nth_le, scanl_cons, singleton_append] }
end

lemma nth_succ_scanl {i : ℕ} :
  (scanl f b l).nth (i + 1) = ((scanl f b l).nth i).bind (λ x, (l.nth i).map (λ y, f x y)) :=
begin
  induction l with hd tl hl generalizing b i,
  { symmetry,
    simp only [option.bind_eq_none', nth, forall_2_true_iff, not_false_iff, option.map_none',
               scanl_nil, option.not_mem_none, forall_true_iff] },
  { simp only [nth, scanl_cons, singleton_append],
    cases i,
    { simp only [option.map_some', nth_zero_scanl, nth, option.some_bind'] },
    { simp only [hl, nth] } }
end

lemma nth_le_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
  (scanl f b l).nth_le (i + 1) h =
  f ((scanl f b l).nth_le i (nat.lt_of_succ_lt h))
    (l.nth_le i (nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l))))) :=
begin
  induction i with i hi generalizing b l,
  { cases l,
    { simp only [length, zero_add, scanl_nil] at h,
      exact absurd h (lt_irrefl 1) },
    { simp only [scanl_cons, singleton_append, nth_le_zero_scanl, nth_le] } },
  { cases l,
    { simp only [length, add_lt_iff_neg_right, scanl_nil] at h,
      exact absurd h (not_lt_of_lt nat.succ_pos') },
    { simp_rw scanl_cons,
      rw nth_le_append_right _,
      { simpa only [hi, length, succ_add_sub_one] },
      { simp only [length, nat.zero_le, le_add_iff_nonneg_left] } } }
end

end scanl

/- scanr -/

@[simp] theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] := rfl

@[simp] theorem scanr_aux_cons (f : α → β → β) (b : β) : ∀ (a : α) (l : list α),
  scanr_aux f b (a::l) = (foldr f b (a::l), scanr f b l)
| a []     := rfl
| a (x::l) := let t := scanr_aux_cons x l in
  by simp only [scanr, scanr_aux, t, foldr_cons]

@[simp] theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : list α) :
  scanr f b (a::l) = foldr f b (a::l) :: scanr f b l :=
by simp only [scanr, scanr_aux_cons, foldr_cons]; split; refl

section foldl_eq_foldr
-- foldl and foldr coincide when f is commutative and associative
variables {f : α → α → α} (hcomm : commutative f) (hassoc : associative f)

include hassoc
theorem foldl1_eq_foldr1 : ∀ a b l, foldl f a (l++[b]) = foldr f b (a::l)
| a b nil      := rfl
| a b (c :: l) :=
  by simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l]; rw hassoc

include hcomm
theorem foldl_eq_of_comm_of_assoc : ∀ a b l, foldl f a (b::l) = f b (foldl f a l)
| a b  nil    := hcomm a b
| a b  (c::l) := by simp only [foldl_cons];
  rw [← foldl_eq_of_comm_of_assoc, right_comm _ hcomm hassoc]; refl

theorem foldl_eq_foldr : ∀ a l, foldl f a l = foldr f a l
| a nil      := rfl
| a (b :: l) :=
  by simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc]; rw (foldl_eq_foldr a l)

end foldl_eq_foldr

section foldl_eq_foldlr'

variables {f : α → β → α}
variables hf : ∀ a b c, f (f a b) c = f (f a c) b
include hf

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b::l) = f (foldl f a l) b
| a b [] := rfl
| a b (c :: l) := by rw [foldl,foldl,foldl,← foldl_eq_of_comm',foldl,hf]

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
| a [] := rfl
| a (b :: l) := by rw [foldl_eq_of_comm' hf,foldr,foldl_eq_foldr']; refl

end foldl_eq_foldlr'

section foldl_eq_foldlr'

variables {f : α → β → β}
variables hf : ∀ a b c, f a (f b c) = f b (f a c)
include hf

theorem foldr_eq_of_comm' : ∀ a b l, foldr f a (b::l) = foldr f (f b a) l
| a b [] := rfl
| a b (c :: l) := by rw [foldr,foldr,foldr,hf,← foldr_eq_of_comm']; refl

end foldl_eq_foldlr'

section
variables {op : α → α → α} [ha : is_associative α op] [hc : is_commutative α op]
local notation a * b := op a b
local notation l <*> a := foldl op a l

include ha

lemma foldl_assoc : ∀ {l : list α} {a₁ a₂}, l <*> (a₁ * a₂) = a₁ * (l <*> a₂)
| [] a₁ a₂ := rfl
| (a :: l) a₁ a₂ :=
  calc a::l <*> (a₁ * a₂) = l <*> (a₁ * (a₂ * a)) : by simp only [foldl_cons, ha.assoc]
    ... = a₁ * (a::l <*> a₂) : by rw [foldl_assoc, foldl_cons]

lemma foldl_op_eq_op_foldr_assoc : ∀{l : list α} {a₁ a₂}, (l <*> a₁) * a₂ = a₁ * l.foldr (*) a₂
| [] a₁ a₂ := rfl
| (a :: l) a₁ a₂ := by simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc];
  rw [foldl_op_eq_op_foldr_assoc]

include hc

lemma foldl_assoc_comm_cons {l : list α} {a₁ a₂} : (a₁ :: l) <*> a₂ = a₁ * (l <*> a₂) :=
by rw [foldl_cons, hc.comm, foldl_assoc]

end

/-! ### mfoldl, mfoldr, mmap -/

section mfoldl_mfoldr
variables {m : Type v → Type w} [monad m]

@[simp] theorem mfoldl_nil (f : β → α → m β) {b} : mfoldl f b [] = pure b := rfl

@[simp] theorem mfoldr_nil (f : α → β → m β) {b} : mfoldr f b [] = pure b := rfl

@[simp] theorem mfoldl_cons {f : β → α → m β} {b a l} :
  mfoldl f b (a :: l) = f b a >>= λ b', mfoldl f b' l := rfl

@[simp] theorem mfoldr_cons {f : α → β → m β} {b a l} :
  mfoldr f b (a :: l) = mfoldr f b l >>= f a := rfl

theorem mfoldr_eq_foldr (f : α → β → m β) (b l) :
  mfoldr f b l = foldr (λ a mb, mb >>= f a) (pure b) l :=
by induction l; simp *

attribute [simp] mmap mmap'

variables [is_lawful_monad m]

theorem mfoldl_eq_foldl (f : β → α → m β) (b l) :
  mfoldl f b l = foldl (λ mb a, mb >>= λ b, f b a) (pure b) l :=
begin
  suffices h : ∀ (mb : m β),
    (mb >>= λ b, mfoldl f b l) = foldl (λ mb a, mb >>= λ b, f b a) mb l,
  by simp [←h (pure b)],
  induction l; intro,
  { simp },
  { simp only [mfoldl, foldl, ←l_ih] with functor_norm }
end

@[simp] theorem mfoldl_append {f : β → α → m β} : ∀ {b l₁ l₂},
  mfoldl f b (l₁ ++ l₂) = mfoldl f b l₁ >>= λ x, mfoldl f x l₂
| _ []     _ := by simp only [nil_append, mfoldl_nil, pure_bind]
| _ (_::_) _ := by simp only [cons_append, mfoldl_cons, mfoldl_append, is_lawful_monad.bind_assoc]

@[simp] theorem mfoldr_append {f : α → β → m β} : ∀ {b l₁ l₂},
  mfoldr f b (l₁ ++ l₂) = mfoldr f b l₂ >>= λ x, mfoldr f x l₁
| _ []     _ := by simp only [nil_append, mfoldr_nil, bind_pure]
| _ (_::_) _ := by simp only [mfoldr_cons, cons_append, mfoldr_append, is_lawful_monad.bind_assoc]

end mfoldl_mfoldr

/-! ### intersperse -/
@[simp] lemma intersperse_nil {α : Type u} (a : α) : intersperse a [] = [] := rfl

@[simp] lemma intersperse_singleton {α : Type u} (a b : α) : intersperse a [b] = [b] := rfl

@[simp] lemma intersperse_cons_cons {α : Type u} (a b c : α) (tl : list α) :
  intersperse a (b :: c :: tl) = b :: a :: intersperse a (c :: tl) := rfl

/-! ### split_at and split_on -/

@[simp] theorem split_at_eq_take_drop : ∀ (n : ℕ) (l : list α), split_at n l = (take n l, drop n l)
| 0        a         := rfl
| (succ n) []        := rfl
| (succ n) (x :: xs) := by simp only [split_at, split_at_eq_take_drop n xs, take, drop]

@[simp] lemma split_on_nil {α : Type u} [decidable_eq α] (a : α) : [].split_on a = [[]] := rfl

/-- An auxiliary definition for proving a specification lemma for `split_on_p`.

`split_on_p_aux' P xs ys` splits the list `ys ++ xs` at every element satisfying `P`,
where `ys` is an accumulating parameter for the initial segment of elements not satisfying `P`.
-/
def split_on_p_aux' {α : Type u} (P : α → Prop) [decidable_pred P] : list α → list α → list (list α)
| [] xs       := [xs]
| (h :: t) xs :=
  if P h then xs :: split_on_p_aux' t []
  else split_on_p_aux' t (xs ++ [h])

lemma split_on_p_aux_eq {α : Type u} (P : α → Prop) [decidable_pred P] (xs ys : list α) :
  split_on_p_aux' P xs ys = split_on_p_aux P xs ((++) ys) :=
begin
  induction xs with a t ih generalizing ys; simp! only [append_nil, eq_self_iff_true, and_self],
  split_ifs; rw ih,
  { refine ⟨rfl, rfl⟩ },
  { congr, ext, simp }
end

lemma split_on_p_aux_nil {α : Type u} (P : α → Prop) [decidable_pred P] (xs : list α) :
  split_on_p_aux P xs id = split_on_p_aux' P xs [] :=
by { rw split_on_p_aux_eq, refl }

/-- The original list `L` can be recovered by joining the lists produced by `split_on_p p L`,
interspersed with the elements `L.filter p`. -/
lemma split_on_p_spec {α : Type u} (p : α → Prop) [decidable_pred p] (as : list α) :
  join (zip_with (++) (split_on_p p as) ((as.filter p).map (λ x, [x]) ++ [[]])) = as :=
begin
  rw [split_on_p, split_on_p_aux_nil],
  suffices : ∀ xs,
    join (zip_with (++) (split_on_p_aux' p as xs) ((as.filter p).map(λ x, [x]) ++ [[]])) = xs ++ as,
  { rw this, refl },
  induction as; intro; simp! only [split_on_p_aux', append_nil],
  split_ifs; simp [zip_with, join, *],
end

/-! ### map for partial functions -/

/-- Partial map. If `f : Π a, p a → β` is a partial function defined on
  `a : α` satisfying `p`, then `pmap f l h` is essentially the same as `map f l`
  but is defined only when all members of `l` satisfy `p`, using the proof
  to apply `f`. -/
@[simp] def pmap {p : α → Prop} (f : Π a, p a → β) : Π l : list α, (∀ a ∈ l, p a) → list β
| []     H := []
| (a::l) H := f a (forall_mem_cons.1 H).1 :: pmap l (forall_mem_cons.1 H).2

/-- "Attach" the proof that the elements of `l` are in `l` to produce a new list
  with the same elements but in the type `{x // x ∈ l}`. -/
def attach (l : list α) : list {x // x ∈ l} := pmap subtype.mk l (λ a, id)

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {l : list α} (hx : x ∈ l) :
  sizeof x < sizeof l :=
begin
  induction l with h t ih; cases hx,
  { rw hx, exact lt_add_of_lt_of_nonneg (lt_one_add _) (nat.zero_le _) },
  { exact lt_add_of_pos_of_le (zero_lt_one_add _) (le_of_lt (ih hx)) }
end

@[simp] theorem pmap_eq_map (p : α → Prop) (f : α → β) (l : list α) (H) :
  @pmap _ _ p (λ a _, f a) l H = map f l :=
by induction l; [refl, simp only [*, pmap, map]]; split; refl

theorem pmap_congr {p q : α → Prop} {f : Π a, p a → β} {g : Π a, q a → β}
  (l : list α) {H₁ H₂} (h : ∀ a h₁ h₂, f a h₁ = g a h₂) :
  pmap f l H₁ = pmap g l H₂ :=
by induction l with _ _ ih; [refl, rw [pmap, pmap, h, ih]]

theorem map_pmap {p : α → Prop} (g : β → γ) (f : Π a, p a → β)
  (l H) : map g (pmap f l H) = pmap (λ a h, g (f a h)) l H :=
by induction l; [refl, simp only [*, pmap, map]]; split; refl

theorem pmap_map {p : β → Prop} (g : ∀ b, p b → γ) (f : α → β)
  (l H) : pmap g (map f l) H = pmap (λ a h, g (f a) h) l (λ a h, H _ (mem_map_of_mem _ h)) :=
by induction l; [refl, simp only [*, pmap, map]]; split; refl

theorem pmap_eq_map_attach {p : α → Prop} (f : Π a, p a → β)
  (l H) : pmap f l H = l.attach.map (λ x, f x.1 (H _ x.2)) :=
by rw [attach, map_pmap]; exact pmap_congr l (λ a h₁ h₂, rfl)

theorem attach_map_val (l : list α) : l.attach.map subtype.val = l :=
by rw [attach, map_pmap]; exact (pmap_eq_map _ _ _ _).trans (map_id l)

@[simp] theorem mem_attach (l : list α) : ∀ x, x ∈ l.attach | ⟨a, h⟩ :=
by have := mem_map.1 (by rw [attach_map_val]; exact h);
   { rcases this with ⟨⟨_, _⟩, m, rfl⟩, exact m }

@[simp] theorem mem_pmap {p : α → Prop} {f : Π a, p a → β}
  {l H b} : b ∈ pmap f l H ↔ ∃ a (h : a ∈ l), f a (H a h) = b :=
by simp only [pmap_eq_map_attach, mem_map, mem_attach, true_and, subtype.exists]

@[simp] theorem length_pmap {p : α → Prop} {f : Π a, p a → β}
  {l H} : length (pmap f l H) = length l :=
by induction l; [refl, simp only [*, pmap, length]]

@[simp] lemma length_attach (L : list α) : L.attach.length = L.length := length_pmap

@[simp] lemma pmap_eq_nil {p : α → Prop} {f : Π a, p a → β}
  {l H} : pmap f l H = [] ↔ l = [] :=
by rw [← length_eq_zero, length_pmap, length_eq_zero]

@[simp] lemma attach_eq_nil (l : list α) : l.attach = [] ↔ l = [] := pmap_eq_nil

lemma last_pmap {α β : Type*} (p : α → Prop) (f : Π a, p a → β)
  (l : list α) (hl₁ : ∀ a ∈ l, p a) (hl₂ : l ≠ []) :
  (l.pmap f hl₁).last (mt list.pmap_eq_nil.1 hl₂) = f (l.last hl₂) (hl₁ _ (list.last_mem hl₂)) :=
begin
  induction l with l_hd l_tl l_ih,
  { apply (hl₂ rfl).elim },
  { cases l_tl,
    { simp },
    { apply l_ih } }
end

lemma nth_pmap {p : α → Prop} (f : Π a, p a → β) {l : list α} (h : ∀ a ∈ l, p a) (n : ℕ) :
  nth (pmap f l h) n = option.pmap f (nth l n) (λ x H, h x (nth_mem H)) :=
begin
  induction l with hd tl hl generalizing n,
  { simp },
  { cases n; simp [hl] }
end

lemma nth_le_pmap {p : α → Prop} (f : Π a, p a → β) {l : list α} (h : ∀ a ∈ l, p a) {n : ℕ}
  (hn : n < (pmap f l h).length) :
  nth_le (pmap f l h) n hn = f (nth_le l n (@length_pmap _ _ p f l h ▸ hn))
    (h _ (nth_le_mem l n (@length_pmap _ _ p f l h ▸ hn))) :=
begin
  induction l with hd tl hl generalizing n,
  { simp only [length, pmap] at hn,
    exact absurd hn (not_lt_of_le n.zero_le) },
  { cases n,
    { simp },
    { simpa [hl] } }
end

/-! ### find -/

section find
variables {p : α → Prop} [decidable_pred p] {l : list α} {a : α}

@[simp] theorem find_nil (p : α → Prop) [decidable_pred p] : find p [] = none :=
rfl

@[simp] theorem find_cons_of_pos (l) (h : p a) : find p (a::l) = some a :=
if_pos h

@[simp] theorem find_cons_of_neg (l) (h : ¬ p a) : find p (a::l) = find p l :=
if_neg h

@[simp] theorem find_eq_none : find p l = none ↔ ∀ x ∈ l, ¬ p x :=
begin
  induction l with a l IH,
  { exact iff_of_true rfl (forall_mem_nil _) },
  rw forall_mem_cons, by_cases h : p a,
  { simp only [find_cons_of_pos _ h, h, not_true, false_and] },
  { rwa [find_cons_of_neg _ h, iff_true_intro h, true_and] }
end

theorem find_some (H : find p l = some a) : p a :=
begin
  induction l with b l IH, {contradiction},
  by_cases h : p b,
  { rw find_cons_of_pos _ h at H, cases H, exact h },
  { rw find_cons_of_neg _ h at H, exact IH H }
end

@[simp] theorem find_mem (H : find p l = some a) : a ∈ l :=
begin
  induction l with b l IH, {contradiction},
  by_cases h : p b,
  { rw find_cons_of_pos _ h at H, cases H, apply mem_cons_self },
  { rw find_cons_of_neg _ h at H, exact mem_cons_of_mem _ (IH H) }
end

end find

/-! ### lookmap -/
section lookmap
variables (f : α → option α)

@[simp] theorem lookmap_nil : [].lookmap f = [] := rfl

@[simp] theorem lookmap_cons_none {a : α} (l : list α) (h : f a = none) :
  (a :: l).lookmap f = a :: l.lookmap f :=
by simp [lookmap, h]

@[simp] theorem lookmap_cons_some {a b : α} (l : list α) (h : f a = some b) :
  (a :: l).lookmap f = b :: l :=
by simp [lookmap, h]

theorem lookmap_some : ∀ l : list α, l.lookmap some = l
| []     := rfl
| (a::l) := rfl

theorem lookmap_none : ∀ l : list α, l.lookmap (λ _, none) = l
| []     := rfl
| (a::l) := congr_arg (cons a) (lookmap_none l)

theorem lookmap_congr {f g : α → option α} :
  ∀ {l : list α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
| []     H := rfl
| (a::l) H := begin
  cases forall_mem_cons.1 H with H₁ H₂,
  cases h : g a with b,
  { simp [h, H₁.trans h, lookmap_congr H₂] },
  { simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)] }
end

theorem lookmap_of_forall_not {l : list α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
(lookmap_congr H).trans (lookmap_none l)

theorem lookmap_map_eq (g : α → β) (h : ∀ a (b ∈ f a), g a = g b) :
  ∀ l : list α, map g (l.lookmap f) = map g l
| []     := rfl
| (a::l) := begin
  cases h' : f a with b,
  { simp [h', lookmap_map_eq] },
  { simp [lookmap_cons_some _ _ h', h _ _ h'] }
end

theorem lookmap_id' (h : ∀ a (b ∈ f a), a = b) (l : list α) : l.lookmap f = l :=
by rw [← map_id (l.lookmap f), lookmap_map_eq, map_id]; exact h

theorem length_lookmap (l : list α) : length (l.lookmap f) = length l :=
by rw [← length_map, lookmap_map_eq _ (λ _, ()), length_map]; simp

end lookmap

/-! ### filter_map -/

@[simp] theorem filter_map_nil (f : α → option β) : filter_map f [] = [] := rfl

@[simp] theorem filter_map_cons_none {f : α → option β} (a : α) (l : list α) (h : f a = none) :
  filter_map f (a :: l) = filter_map f l :=
by simp only [filter_map, h]

@[simp] theorem filter_map_cons_some (f : α → option β)
  (a : α) (l : list α) {b : β} (h : f a = some b) :
  filter_map f (a :: l) = b :: filter_map f l :=
by simp only [filter_map, h]; split; refl

theorem filter_map_cons (f : α → option β) (a : α) (l : list α) :
  filter_map f (a :: l) = option.cases_on (f a) (filter_map f l) (λb, b :: filter_map f l) :=
begin
  generalize eq : f a = b,
  cases b,
  { rw filter_map_cons_none _ _ eq },
  { rw filter_map_cons_some _ _ _ eq },
end

lemma filter_map_append {α β : Type*} (l l' : list α) (f : α → option β) :
  filter_map f (l ++ l') = filter_map f l ++ filter_map f l' :=
begin
  induction l with hd tl hl generalizing l',
  { simp },
  { rw [cons_append, filter_map, filter_map],
    cases f hd;
    simp only [filter_map, hl, cons_append, eq_self_iff_true, and_self] }
end

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
begin
  funext l,
  induction l with a l IH, {refl},
  simp only [filter_map_cons_some (some ∘ f) _ _ rfl, IH, map_cons], split; refl
end

theorem filter_map_eq_filter (p : α → Prop) [decidable_pred p] :
  filter_map (option.guard p) = filter p :=
begin
  funext l,
  induction l with a l IH, {refl},
  by_cases pa : p a,
  { simp only [filter_map, option.guard, IH, if_pos pa, filter_cons_of_pos _ pa], split; refl },
  { simp only [filter_map, option.guard, IH, if_neg pa, filter_cons_of_neg _ pa] }
end

theorem filter_map_filter_map (f : α → option β) (g : β → option γ) (l : list α) :
  filter_map g (filter_map f l) = filter_map (λ x, (f x).bind g) l :=
begin
  induction l with a l IH, {refl},
  cases h : f a with b,
  { rw [filter_map_cons_none _ _ h, filter_map_cons_none, IH],
    simp only [h, option.none_bind'] },
  rw filter_map_cons_some _ _ _ h,
  cases h' : g b with c;
  [ rw [filter_map_cons_none _ _ h', filter_map_cons_none, IH],
    rw [filter_map_cons_some _ _ _ h', filter_map_cons_some, IH] ];
  simp only [h, h', option.some_bind']
end

theorem map_filter_map (f : α → option β) (g : β → γ) (l : list α) :
  map g (filter_map f l) = filter_map (λ x, (f x).map g) l :=
by rw [← filter_map_eq_map, filter_map_filter_map]; refl

theorem filter_map_map (f : α → β) (g : β → option γ) (l : list α) :
  filter_map g (map f l) = filter_map (g ∘ f) l :=
by rw [← filter_map_eq_map, filter_map_filter_map]; refl

theorem filter_filter_map (f : α → option β) (p : β → Prop) [decidable_pred p] (l : list α) :
  filter p (filter_map f l) = filter_map (λ x, (f x).filter p) l :=
by rw [← filter_map_eq_filter, filter_map_filter_map]; refl

theorem filter_map_filter (p : α → Prop) [decidable_pred p] (f : α → option β) (l : list α) :
  filter_map f (filter p l) = filter_map (λ x, if p x then f x else none) l :=
begin
  rw [← filter_map_eq_filter, filter_map_filter_map], congr,
  funext x,
  show (option.guard p x).bind f = ite (p x) (f x) none,
  by_cases h : p x,
  { simp only [option.guard, if_pos h, option.some_bind'] },
  { simp only [option.guard, if_neg h, option.none_bind'] }
end

@[simp] theorem filter_map_some (l : list α) : filter_map some l = l :=
by rw filter_map_eq_map; apply map_id

@[simp] theorem mem_filter_map (f : α → option β) (l : list α) {b : β} :
  b ∈ filter_map f l ↔ ∃ a, a ∈ l ∧ f a = some b :=
begin
  induction l with a l IH,
  { split, { intro H, cases H }, { rintro ⟨_, H, _⟩, cases H } },
  cases h : f a with b',
  { have : f a ≠ some b, {rw h, intro, contradiction},
    simp only [filter_map_cons_none _ _ h, IH, mem_cons_iff,
      or_and_distrib_right, exists_or_distrib, exists_eq_left, this, false_or] },
  { have : f a = some b ↔ b = b',
    { split; intro t, {rw t at h; injection h}, {exact t.symm ▸ h} },
      simp only [filter_map_cons_some _ _ _ h, IH, mem_cons_iff,
        or_and_distrib_right, exists_or_distrib, this, exists_eq_left] }
end

theorem map_filter_map_of_inv (f : α → option β) (g : β → α)
  (H : ∀ x : α, (f x).map g = some x) (l : list α) :
  map g (filter_map f l) = l :=
by simp only [map_filter_map, H, filter_map_some]

theorem sublist.filter_map (f : α → option β) {l₁ l₂ : list α}
  (s : l₁ <+ l₂) : filter_map f l₁ <+ filter_map f l₂ :=
by induction s with l₁ l₂ a s IH l₁ l₂ a s IH;
   simp only [filter_map]; cases f a with b;
   simp only [filter_map, IH, sublist.cons, sublist.cons2]

theorem sublist.map (f : α → β) {l₁ l₂ : list α}
  (s : l₁ <+ l₂) : map f l₁ <+ map f l₂ :=
filter_map_eq_map f ▸ s.filter_map _

/-! ### reduce_option -/

@[simp] lemma reduce_option_cons_of_some (x : α) (l : list (option α)) :
  reduce_option (some x :: l) = x :: l.reduce_option :=
by simp only [reduce_option, filter_map, id.def, eq_self_iff_true, and_self]

@[simp] lemma reduce_option_cons_of_none (l : list (option α)) :
  reduce_option (none :: l) = l.reduce_option :=
by simp only [reduce_option, filter_map, id.def]

@[simp] lemma reduce_option_nil : @reduce_option α [] = [] := rfl

@[simp] lemma reduce_option_map {l : list (option α)} {f : α → β} :
  reduce_option (map (option.map f) l) = map f (reduce_option l) :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, map_nil] },
  { cases hd;
    simpa only [true_and, option.map_some', map, eq_self_iff_true,
                reduce_option_cons_of_some] using hl },
end

lemma reduce_option_append (l l' : list (option α)) :
  (l ++ l').reduce_option = l.reduce_option ++ l'.reduce_option :=
filter_map_append l l' id

lemma reduce_option_length_le (l : list (option α)) :
  l.reduce_option.length ≤ l.length :=
begin
  induction l with hd tl hl,
  { simp only [reduce_option_nil, length] },
  { cases hd,
    { exact nat.le_succ_of_le hl },
    { simpa only [length, add_le_add_iff_right, reduce_option_cons_of_some] using hl} }
end

lemma reduce_option_length_eq_iff {l : list (option α)} :
  l.reduce_option.length = l.length ↔ ∀ x ∈ l, option.is_some x :=
begin
  induction l with hd tl hl,
  { simp only [forall_const, reduce_option_nil, not_mem_nil,
               forall_prop_of_false, eq_self_iff_true, length, not_false_iff] },
  { cases hd,
    { simp only [mem_cons_iff, forall_eq_or_imp, bool.coe_sort_ff, false_and,
                 reduce_option_cons_of_none, length, option.is_some_none, iff_false],
      intro H,
      have := reduce_option_length_le tl,
      rw H at this,
      exact absurd (nat.lt_succ_self _) (not_lt_of_le this) },
    { simp only [hl, true_and, mem_cons_iff, forall_eq_or_imp, add_left_inj,
                 bool.coe_sort_tt, length, option.is_some_some, reduce_option_cons_of_some] } }
end

lemma reduce_option_length_lt_iff {l : list (option α)} :
  l.reduce_option.length < l.length ↔ none ∈ l :=
begin
  rw [(reduce_option_length_le l).lt_iff_ne, ne, reduce_option_length_eq_iff],
  induction l; simp *,
  rw [eq_comm, ← option.not_is_some_iff_eq_none, decidable.imp_iff_not_or]
end

lemma reduce_option_singleton (x : option α) :
  [x].reduce_option = x.to_list :=
by cases x; refl

lemma reduce_option_concat (l : list (option α)) (x : option α) :
  (l.concat x).reduce_option = l.reduce_option ++ x.to_list :=
begin
  induction l with hd tl hl generalizing x,
  { cases x;
    simp [option.to_list] },
  { simp only [concat_eq_append, reduce_option_append] at hl,
    cases hd;
    simp [hl, reduce_option_append] }
end

lemma reduce_option_concat_of_some (l : list (option α)) (x : α) :
  (l.concat (some x)).reduce_option = l.reduce_option.concat x :=
by simp only [reduce_option_nil, concat_eq_append, reduce_option_append, reduce_option_cons_of_some]

lemma reduce_option_mem_iff {l : list (option α)} {x : α} :
  x ∈ l.reduce_option ↔ (some x) ∈ l :=
by simp only [reduce_option, id.def, mem_filter_map, exists_eq_right]


lemma reduce_option_nth_iff {l : list (option α)} {x : α} :
  (∃ i, l.nth i = some (some x)) ↔ ∃ i, l.reduce_option.nth i = some x :=
by rw [←mem_iff_nth, ←mem_iff_nth, reduce_option_mem_iff]

/-! ### filter -/

section filter
variables {p : α → Prop} [decidable_pred p]

theorem filter_eq_foldr (p : α → Prop) [decidable_pred p] (l : list α) :
  filter p l = foldr (λ a out, if p a then a :: out else out) [] l :=
by induction l; simp [*, filter]

lemma filter_congr' {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  : ∀ {l : list α}, (∀ x ∈ l, p x ↔ q x) → filter p l = filter q l
| [] _     := rfl
| (a::l) h := by rw forall_mem_cons at h; by_cases pa : p a;
  [simp only [filter_cons_of_pos _ pa, filter_cons_of_pos _ (h.1.1 pa), filter_congr' h.2],
   simp only [filter_cons_of_neg _ pa, filter_cons_of_neg _ (mt h.1.2 pa), filter_congr' h.2]];
     split; refl

@[simp] theorem filter_subset (l : list α) : filter p l ⊆ l :=
(filter_sublist l).subset

theorem of_mem_filter {a : α} : ∀ {l}, a ∈ filter p l → p a
| (b::l) ain :=
  if pb : p b then
    have a ∈ b :: filter p l, by simpa only [filter_cons_of_pos _ pb] using ain,
    or.elim (eq_or_mem_of_mem_cons this)
      (assume : a = b, begin rw [← this] at pb, exact pb end)
      (assume : a ∈ filter p l, of_mem_filter this)
  else
    begin simp only [filter_cons_of_neg _ pb] at ain, exact (of_mem_filter ain) end

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
filter_subset l h

theorem mem_filter_of_mem {a : α} : ∀ {l}, a ∈ l → p a → a ∈ filter p l
| (_::l) (or.inl rfl) pa := by rw filter_cons_of_pos _ pa; apply mem_cons_self
| (b::l) (or.inr ain) pa := if pb : p b
    then by rw [filter_cons_of_pos _ pb]; apply mem_cons_of_mem; apply mem_filter_of_mem ain pa
    else by rw [filter_cons_of_neg _ pb]; apply mem_filter_of_mem ain pa

@[simp] theorem mem_filter {a : α} {l} : a ∈ filter p l ↔ a ∈ l ∧ p a :=
⟨λ h, ⟨mem_of_mem_filter h, of_mem_filter h⟩, λ ⟨h₁, h₂⟩, mem_filter_of_mem h₁ h₂⟩

lemma monotone_filter_left (p : α → Prop) [decidable_pred p]
  ⦃l l' : list α⦄ (h : l ⊆ l') : filter p l ⊆ filter p l' :=
begin
  intros x hx,
  rw [mem_filter] at hx ⊢,
  exact ⟨h hx.left, hx.right⟩
end

theorem filter_eq_self {l} : filter p l = l ↔ ∀ a ∈ l, p a :=
begin
  induction l with a l ih,
  { exact iff_of_true rfl (forall_mem_nil _) },
  rw forall_mem_cons, by_cases p a,
  { rw [filter_cons_of_pos _ h, cons_inj, ih, and_iff_right h] },
  { rw [filter_cons_of_neg _ h],
    refine iff_of_false _ (mt and.left h), intro e,
    have := filter_sublist l, rw e at this,
    exact not_lt_of_ge (length_le_of_sublist this) (lt_succ_self _) }
end

theorem filter_length_eq_length {l} : (filter p l).length = l.length ↔ ∀ a ∈ l, p a :=
iff.trans ⟨eq_of_sublist_of_length_eq l.filter_sublist, congr_arg list.length⟩ filter_eq_self

theorem filter_eq_nil {l} : filter p l = [] ↔ ∀ a ∈ l, ¬p a :=
by simp only [eq_nil_iff_forall_not_mem, mem_filter, not_and]

variable (p)
theorem sublist.filter {l₁ l₂} (s : l₁ <+ l₂) : filter p l₁ <+ filter p l₂ :=
filter_map_eq_filter p ▸ s.filter_map _

lemma monotone_filter_right (l : list α) ⦃p q : α → Prop⦄ [decidable_pred p] [decidable_pred q]
  (h : p ≤ q) : l.filter p <+ l.filter q :=
begin
  induction l with hd tl IH,
  { refl },
  { by_cases hp : p hd,
    { rw [filter_cons_of_pos _ hp, filter_cons_of_pos _ (h _ hp)],
      exact IH.cons_cons hd },
    { rw filter_cons_of_neg _ hp,
      by_cases hq : q hd,
      { rw filter_cons_of_pos _ hq,
        exact sublist_cons_of_sublist hd IH },
      { rw filter_cons_of_neg _ hq,
        exact IH } } }
end

theorem map_filter (f : β → α) (l : list β) :
  filter p (map f l) = map f (filter (p ∘ f) l) :=
by rw [← filter_map_eq_map, filter_filter_map, filter_map_filter]; refl

@[simp] theorem filter_filter (q) [decidable_pred q] : ∀ l,
  filter p (filter q l) = filter (λ a, p a ∧ q a) l
| [] := rfl
| (a :: l) := by by_cases hp : p a; by_cases hq : q a; simp only [hp, hq, filter, if_true, if_false,
    true_and, false_and, filter_filter l, eq_self_iff_true]

@[simp] lemma filter_true {h : decidable_pred (λ a : α, true)} (l : list α) :
  @filter α (λ _, true) h l = l :=
by convert filter_eq_self.2 (λ _ _, trivial)

@[simp] lemma filter_false {h : decidable_pred (λ a : α, false)} (l : list α) :
  @filter α (λ _, false) h l = [] :=
by convert filter_eq_nil.2 (λ _ _, id)

@[simp] theorem span_eq_take_drop : ∀ (l : list α), span p l = (take_while p l, drop_while p l)
| []     := rfl
| (a::l) :=
    if pa : p a then by simp only [span, if_pos pa, span_eq_take_drop l, take_while, drop_while]
    else by simp only [span, take_while, drop_while, if_neg pa]

@[simp] theorem take_while_append_drop : ∀ (l : list α), take_while p l ++ drop_while p l = l
| []     := rfl
| (a::l) := if pa : p a then by rw [take_while, drop_while, if_pos pa, if_pos pa, cons_append,
      take_while_append_drop l]
    else by rw [take_while, drop_while, if_neg pa, if_neg pa, nil_append]

end filter

/-! ### erasep -/
section erasep
variables {p : α → Prop} [decidable_pred p]

@[simp] theorem erasep_nil : [].erasep p = [] := rfl

theorem erasep_cons (a : α) (l : list α) :
  (a :: l).erasep p = if p a then l else a :: l.erasep p := rfl

@[simp] theorem erasep_cons_of_pos {a : α} {l : list α} (h : p a) : (a :: l).erasep p = l :=
by simp [erasep_cons, h]

@[simp] theorem erasep_cons_of_neg {a : α} {l : list α} (h : ¬ p a) :
  (a::l).erasep p = a :: l.erasep p :=
by simp [erasep_cons, h]

theorem erasep_of_forall_not {l : list α}
  (h : ∀ a ∈ l, ¬ p a) : l.erasep p = l :=
by induction l with _ _ ih; [refl,
  simp [h _ (or.inl rfl), ih (forall_mem_of_forall_mem_cons h)]]

theorem exists_of_erasep {l : list α} {a} (al : a ∈ l) (pa : p a) :
  ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
begin
  induction l with b l IH, {cases al},
  by_cases pb : p b,
  { exact ⟨b, [], l, forall_mem_nil _, pb, by simp [pb]⟩ },
  { rcases al with rfl | al, {exact pb.elim pa},
    rcases IH al with ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩,
    exact ⟨c, b::l₁, l₂, forall_mem_cons.2 ⟨pb, h₁⟩,
      h₂, by rw h₃; refl, by simp [pb, h₄]⟩ }
end

theorem exists_or_eq_self_of_erasep (p : α → Prop) [decidable_pred p] (l : list α) :
  l.erasep p = l ∨ ∃ a l₁ l₂, (∀ b ∈ l₁, ¬ p b) ∧ p a ∧ l = l₁ ++ a :: l₂ ∧ l.erasep p = l₁ ++ l₂ :=
begin
  by_cases h : ∃ a ∈ l, p a,
  { rcases h with ⟨a, ha, pa⟩,
    exact or.inr (exists_of_erasep ha pa) },
  { simp at h, exact or.inl (erasep_of_forall_not h) }
end

@[simp] theorem length_erasep_of_mem {l : list α} {a} (al : a ∈ l) (pa : p a) :
 length (l.erasep p) = pred (length l) :=
by rcases exists_of_erasep al pa with ⟨_, l₁, l₂, _, _, e₁, e₂⟩;
   rw e₂; simp [-add_comm, e₁]; refl

@[simp] lemma length_erasep_add_one {l : list α} {a} (al : a ∈ l) (pa : p a) :
  (l.erasep p).length + 1 = l.length :=
let ⟨_, l₁, l₂, _, _, h₁, h₂⟩ := exists_of_erasep al pa in
by { rw [h₂, h₁, length_append, length_append], refl }

theorem erasep_append_left {a : α} (pa : p a) :
  ∀ {l₁ : list α} (l₂), a ∈ l₁ → (l₁++l₂).erasep p = l₁.erasep p ++ l₂
| (x::xs) l₂ h := begin
  by_cases h' : p x; simp [h'],
  rw erasep_append_left l₂ (mem_of_ne_of_mem (mt _ h') h),
  rintro rfl, exact pa
end

theorem erasep_append_right :
  ∀ {l₁ : list α} (l₂), (∀ b ∈ l₁, ¬ p b) → (l₁++l₂).erasep p = l₁ ++ l₂.erasep p
| []      l₂ h := rfl
| (x::xs) l₂ h := by simp [(forall_mem_cons.1 h).1,
  erasep_append_right _ (forall_mem_cons.1 h).2]

theorem erasep_sublist (l : list α) : l.erasep p <+ l :=
by rcases exists_or_eq_self_of_erasep p l with h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩;
   [rw h, {rw [h₄, h₃], simp}]

theorem erasep_subset (l : list α) : l.erasep p ⊆ l :=
(erasep_sublist l).subset

theorem sublist.erasep {l₁ l₂ : list α} (s : l₁ <+ l₂) : l₁.erasep p <+ l₂.erasep p :=
begin
  induction s,
  case list.sublist.slnil { refl },
  case list.sublist.cons : l₁ l₂ a s IH
  { by_cases h : p a; simp [h],
    exacts [IH.trans (erasep_sublist _), IH.cons _ _ _] },
  case list.sublist.cons2 : l₁ l₂ a s IH
  { by_cases h : p a; simp [h],
    exacts [s, IH.cons2 _ _ _] }
end

theorem mem_of_mem_erasep {a : α} {l : list α} : a ∈ l.erasep p → a ∈ l :=
@erasep_subset _ _ _ _ _

@[simp] theorem mem_erasep_of_neg {a : α} {l : list α} (pa : ¬ p a) : a ∈ l.erasep p ↔ a ∈ l :=
⟨mem_of_mem_erasep, λ al, begin
  rcases exists_or_eq_self_of_erasep p l with h | ⟨c, l₁, l₂, h₁, h₂, h₃, h₄⟩,
  { rwa h },
  { rw h₄, rw h₃ at al,
    have : a ≠ c, {rintro rfl, exact pa.elim h₂},
    simpa [this] using al }
end⟩

theorem erasep_map (f : β → α) :
  ∀ (l : list β), (map f l).erasep p = map f (l.erasep (p ∘ f))
| []     := rfl
| (b::l) := by by_cases p (f b); simp [h, erasep_map l]

@[simp] theorem extractp_eq_find_erasep :
  ∀ l : list α, extractp p l = (find p l, erasep p l)
| []     := rfl
| (a::l) := by by_cases pa : p a; simp [extractp, pa, extractp_eq_find_erasep l]

end erasep

/-! ### erase -/
section erase
variable [decidable_eq α]

@[simp] theorem erase_nil (a : α) : [].erase a = [] := rfl

theorem erase_cons (a b : α) (l : list α) :
  (b :: l).erase a = if b = a then l else b :: l.erase a := rfl

@[simp] theorem erase_cons_head (a : α) (l : list α) : (a :: l).erase a = l :=
by simp only [erase_cons, if_pos rfl]

@[simp] theorem erase_cons_tail {a b : α} (l : list α) (h : b ≠ a) :
  (b::l).erase a = b :: l.erase a :=
by simp only [erase_cons, if_neg h]; split; refl

theorem erase_eq_erasep (a : α) (l : list α) : l.erase a = l.erasep (eq a) :=
by { induction l with b l, {refl},
  by_cases a = b; [simp [h], simp [h, ne.symm h, *]] }

@[simp, priority 980]
theorem erase_of_not_mem {a : α} {l : list α} (h : a ∉ l) : l.erase a = l :=
by rw [erase_eq_erasep, erasep_of_forall_not]; rintro b h' rfl; exact h h'

theorem exists_erase_eq {a : α} {l : list α} (h : a ∈ l) :
  ∃ l₁ l₂, a ∉ l₁ ∧ l = l₁ ++ a :: l₂ ∧ l.erase a = l₁ ++ l₂ :=
by rcases exists_of_erasep h rfl with ⟨_, l₁, l₂, h₁, rfl, h₂, h₃⟩;
   rw erase_eq_erasep; exact ⟨l₁, l₂, λ h, h₁ _ h rfl, h₂, h₃⟩

@[simp] theorem length_erase_of_mem {a : α} {l : list α} (h : a ∈ l) :
  length (l.erase a) = pred (length l) :=
by rw erase_eq_erasep; exact length_erasep_of_mem h rfl

@[simp] lemma length_erase_add_one {a : α} {l : list α} (h : a ∈ l) :
  (l.erase a).length + 1 = l.length :=
by rw [erase_eq_erasep, length_erasep_add_one h rfl]

theorem erase_append_left {a : α} {l₁ : list α} (l₂) (h : a ∈ l₁) :
  (l₁++l₂).erase a = l₁.erase a ++ l₂ :=
by simp [erase_eq_erasep]; exact erasep_append_left (by refl) l₂ h

theorem erase_append_right {a : α} {l₁ : list α} (l₂) (h : a ∉ l₁) :
  (l₁++l₂).erase a = l₁ ++ l₂.erase a :=
by rw [erase_eq_erasep, erase_eq_erasep, erasep_append_right];
   rintro b h' rfl; exact h h'

theorem erase_sublist (a : α) (l : list α) : l.erase a <+ l :=
by rw erase_eq_erasep; apply erasep_sublist

theorem erase_subset (a : α) (l : list α) : l.erase a ⊆ l :=
(erase_sublist a l).subset

theorem sublist.erase (a : α) {l₁ l₂ : list α} (h : l₁ <+ l₂) : l₁.erase a <+ l₂.erase a :=
by simp [erase_eq_erasep]; exact sublist.erasep h

theorem mem_of_mem_erase {a b : α} {l : list α} : a ∈ l.erase b → a ∈ l :=
@erase_subset _ _ _ _ _

@[simp] theorem mem_erase_of_ne {a b : α} {l : list α} (ab : a ≠ b) : a ∈ l.erase b ↔ a ∈ l :=
by rw erase_eq_erasep; exact mem_erasep_of_neg ab.symm

theorem erase_comm (a b : α) (l : list α) : (l.erase a).erase b = (l.erase b).erase a :=
if ab : a = b then by rw ab else
if ha : a ∈ l then
if hb : b ∈ l then match l, l.erase a, exists_erase_eq ha, hb with
| ._, ._, ⟨l₁, l₂, ha', rfl, rfl⟩, hb :=
  if h₁ : b ∈ l₁ then
    by rw [erase_append_left _ h₁, erase_append_left _ h₁,
           erase_append_right _ (mt mem_of_mem_erase ha'), erase_cons_head]
  else
    by rw [erase_append_right _ h₁, erase_append_right _ h₁, erase_append_right _ ha',
           erase_cons_tail _ ab, erase_cons_head]
end
else by simp only [erase_of_not_mem hb, erase_of_not_mem (mt mem_of_mem_erase hb)]
else by simp only [erase_of_not_mem ha, erase_of_not_mem (mt mem_of_mem_erase ha)]

theorem map_erase [decidable_eq β] {f : α → β} (finj : injective f) {a : α}
  (l : list α) : map f (l.erase a) = (map f l).erase (f a) :=
have this : eq a = eq (f a) ∘ f, { ext b, simp [finj.eq_iff] },
by simp [erase_eq_erasep, erase_eq_erasep, erasep_map, this]

theorem map_foldl_erase [decidable_eq β] {f : α → β} (finj : injective f) {l₁ l₂ : list α} :
  map f (foldl list.erase l₁ l₂) = foldl (λ l a, l.erase (f a)) (map f l₁) l₂ :=
by induction l₂ generalizing l₁; [refl,
simp only [foldl_cons, map_erase finj, *]]

end erase

/-! ### diff -/
section diff
variable [decidable_eq α]

@[simp] theorem diff_nil (l : list α) : l.diff [] = l := rfl

@[simp] theorem diff_cons (l₁ l₂ : list α) (a : α) : l₁.diff (a::l₂) = (l₁.erase a).diff l₂ :=
if h : a ∈ l₁ then by simp only [list.diff, if_pos h]
else by simp only [list.diff, if_neg h, erase_of_not_mem h]

lemma diff_cons_right (l₁ l₂ : list α) (a : α) : l₁.diff (a::l₂) = (l₁.diff l₂).erase a :=
begin
  induction l₂ with b l₂ ih generalizing l₁ a,
  { simp_rw [diff_cons, diff_nil] },
  { rw [diff_cons, diff_cons, erase_comm, ← diff_cons, ih, ← diff_cons] }
end

lemma diff_erase (l₁ l₂ : list α) (a : α) : (l₁.diff l₂).erase a = (l₁.erase a).diff l₂ :=
by rw [← diff_cons_right, diff_cons]

@[simp] theorem nil_diff (l : list α) : [].diff l = [] :=
by induction l; [refl, simp only [*, diff_cons, erase_of_not_mem (not_mem_nil _)]]

theorem diff_eq_foldl : ∀ (l₁ l₂ : list α), l₁.diff l₂ = foldl list.erase l₁ l₂
| l₁ []      := rfl
| l₁ (a::l₂) := (diff_cons l₁ l₂ a).trans (diff_eq_foldl _ _)

@[simp] theorem diff_append (l₁ l₂ l₃ : list α) : l₁.diff (l₂ ++ l₃) = (l₁.diff l₂).diff l₃ :=
by simp only [diff_eq_foldl, foldl_append]

@[simp] theorem map_diff [decidable_eq β] {f : α → β} (finj : injective f) {l₁ l₂ : list α} :
  map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) :=
by simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

theorem diff_sublist : ∀ l₁ l₂ : list α, l₁.diff l₂ <+ l₁
| l₁ []      := sublist.refl _
| l₁ (a::l₂) := calc l₁.diff (a :: l₂) = (l₁.erase a).diff l₂ : diff_cons _ _ _
  ... <+ l₁.erase a : diff_sublist _ _
  ... <+ l₁ : list.erase_sublist _ _

theorem diff_subset (l₁ l₂ : list α) : l₁.diff l₂ ⊆ l₁ :=
(diff_sublist _ _).subset

theorem mem_diff_of_mem {a : α} : ∀ {l₁ l₂ : list α}, a ∈ l₁ → a ∉ l₂ → a ∈ l₁.diff l₂
| l₁ []      h₁ h₂ := h₁
| l₁ (b::l₂) h₁ h₂ := by rw diff_cons; exact
  mem_diff_of_mem ((mem_erase_of_ne (ne_of_not_mem_cons h₂)).2 h₁) (not_mem_of_not_mem_cons h₂)

theorem sublist.diff_right : ∀ {l₁ l₂ l₃: list α}, l₁ <+ l₂ → l₁.diff l₃ <+ l₂.diff l₃
| l₁ l₂ [] h      := h
| l₁ l₂ (a::l₃) h := by simp only
  [diff_cons, (h.erase _).diff_right]

theorem erase_diff_erase_sublist_of_sublist {a : α} : ∀ {l₁ l₂ : list α},
  l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
| []      l₂ h := erase_sublist _ _
| (b::l₁) l₂ h := if heq : b = a then by simp only [heq, erase_cons_head, diff_cons]
                  else by simpa only [erase_cons_head, erase_cons_tail _ heq, diff_cons,
                    erase_comm a b l₂]
                  using erase_diff_erase_sublist_of_sublist (h.erase b)

end diff

/-! ### enum -/

theorem length_enum_from : ∀ n (l : list α), length (enum_from n l) = length l
| n []     := rfl
| n (a::l) := congr_arg nat.succ (length_enum_from _ _)

theorem length_enum : ∀ (l : list α), length (enum l) = length l := length_enum_from _

@[simp] theorem enum_from_nth : ∀ n (l : list α) m,
  nth (enum_from n l) m = (λ a, (n + m, a)) <$> nth l m
| n []       m     := rfl
| n (a :: l) 0     := rfl
| n (a :: l) (m+1) := (enum_from_nth (n+1) l m).trans $
  by rw [add_right_comm]; refl

@[simp] theorem enum_nth : ∀ (l : list α) n,
  nth (enum l) n = (λ a, (n, a)) <$> nth l n :=
by simp only [enum, enum_from_nth, zero_add]; intros; refl

@[simp] theorem enum_from_map_snd : ∀ n (l : list α),
  map prod.snd (enum_from n l) = l
| n []       := rfl
| n (a :: l) := congr_arg (cons _) (enum_from_map_snd _ _)

@[simp] theorem enum_map_snd : ∀ (l : list α),
  map prod.snd (enum l) = l := enum_from_map_snd _

theorem mem_enum_from {x : α} {i : ℕ} :
   ∀ {j : ℕ} (xs : list α), (i, x) ∈ xs.enum_from j → j ≤ i ∧ i < j + xs.length ∧ x ∈ xs
| j [] := by simp [enum_from]
| j (y :: ys) :=
suffices i = j ∧ x = y ∨ (i, x) ∈ enum_from (j + 1) ys →
    j ≤ i ∧ i < j + (length ys + 1) ∧ (x = y ∨ x ∈ ys),
  by simpa [enum_from, mem_enum_from ys],
begin
  rintro (h|h),
  { refine ⟨le_of_eq h.1.symm,h.1 ▸ _,or.inl h.2⟩,
    apply nat.lt_add_of_pos_right; simp },
  { obtain ⟨hji, hijlen, hmem⟩ := mem_enum_from _ h,
    refine ⟨_, _, _⟩,
    { exact le_trans (nat.le_succ _) hji },
    { convert hijlen using 1, ac_refl },
    { simp [hmem] } }
end

section choose
variables (p : α → Prop) [decidable_pred p] (l : list α)

lemma choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

/-! ### map₂_left' -/

section map₂_left'

-- The definitional equalities for `map₂_left'` can already be used by the
-- simplifie because `map₂_left'` is marked `@[simp]`.

@[simp] theorem map₂_left'_nil_right (f : α → option β → γ) (as) :
  map₂_left' f as [] = (as.map (λ a, f a none), []) :=
by cases as; refl

end map₂_left'

/-! ### map₂_right' -/

section map₂_right'

variables (f : option α → β → γ) (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem map₂_right'_nil_left :
  map₂_right' f [] bs = (bs.map (f none), []) :=
by cases bs; refl

@[simp] theorem map₂_right'_nil_right  :
  map₂_right' f as [] = ([], as) :=
rfl

@[simp] theorem map₂_right'_nil_cons :
  map₂_right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
rfl

@[simp] theorem map₂_right'_cons_cons :
  map₂_right' f (a :: as) (b :: bs) =
    let rec := map₂_right' f as bs in
    (f (some a) b :: rec.fst, rec.snd) :=
rfl

end map₂_right'

/-! ### zip_left' -/

section zip_left'

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_left'_nil_right :
  zip_left' as ([] : list β) = (as.map (λ a, (a, none)), []) :=
by cases as; refl

@[simp] theorem zip_left'_nil_left :
  zip_left' ([] : list α) bs = ([], bs) :=
rfl

@[simp] theorem zip_left'_cons_nil :
  zip_left' (a :: as) ([] : list β) = ((a, none) :: as.map (λ a, (a, none)), []) :=
rfl

@[simp] theorem zip_left'_cons_cons :
  zip_left' (a :: as) (b :: bs) =
    let rec := zip_left' as bs in
    ((a, some b) :: rec.fst, rec.snd) :=
rfl

end zip_left'

/-! ### zip_right' -/

section zip_right'

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_right'_nil_left :
  zip_right' ([] : list α) bs = (bs.map (λ b, (none, b)), []) :=
by cases bs; refl

@[simp] theorem zip_right'_nil_right :
  zip_right' as ([] : list β) = ([], as) :=
rfl

@[simp] theorem zip_right'_nil_cons :
  zip_right' ([] : list α) (b :: bs) = ((none, b) :: bs.map (λ b, (none, b)), []) :=
rfl

@[simp] theorem zip_right'_cons_cons :
  zip_right' (a :: as) (b :: bs) =
    let rec := zip_right' as bs in
    ((some a, b) :: rec.fst, rec.snd) :=
rfl

end zip_right'

/-! ### map₂_left -/

section map₂_left

variables (f : α → option β → γ) (as : list α)

-- The definitional equalities for `map₂_left` can already be used by the
-- simplifier because `map₂_left` is marked `@[simp]`.

@[simp] theorem map₂_left_nil_right :
  map₂_left f as [] = as.map (λ a, f a none) :=
by cases as; refl

theorem map₂_left_eq_map₂_left' : ∀ as bs,
  map₂_left f as bs = (map₂_left' f as bs).fst
| [] bs := by simp!
| (a :: as) [] := by simp!
| (a :: as) (b :: bs) := by simp! [*]

theorem map₂_left_eq_map₂ : ∀ as bs,
  length as ≤ length bs →
  map₂_left f as bs = map₂ (λ a b, f a (some b)) as bs
| [] [] h := by simp!
| [] (b :: bs) h := by simp!
| (a :: as) [] h := by { simp at h, contradiction }
| (a :: as) (b :: bs) h := by { simp at h, simp! [*] }

end map₂_left

/-! ### map₂_right -/

section map₂_right

variables (f : option α → β → γ) (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem map₂_right_nil_left :
  map₂_right f [] bs = bs.map (f none) :=
by cases bs; refl

@[simp] theorem map₂_right_nil_right :
  map₂_right f as [] = [] :=
rfl

@[simp] theorem map₂_right_nil_cons :
  map₂_right f [] (b :: bs) = f none b :: bs.map (f none) :=
rfl

@[simp] theorem map₂_right_cons_cons :
  map₂_right f (a :: as) (b :: bs) = f (some a) b :: map₂_right f as bs :=
rfl

theorem map₂_right_eq_map₂_right' :
  map₂_right f as bs = (map₂_right' f as bs).fst :=
by simp only [map₂_right, map₂_right', map₂_left_eq_map₂_left']

theorem map₂_right_eq_map₂ (h : length bs ≤ length as) :
  map₂_right f as bs = map₂ (λ a b, f (some a) b) as bs :=
begin
  have : (λ a b, flip f a (some b)) = (flip (λ a b, f (some a) b)) := rfl,
  simp only [map₂_right, map₂_left_eq_map₂, map₂_flip, *]
end

end map₂_right

/-! ### zip_left -/

section zip_left

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_left_nil_right :
  zip_left as ([] : list β) = as.map (λ a, (a, none)) :=
by cases as; refl

@[simp] theorem zip_left_nil_left :
  zip_left ([] : list α) bs = [] :=
rfl

@[simp] theorem zip_left_cons_nil :
  zip_left (a :: as) ([] : list β) = (a, none) :: as.map (λ a, (a, none)) :=
rfl

@[simp] theorem zip_left_cons_cons :
  zip_left (a :: as) (b :: bs) = (a, some b) :: zip_left as bs :=
rfl

theorem zip_left_eq_zip_left' :
  zip_left as bs = (zip_left' as bs).fst :=
by simp only [zip_left, zip_left', map₂_left_eq_map₂_left']

end zip_left

/-! ### zip_right -/

section zip_right

variables (a : α) (as : list α) (b : β) (bs : list β)

@[simp] theorem zip_right_nil_left :
  zip_right ([] : list α) bs = bs.map (λ b, (none, b)) :=
by cases bs; refl

@[simp] theorem zip_right_nil_right :
  zip_right as ([] : list β) = [] :=
rfl

@[simp] theorem zip_right_nil_cons :
  zip_right ([] : list α) (b :: bs) = (none, b) :: bs.map (λ b, (none, b)) :=
rfl

@[simp] theorem zip_right_cons_cons :
  zip_right (a :: as) (b :: bs) = (some a, b) :: zip_right as bs :=
rfl

theorem zip_right_eq_zip_right' :
  zip_right as bs = (zip_right' as bs).fst :=
by simp only [zip_right, zip_right', map₂_right_eq_map₂_right']

end zip_right

/-! ### to_chunks -/

section to_chunks

@[simp] theorem to_chunks_nil (n) : @to_chunks α n [] = [] := by cases n; refl

theorem to_chunks_aux_eq (n) : ∀ xs i,
  @to_chunks_aux α n xs i = (xs.take i, (xs.drop i).to_chunks (n+1))
| [] i := by cases i; refl
| (x::xs) 0 := by rw [to_chunks_aux, drop, to_chunks]; cases to_chunks_aux n xs n; refl
| (x::xs) (i+1) := by rw [to_chunks_aux, to_chunks_aux_eq]; refl

theorem to_chunks_eq_cons' (n) : ∀ {xs : list α} (h : xs ≠ []),
  xs.to_chunks (n+1) = xs.take (n+1) :: (xs.drop (n+1)).to_chunks (n+1)
| [] e := (e rfl).elim
| (x::xs) _ := by rw [to_chunks, to_chunks_aux_eq]; refl

theorem to_chunks_eq_cons : ∀ {n} {xs : list α} (n0 : n ≠ 0) (x0 : xs ≠ []),
  xs.to_chunks n = xs.take n :: (xs.drop n).to_chunks n
| 0 _ e := (e rfl).elim
| (n+1) xs _ := to_chunks_eq_cons' _

theorem to_chunks_aux_join {n} : ∀ {xs i l L}, @to_chunks_aux α n xs i = (l, L) → l ++ L.join = xs
| [] _ _ _ rfl := rfl
| (x::xs) i l L e := begin
    cases i; [
      cases e' : to_chunks_aux n xs n with l L,
      cases e' : to_chunks_aux n xs i with l L];
    { rw [to_chunks_aux, e', to_chunks_aux] at e, cases e,
      exact (congr_arg (cons x) (to_chunks_aux_join e') : _) }
  end

@[simp] theorem to_chunks_join : ∀ n xs, (@to_chunks α n xs).join = xs
| n [] := by cases n; refl
| 0 (x::xs) := by simp only [to_chunks, join]; rw append_nil
| (n+1) (x::xs) := begin
    rw to_chunks,
    cases e : to_chunks_aux n xs n with l L,
    exact (congr_arg (cons x) (to_chunks_aux_join e) : _),
  end

theorem to_chunks_length_le : ∀ n xs, n ≠ 0 → ∀ l : list α,
  l ∈ @to_chunks α n xs → l.length ≤ n
| 0 _ e _ := (e rfl).elim
| (n+1) xs _ l := begin
  refine (measure_wf length).induction xs _, intros xs IH h,
  by_cases x0 : xs = [], {subst xs, cases h},
  rw to_chunks_eq_cons' _ x0 at h, rcases h with rfl|h,
  { apply length_take_le },
  { refine IH _ _ h,
    simp only [measure, inv_image, length_drop],
    exact tsub_lt_self (length_pos_iff_ne_nil.2 x0) (succ_pos _) },
end

end to_chunks

/-! ### Retroattributes

The list definitions happen earlier than `to_additive`, so here we tag the few multiplicative
definitions that couldn't be tagged earlier.
-/

attribute [to_additive] list.prod -- `list.sum`

attribute [to_additive] alternating_prod -- `list.alternating_sum`

/-! ### Miscellaneous lemmas -/

theorem ilast'_mem : ∀ a l, @ilast' α a l ∈ a :: l
| a []     := or.inl rfl
| a (b::l) := or.inr (ilast'_mem b l)

@[simp] lemma nth_le_attach (L : list α) (i) (H : i < L.attach.length) :
  (L.attach.nth_le i H).1 = L.nth_le i (length_attach L ▸ H) :=
calc  (L.attach.nth_le i H).1
    = (L.attach.map subtype.val).nth_le i (by simpa using H) : by rw nth_le_map'
... = L.nth_le i _ : by congr; apply attach_map_val

@[simp]
theorem mem_map_swap (x : α) (y : β) (xs : list (α × β)) :
  (y, x) ∈ map prod.swap xs ↔ (x, y) ∈ xs :=
begin
  induction xs with x xs,
  { simp only [not_mem_nil, map_nil] },
  { cases x with a b,
    simp only [mem_cons_iff, prod.mk.inj_iff, map, prod.swap_prod_mk,
      prod.exists, xs_ih, and_comm] },
end

lemma slice_eq (xs : list α) (n m : ℕ) :
  slice n m xs = xs.take n ++ xs.drop (n+m) :=
begin
  induction n generalizing xs,
  { simp [slice] },
  { cases xs; simp [slice, *, nat.succ_add], }
end

lemma sizeof_slice_lt [has_sizeof α] (i j : ℕ) (hj : 0 < j) (xs : list α) (hi : i < xs.length) :
  sizeof (list.slice i j xs) < sizeof xs :=
begin
  induction xs generalizing i j,
  case list.nil : i j h
  { cases hi },
  case list.cons : x xs xs_ih i j h
  { cases i; simp only [-slice_eq, list.slice],
    { cases j, cases h,
      dsimp only [drop], unfold_wf,
      apply @lt_of_le_of_lt _ _ _ xs.sizeof,
      { clear_except,
        induction xs generalizing j; unfold_wf,
        case list.nil : j
        { refl },
        case list.cons : xs_hd xs_tl xs_ih j
        { cases j; unfold_wf, refl,
          transitivity, apply xs_ih,
          simp }, },
      unfold_wf, apply zero_lt_one_add, },
    { unfold_wf, apply xs_ih _ _ h,
      apply lt_of_succ_lt_succ hi, } },
end

end list
