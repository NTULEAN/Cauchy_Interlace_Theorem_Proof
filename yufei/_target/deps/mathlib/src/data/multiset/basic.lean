/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.bool.all_any
import data.list.perm

/-!
# Multisets
These are implemented as the quotient of a list by permutations.
## Notation
We define the global infix notation `::ₘ` for `multiset.cons`.
-/

open list subtype nat

variables {α : Type*} {β : Type*} {γ : Type*}

/-- `multiset α` is the quotient of `list α` by list permutation. The result
  is a type of finite sets with duplicates allowed.  -/
def {u} multiset (α : Type u) : Type u :=
quotient (list.is_setoid α)

namespace multiset

instance : has_coe (list α) (multiset α) := ⟨quot.mk _⟩

@[simp] theorem quot_mk_to_coe (l : list α) : @eq (multiset α) ⟦l⟧ l := rfl

@[simp] theorem quot_mk_to_coe' (l : list α) : @eq (multiset α) (quot.mk (≈) l) l := rfl

@[simp] theorem quot_mk_to_coe'' (l : list α) : @eq (multiset α) (quot.mk setoid.r l) l := rfl

@[simp] theorem coe_eq_coe {l₁ l₂ : list α} : (l₁ : multiset α) = l₂ ↔ l₁ ~ l₂ := quotient.eq

instance has_decidable_eq [decidable_eq α] : decidable_eq (multiset α)
| s₁ s₂ := quotient.rec_on_subsingleton₂ s₁ s₂ $ λ l₁ l₂,
  decidable_of_iff' _ quotient.eq

/-- defines a size for a multiset by referring to the size of the underlying list -/
protected def sizeof [has_sizeof α] (s : multiset α) : ℕ :=
quot.lift_on s sizeof $ λ l₁ l₂, perm.sizeof_eq_sizeof

instance has_sizeof [has_sizeof α] : has_sizeof (multiset α) := ⟨multiset.sizeof⟩

/-! ### Empty multiset -/

/-- `0 : multiset α` is the empty set -/
protected def zero : multiset α := @nil α

instance : has_zero (multiset α)   := ⟨multiset.zero⟩
instance : has_emptyc (multiset α) := ⟨0⟩
instance inhabited_multiset : inhabited (multiset α)  := ⟨0⟩

@[simp] theorem coe_nil_eq_zero : (@nil α : multiset α) = 0 := rfl
@[simp] theorem empty_eq_zero : (∅ : multiset α) = 0 := rfl

theorem coe_eq_zero (l : list α) : (l : multiset α) = 0 ↔ l = [] :=
iff.trans coe_eq_coe perm_nil

/-! ### `multiset.cons` -/

/-- `cons a s` is the multiset which contains `s` plus one more
  instance of `a`. -/
def cons (a : α) (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (a :: l : multiset α))
  (λ l₁ l₂ p, quot.sound (p.cons a))

infixr ` ::ₘ `:67  := multiset.cons

instance : has_insert α (multiset α) := ⟨cons⟩

@[simp] theorem insert_eq_cons (a : α) (s : multiset α) :
  insert a s = a ::ₘ s := rfl

@[simp] theorem cons_coe (a : α) (l : list α) :
  (a ::ₘ l : multiset α) = (a::l : list α) := rfl

theorem singleton_coe (a : α) : (a ::ₘ 0 : multiset α) = ([a] : list α) := rfl

@[simp] theorem cons_inj_left {a b : α} (s : multiset α) :
  a ::ₘ s = b ::ₘ s ↔ a = b :=
⟨quot.induction_on s $ λ l e,
  have [a] ++ l ~ [b] ++ l, from quotient.exact e,
  singleton_perm_singleton.1 $ (perm_append_right_iff _).1 this, congr_arg _⟩

@[simp] theorem cons_inj_right (a : α) : ∀{s t : multiset α}, a ::ₘ s = a ::ₘ t ↔ s = t :=
by rintros ⟨l₁⟩ ⟨l₂⟩; simp

@[recursor 5] protected theorem induction {p : multiset α → Prop}
  (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a ::ₘ s)) : ∀s, p s :=
by rintros ⟨l⟩; induction l with _ _ ih; [exact h₁, exact h₂ ih]

@[elab_as_eliminator] protected theorem induction_on {p : multiset α → Prop}
  (s : multiset α) (h₁ : p 0) (h₂ : ∀ ⦃a : α⦄ {s : multiset α}, p s → p (a ::ₘ s)) : p s :=
multiset.induction h₁ h₂ s

theorem cons_swap (a b : α) (s : multiset α) : a ::ₘ b ::ₘ s = b ::ₘ a ::ₘ s :=
quot.induction_on s $ λ l, quotient.sound $ perm.swap _ _ _

section rec
variables {C : multiset α → Sort*}

/-- Dependent recursor on multisets.
TODO: should be @[recursor 6], but then the definition of `multiset.pi` fails with a stack
overflow in `whnf`.
-/
protected def rec
  (C_0 : C 0)
  (C_cons : Πa m, C m → C (a ::ₘ m))
  (C_cons_heq : ∀ a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ==
    C_cons a' (a ::ₘ m) (C_cons a m b))
  (m : multiset α) : C m :=
quotient.hrec_on m (@list.rec α (λl, C ⟦l⟧) C_0 (λa l b, C_cons a ⟦l⟧ b)) $
  assume l l' h,
  h.rec_heq
    (assume a l l' b b' hl, have ⟦l⟧ = ⟦l'⟧, from quot.sound hl, by cc)
    (assume a a' l, C_cons_heq a a' ⟦l⟧)

/-- Companion to `multiset.rec` with more convenient argument order. -/
@[elab_as_eliminator]
protected def rec_on (m : multiset α)
  (C_0 : C 0)
  (C_cons : Πa m, C m → C (a ::ₘ m))
  (C_cons_heq : ∀a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ==
      C_cons a' (a ::ₘ m) (C_cons a m b)) :
  C m :=
multiset.rec C_0 C_cons C_cons_heq m

variables {C_0 : C 0} {C_cons : Πa m, C m → C (a ::ₘ m)}
  {C_cons_heq : ∀a a' m b, C_cons a (a' ::ₘ m) (C_cons a' m b) ==
    C_cons a' (a ::ₘ m) (C_cons a m b)}

@[simp] lemma rec_on_0 : @multiset.rec_on α C (0:multiset α) C_0 C_cons C_cons_heq = C_0 :=
rfl

@[simp] lemma rec_on_cons (a : α) (m : multiset α) :
  (a ::ₘ m).rec_on C_0 C_cons C_cons_heq = C_cons a m (m.rec_on C_0 C_cons C_cons_heq) :=
quotient.induction_on m $ assume l, rfl

end rec

section mem

/-- `a ∈ s` means that `a` has nonzero multiplicity in `s`. -/
def mem (a : α) (s : multiset α) : Prop :=
quot.lift_on s (λ l, a ∈ l) (λ l₁ l₂ (e : l₁ ~ l₂), propext $ e.mem_iff)

instance : has_mem α (multiset α) := ⟨mem⟩

@[simp] lemma mem_coe {a : α} {l : list α} : a ∈ (l : multiset α) ↔ a ∈ l := iff.rfl

instance decidable_mem [decidable_eq α] (a : α) (s : multiset α) : decidable (a ∈ s) :=
quot.rec_on_subsingleton s $ list.decidable_mem a

@[simp] theorem mem_cons {a b : α} {s : multiset α} : a ∈ b ::ₘ s ↔ a = b ∨ a ∈ s :=
quot.induction_on s $ λ l, iff.rfl

lemma mem_cons_of_mem {a b : α} {s : multiset α} (h : a ∈ s) : a ∈ b ::ₘ s :=
mem_cons.2 $ or.inr h

@[simp] theorem mem_cons_self (a : α) (s : multiset α) : a ∈ a ::ₘ s :=
mem_cons.2 (or.inl rfl)

theorem forall_mem_cons {p : α → Prop} {a : α} {s : multiset α} :
  (∀ x ∈ (a ::ₘ s), p x) ↔ p a ∧ ∀ x ∈ s, p x :=
quotient.induction_on' s $ λ L, list.forall_mem_cons

theorem exists_cons_of_mem {s : multiset α} {a : α} : a ∈ s → ∃ t, s = a ::ₘ t :=
quot.induction_on s $ λ l (h : a ∈ l),
let ⟨l₁, l₂, e⟩ := mem_split h in
e.symm ▸ ⟨(l₁++l₂ : list α), quot.sound perm_middle⟩

@[simp] theorem not_mem_zero (a : α) : a ∉ (0 : multiset α) := id

theorem eq_zero_of_forall_not_mem {s : multiset α} : (∀x, x ∉ s) → s = 0 :=
quot.induction_on s $ λ l H, by rw eq_nil_iff_forall_not_mem.mpr H; refl

theorem eq_zero_iff_forall_not_mem {s : multiset α} : s = 0 ↔ ∀ a, a ∉ s :=
⟨λ h, h.symm ▸ λ _, not_false, eq_zero_of_forall_not_mem⟩

theorem exists_mem_of_ne_zero {s : multiset α} : s ≠ 0 → ∃ a : α, a ∈ s :=
quot.induction_on s $ assume l hl,
  match l, hl with
  | [] := assume h, false.elim $ h rfl
  | (a :: l) := assume _, ⟨a, by simp⟩
  end

lemma empty_or_exists_mem (s : multiset α) : s = 0 ∨ ∃ a, a ∈ s :=
or_iff_not_imp_left.mpr multiset.exists_mem_of_ne_zero

@[simp] lemma zero_ne_cons {a : α} {m : multiset α} : 0 ≠ a ::ₘ m :=
assume h, have a ∈ (0:multiset α), from h.symm ▸ mem_cons_self _ _, not_mem_zero _ this

@[simp] lemma cons_ne_zero {a : α} {m : multiset α} : a ::ₘ m ≠ 0 := zero_ne_cons.symm

lemma cons_eq_cons {a b : α} {as bs : multiset α} :
  a ::ₘ as = b ::ₘ bs ↔ ((a = b ∧ as = bs) ∨ (a ≠ b ∧ ∃cs, as = b ::ₘ cs ∧ bs = a ::ₘ cs)) :=
begin
  haveI : decidable_eq α := classical.dec_eq α,
  split,
  { assume eq,
    by_cases a = b,
    { subst h, simp * at * },
    { have : a ∈ b ::ₘ bs, from eq ▸ mem_cons_self _ _,
      have : a ∈ bs, by simpa [h],
      rcases exists_cons_of_mem this with ⟨cs, hcs⟩,
      simp [h, hcs],
      have : a ::ₘ as = b ::ₘ a ::ₘ cs, by simp [eq, hcs],
      have : a ::ₘ as = a ::ₘ b ::ₘ cs, by rwa [cons_swap],
      simpa using this } },
  { assume h,
    rcases h with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
    { simp * },
    { simp [*, cons_swap a b] } }
end

end mem

/-! ### `multiset.subset` -/
section subset

/-- `s ⊆ t` is the lift of the list subset relation. It means that any
  element with nonzero multiplicity in `s` has nonzero multiplicity in `t`,
  but it does not imply that the multiplicity of `a` in `s` is less or equal than in `t`;
  see `s ≤ t` for this relation. -/
protected def subset (s t : multiset α) : Prop := ∀ ⦃a : α⦄, a ∈ s → a ∈ t

instance : has_subset (multiset α) := ⟨multiset.subset⟩

@[simp] theorem coe_subset {l₁ l₂ : list α} : (l₁ : multiset α) ⊆ l₂ ↔ l₁ ⊆ l₂ := iff.rfl

@[simp] theorem subset.refl (s : multiset α) : s ⊆ s := λ a h, h

theorem subset.trans {s t u : multiset α} : s ⊆ t → t ⊆ u → s ⊆ u :=
λ h₁ h₂ a m, h₂ (h₁ m)

theorem subset_iff {s t : multiset α} : s ⊆ t ↔ (∀⦃x⦄, x ∈ s → x ∈ t) := iff.rfl

theorem mem_of_subset {s t : multiset α} {a : α} (h : s ⊆ t) : a ∈ s → a ∈ t := @h _

@[simp] theorem zero_subset (s : multiset α) : 0 ⊆ s :=
λ a, (not_mem_nil a).elim

@[simp] theorem cons_subset {a : α} {s t : multiset α} : (a ::ₘ s) ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
by simp [subset_iff, or_imp_distrib, forall_and_distrib]

theorem eq_zero_of_subset_zero {s : multiset α} (h : s ⊆ 0) : s = 0 :=
eq_zero_of_forall_not_mem h

theorem subset_zero {s : multiset α} : s ⊆ 0 ↔ s = 0 :=
⟨eq_zero_of_subset_zero, λ xeq, xeq.symm ▸ subset.refl 0⟩

lemma induction_on' {p : multiset α → Prop} (S : multiset α)
  (h₁ : p ∅) (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → p s → p (insert a s)) : p S :=
@multiset.induction_on α (λ T, T ⊆ S → p T) S (λ _, h₁) (λ a s hps hs,
  let ⟨hS, sS⟩ := cons_subset.1 hs in h₂ hS sS (hps sS)) (subset.refl S)

end subset

section to_list

/-- Produces a list of the elements in the multiset using choice. -/
@[reducible] noncomputable def to_list {α : Type*} (s : multiset α) :=
classical.some (quotient.exists_rep s)

@[simp] lemma to_list_zero {α : Type*} : (multiset.to_list 0 : list α) = [] :=
(multiset.coe_eq_zero _).1 (classical.some_spec (quotient.exists_rep multiset.zero))

@[simp, norm_cast]
lemma coe_to_list {α : Type*} (s : multiset α) : (s.to_list : multiset α) = s :=
classical.some_spec (quotient.exists_rep _)

@[simp]
lemma mem_to_list {α : Type*} (a : α) (s : multiset α) : a ∈ s.to_list ↔ a ∈ s :=
by rw [←multiset.mem_coe, multiset.coe_to_list]

end to_list

/-! ### Partial order on `multiset`s -/

/-- `s ≤ t` means that `s` is a sublist of `t` (up to permutation).
  Equivalently, `s ≤ t` means that `count a s ≤ count a t` for all `a`. -/
protected def le (s t : multiset α) : Prop :=
quotient.lift_on₂ s t (<+~) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  propext (p₂.subperm_left.trans p₁.subperm_right)

instance : partial_order (multiset α) :=
{ le          := multiset.le,
  le_refl     := by rintros ⟨l⟩; exact subperm.refl _,
  le_trans    := by rintros ⟨l₁⟩ ⟨l₂⟩ ⟨l₃⟩; exact @subperm.trans _ _ _ _,
  le_antisymm := by rintros ⟨l₁⟩ ⟨l₂⟩ h₁ h₂; exact quot.sound (subperm.antisymm h₁ h₂) }

section
variables {s t : multiset α} {a : α}

lemma subset_of_le : s ≤ t → s ⊆ t := quotient.induction_on₂ s t $ λ l₁ l₂, subperm.subset

alias subset_of_le ← multiset.le.subset

lemma mem_of_le (h : s ≤ t) : a ∈ s → a ∈ t := mem_of_subset (subset_of_le h)

lemma not_mem_mono (h : s ⊆ t) : a ∉ t → a ∉ s := mt $ @h _

@[simp] theorem coe_le {l₁ l₂ : list α} : (l₁ : multiset α) ≤ l₂ ↔ l₁ <+~ l₂ := iff.rfl

@[elab_as_eliminator] theorem le_induction_on {C : multiset α → multiset α → Prop}
  {s t : multiset α} (h : s ≤ t)
  (H : ∀ {l₁ l₂ : list α}, l₁ <+ l₂ → C l₁ l₂) : C s t :=
quotient.induction_on₂ s t (λ l₁ l₂ ⟨l, p, s⟩,
  (show ⟦l⟧ = ⟦l₁⟧, from quot.sound p) ▸ H s) h

theorem zero_le (s : multiset α) : 0 ≤ s :=
quot.induction_on s $ λ l, (nil_sublist l).subperm

lemma le_zero : s ≤ 0 ↔ s = 0 := ⟨λ h, le_antisymm h (zero_le _), le_of_eq⟩

theorem lt_cons_self (s : multiset α) (a : α) : s < a ::ₘ s :=
quot.induction_on s $ λ l,
suffices l <+~ a :: l ∧ (¬l ~ a :: l),
  by simpa [lt_iff_le_and_ne],
⟨(sublist_cons _ _).subperm,
 λ p, ne_of_lt (lt_succ_self (length l)) p.length_eq⟩

theorem le_cons_self (s : multiset α) (a : α) : s ≤ a ::ₘ s :=
le_of_lt $ lt_cons_self _ _

lemma cons_le_cons_iff (a : α) : a ::ₘ s ≤ a ::ₘ t ↔ s ≤ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, subperm_cons a

lemma cons_le_cons (a : α) : s ≤ t → a ::ₘ s ≤ a ::ₘ t := (cons_le_cons_iff a).2

lemma le_cons_of_not_mem (m : a ∉ s) : s ≤ a ::ₘ t ↔ s ≤ t :=
begin
  refine ⟨_, λ h, le_trans h $ le_cons_self _ _⟩,
  suffices : ∀ {t'} (_ : s ≤ t') (_ : a ∈ t'), a ::ₘ s ≤ t',
  { exact λ h, (cons_le_cons_iff a).1 (this h (mem_cons_self _ _)) },
  introv h, revert m, refine le_induction_on h _,
  introv s m₁ m₂,
  rcases mem_split m₂ with ⟨r₁, r₂, rfl⟩,
  exact perm_middle.subperm_left.2 ((subperm_cons _).2 $
    ((sublist_or_mem_of_sublist s).resolve_right m₁).subperm)
end

end

/-! ### Singleton -/
instance : has_singleton α (multiset α) := ⟨λ a, a ::ₘ 0⟩

instance : is_lawful_singleton α (multiset α) := ⟨λ a, rfl⟩

theorem singleton_eq_cons (a : α) : singleton a = a ::ₘ 0 := rfl

@[simp] theorem mem_singleton {a b : α} : b ∈ ({a} : multiset α) ↔ b = a :=
by simp only [singleton_eq_cons, mem_cons, iff_self, or_false, not_mem_zero]

theorem mem_singleton_self (a : α) : a ∈ ({a} : multiset α) :=
by { rw singleton_eq_cons, exact mem_cons_self _ _ }

theorem singleton_inj {a b : α} : ({a} : multiset α) = {b} ↔ a = b :=
by { simp_rw [singleton_eq_cons], exact cons_inj_left _ }

@[simp] theorem singleton_ne_zero (a : α) : ({a} : multiset α) ≠ 0 :=
ne_of_gt (lt_cons_self _ _)

@[simp] theorem singleton_le {a : α} {s : multiset α} : {a} ≤ s ↔ a ∈ s :=
⟨λ h, mem_of_le h (mem_singleton_self _),
 λ h, let ⟨t, e⟩ := exists_cons_of_mem h in e.symm ▸ cons_le_cons _ (zero_le _)⟩

/-! ### Additive monoid -/

/-- The sum of two multisets is the lift of the list append operation.
  This adds the multiplicities of each element,
  i.e. `count a (s + t) = count a s + count a t`. -/
protected def add (s₁ s₂ : multiset α) : multiset α :=
quotient.lift_on₂ s₁ s₂ (λ l₁ l₂, ((l₁ ++ l₂ : list α) : multiset α)) $
  λ v₁ v₂ w₁ w₂ p₁ p₂, quot.sound $ p₁.append p₂

instance : has_add (multiset α) := ⟨multiset.add⟩

@[simp] theorem coe_add (s t : list α) : (s + t : multiset α) = (s ++ t : list α) := rfl

protected theorem add_comm (s t : multiset α) : s + t = t + s :=
quotient.induction_on₂ s t $ λ l₁ l₂, quot.sound perm_append_comm

protected theorem zero_add (s : multiset α) : 0 + s = s :=
quot.induction_on s $ λ l, rfl

theorem singleton_add (a : α) (s : multiset α) : {a} + s = a ::ₘ s := rfl

protected theorem add_le_add_left (s) {t u : multiset α} : s + t ≤ s + u ↔ t ≤ u :=
quotient.induction_on₃ s t u $ λ l₁ l₂ l₃, subperm_append_left _

protected theorem add_left_cancel (s) {t u : multiset α} (h : s + t = s + u) : t = u :=
le_antisymm ((multiset.add_le_add_left _).1 (le_of_eq h))
  ((multiset.add_le_add_left _).1 (le_of_eq h.symm))

instance : ordered_cancel_add_comm_monoid (multiset α) :=
{ zero                  := 0,
  add                   := (+),
  add_comm              := multiset.add_comm,
  add_assoc             := λ s₁ s₂ s₃, quotient.induction_on₃ s₁ s₂ s₃ $ λ l₁ l₂ l₃,
    congr_arg coe $ append_assoc l₁ l₂ l₃,
  zero_add              := multiset.zero_add,
  add_zero              := λ s, by rw [multiset.add_comm, multiset.zero_add],
  add_left_cancel       := multiset.add_left_cancel,
  add_le_add_left       := λ s₁ s₂ h s₃, (multiset.add_le_add_left _).2 h,
  le_of_add_le_add_left := λ s₁ s₂ s₃, (multiset.add_le_add_left _).1,
  ..@multiset.partial_order α }

theorem le_add_right (s t : multiset α) : s ≤ s + t :=
by simpa using add_le_add_left (zero_le t) s

theorem le_add_left (s t : multiset α) : s ≤ t + s :=
by simpa using add_le_add_right (zero_le t) s
theorem le_iff_exists_add {s t : multiset α} : s ≤ t ↔ ∃ u, t = s + u :=
⟨λ h, le_induction_on h $ λ l₁ l₂ s,
  let ⟨l, p⟩ := s.exists_perm_append in ⟨l, quot.sound p⟩,
 λ ⟨u, e⟩, e.symm ▸ le_add_right _ _⟩

instance : order_bot (multiset α) :=
{ bot                   := 0,
  bot_le                := multiset.zero_le }

instance : canonically_ordered_add_monoid (multiset α) :=
{ le_iff_exists_add     := @le_iff_exists_add _,
  ..multiset.order_bot,
  ..multiset.ordered_cancel_add_comm_monoid }

@[simp] theorem cons_add (a : α) (s t : multiset α) : a ::ₘ s + t = a ::ₘ (s + t) :=
by rw [← singleton_add, ← singleton_add, add_assoc]

@[simp] theorem add_cons (a : α) (s t : multiset α) : s + a ::ₘ t = a ::ₘ (s + t) :=
by rw [add_comm, cons_add, add_comm]

@[simp] theorem mem_add {a : α} {s t : multiset α} : a ∈ s + t ↔ a ∈ s ∨ a ∈ t :=
quotient.induction_on₂ s t $ λ l₁ l₂, mem_append

lemma mem_of_mem_nsmul {a : α} {s : multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s :=
begin
  induction n with n ih,
  { rw zero_nsmul at h,
    exact absurd h (not_mem_zero _) },
  { rw [succ_nsmul, mem_add] at h,
    exact h.elim id ih },
end

@[simp]
lemma mem_nsmul {a : α} {s : multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n • s ↔ a ∈ s :=
begin
  refine ⟨mem_of_mem_nsmul, λ h, _⟩,
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h0,
  rw [succ_nsmul, mem_add],
  exact or.inl h
end

lemma nsmul_cons {s : multiset α} (n : ℕ) (a : α) : n • (a ::ₘ s) = n • {a} + n • s :=
by rw [←singleton_add, nsmul_add]

/-! ### Cardinality -/

/-- The cardinality of a multiset is the sum of the multiplicities
  of all its elements, or simply the length of the underlying list. -/
def card : multiset α →+ ℕ :=
{ to_fun := λ s, quot.lift_on s length $ λ l₁ l₂, perm.length_eq,
  map_zero' := rfl,
  map_add' := λ s t, quotient.induction_on₂ s t length_append }

@[simp] theorem coe_card (l : list α) : card (l : multiset α) = length l := rfl

@[simp] theorem card_zero : @card α 0 = 0 := rfl

theorem card_add (s t : multiset α) : card (s + t) = card s + card t :=
card.map_add s t

lemma card_nsmul (s : multiset α) (n : ℕ) :
  (n • s).card = n * s.card :=
by rw [card.map_nsmul s n, nat.nsmul_eq_mul]

@[simp] theorem card_cons (a : α) (s : multiset α) : card (a ::ₘ s) = card s + 1 :=
quot.induction_on s $ λ l, rfl

@[simp] theorem card_singleton (a : α) : card ({a} : multiset α) = 1 :=
by simp only [singleton_eq_cons, card_zero, eq_self_iff_true, zero_add, card_cons]

theorem card_eq_one {s : multiset α} : card s = 1 ↔ ∃ a, s = {a} :=
⟨quot.induction_on s $ λ l h,
  (list.length_eq_one.1 h).imp $ λ a, congr_arg coe,
 λ ⟨a, e⟩, e.symm ▸ rfl⟩

theorem card_le_of_le {s t : multiset α} (h : s ≤ t) : card s ≤ card t :=
le_induction_on h $ λ l₁ l₂, length_le_of_sublist

@[mono] theorem card_mono : monotone (@card α) := λ a b, card_le_of_le

theorem eq_of_le_of_card_le {s t : multiset α} (h : s ≤ t) : card t ≤ card s → s = t :=
le_induction_on h $ λ l₁ l₂ s h₂, congr_arg coe $ eq_of_sublist_of_length_le s h₂

theorem card_lt_of_lt {s t : multiset α} (h : s < t) : card s < card t :=
lt_of_not_ge $ λ h₂, ne_of_lt h $ eq_of_le_of_card_le (le_of_lt h) h₂

theorem lt_iff_cons_le {s t : multiset α} : s < t ↔ ∃ a, a ::ₘ s ≤ t :=
⟨quotient.induction_on₂ s t $ λ l₁ l₂ h,
  subperm.exists_of_length_lt (le_of_lt h) (card_lt_of_lt h),
λ ⟨a, h⟩, lt_of_lt_of_le (lt_cons_self _ _) h⟩

@[simp] theorem card_eq_zero {s : multiset α} : card s = 0 ↔ s = 0 :=
⟨λ h, (eq_of_le_of_card_le (zero_le _) (le_of_eq h)).symm, λ e, by simp [e]⟩

theorem card_pos {s : multiset α} : 0 < card s ↔ s ≠ 0 :=
pos_iff_ne_zero.trans $ not_congr card_eq_zero

theorem card_pos_iff_exists_mem {s : multiset α} : 0 < card s ↔ ∃ a, a ∈ s :=
quot.induction_on s $ λ l, length_pos_iff_exists_mem

lemma card_eq_two {s : multiset α} : s.card = 2 ↔ ∃ x y, s = {x, y} :=
⟨quot.induction_on s (λ l h, (list.length_eq_two.mp h).imp
  (λ a, Exists.imp (λ b, congr_arg coe))), λ ⟨a, b, e⟩, e.symm ▸ rfl⟩

lemma card_eq_three {s : multiset α} : s.card = 3 ↔ ∃ x y z, s = {x, y, z} :=
⟨quot.induction_on s (λ l h, (list.length_eq_three.mp h).imp
  (λ a, Exists.imp (λ b, Exists.imp (λ c, congr_arg coe)))), λ ⟨a, b, c, e⟩, e.symm ▸ rfl⟩

/-! ### Induction principles -/

/-- A strong induction principle for multisets:
If you construct a value for a particular multiset given values for all strictly smaller multisets,
you can construct a value for any multiset.
-/
@[elab_as_eliminator] def strong_induction_on {p : multiset α → Sort*} :
  ∀ (s : multiset α), (∀ s, (∀t < s, p t) → p s) → p s
| s := λ ih, ih s $ λ t h,
  have card t < card s, from card_lt_of_lt h,
  strong_induction_on t ih
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf card⟩]}

theorem strong_induction_eq {p : multiset α → Sort*}
  (s : multiset α) (H) : @strong_induction_on _ p s H =
    H s (λ t h, @strong_induction_on _ p t H) :=
by rw [strong_induction_on]
@[elab_as_eliminator] lemma case_strong_induction_on {p : multiset α → Prop}
  (s : multiset α) (h₀ : p 0) (h₁ : ∀ a s, (∀t ≤ s, p t) → p (a ::ₘ s)) : p s :=
multiset.strong_induction_on s $ assume s,
multiset.induction_on s (λ _, h₀) $ λ a s _ ih, h₁ _ _ $
λ t h, ih _ $ lt_of_le_of_lt h $ lt_cons_self _ _

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all multisets `s` of
cardinality less than `n`, starting from multisets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
def strong_downward_induction {p : multiset α → Sort*} {n : ℕ} (H : ∀ t₁, (∀ {t₂ : multiset α},
  t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  ∀ (s : multiset α), s.card ≤ n → p s
| s := H s (λ t ht h, have n - card t < n - card s,
     from (tsub_lt_tsub_iff_left_of_le ht).2 (card_lt_of_lt h),
  strong_downward_induction t ht)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf (λ (t : multiset α), n - t.card)⟩]}

lemma strong_downward_induction_eq {p : multiset α → Sort*} {n : ℕ} (H : ∀ t₁, (∀ {t₂ : multiset α},
  t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) (s : multiset α) :
  strong_downward_induction H s = H s (λ t ht hst, strong_downward_induction H t ht) :=
by rw strong_downward_induction

/-- Analogue of `strong_downward_induction` with order of arguments swapped. -/
@[elab_as_eliminator] def strong_downward_induction_on {p : multiset α → Sort*} {n : ℕ} :
  ∀ (s : multiset α), (∀ t₁, (∀ {t₂ : multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n →
  p t₁) → s.card ≤ n → p s :=
λ s H, strong_downward_induction H s

lemma strong_downward_induction_on_eq {p : multiset α → Sort*} (s : multiset α) {n : ℕ} (H : ∀ t₁,
  (∀ {t₂ : multiset α}, t₂.card ≤ n → t₁ < t₂ → p t₂) → t₁.card ≤ n → p t₁) :
  s.strong_downward_induction_on H = H s (λ t ht h, t.strong_downward_induction_on H ht) :=
by { dunfold strong_downward_induction_on, rw strong_downward_induction }

/-- Another way of expressing `strong_induction_on`: the `(<)` relation is well-founded. -/
lemma well_founded_lt : well_founded ((<) : multiset α → multiset α → Prop) :=
subrelation.wf (λ _ _, multiset.card_lt_of_lt) (measure_wf multiset.card)

/-! ### `multiset.repeat` -/

/-- `repeat a n` is the multiset containing only `a` with multiplicity `n`. -/
def repeat (a : α) (n : ℕ) : multiset α := repeat a n

@[simp] lemma repeat_zero (a : α) : repeat a 0 = 0 := rfl

@[simp] lemma repeat_succ (a : α) (n) : repeat a (n+1) = a ::ₘ repeat a n := by simp [repeat]

@[simp] lemma repeat_one (a : α) : repeat a 1 = {a} :=
by simp only [repeat_succ, singleton_eq_cons, eq_self_iff_true, repeat_zero, cons_inj_right]

@[simp] lemma card_repeat : ∀ (a : α) n, card (repeat a n) = n := length_repeat

lemma mem_repeat {a b : α} {n : ℕ} : b ∈ repeat a n ↔ n ≠ 0 ∧ b = a := mem_repeat

theorem eq_of_mem_repeat {a b : α} {n} : b ∈ repeat a n → b = a := eq_of_mem_repeat

theorem eq_repeat' {a : α} {s : multiset α} : s = repeat a s.card ↔ ∀ b ∈ s, b = a :=
quot.induction_on s $ λ l, iff.trans ⟨λ h,
  (perm_repeat.1 $ (quotient.exact h)), congr_arg coe⟩ eq_repeat'

theorem eq_repeat_of_mem {a : α} {s : multiset α} : (∀ b ∈ s, b = a) → s = repeat a s.card :=
eq_repeat'.2

theorem eq_repeat {a : α} {n} {s : multiset α} : s = repeat a n ↔ card s = n ∧ ∀ b ∈ s, b = a :=
⟨λ h, h.symm ▸ ⟨card_repeat _ _, λ b, eq_of_mem_repeat⟩,
 λ ⟨e, al⟩, e ▸ eq_repeat_of_mem al⟩

lemma repeat_left_injective {n : ℕ} (hn : n ≠ 0) : function.injective (λ a : α, repeat a n) :=
λ a b h, (eq_repeat.1 h).2 _ $ mem_repeat.2 ⟨hn, rfl⟩

@[simp] lemma repeat_left_inj {a b : α} {n : ℕ} (h : n ≠ 0) : repeat a n = repeat b n ↔ a = b :=
(repeat_left_injective h).eq_iff

theorem repeat_injective (a : α) : function.injective (repeat a) :=
λ m n h, by rw [← (eq_repeat.1 h).1, card_repeat]

theorem repeat_subset_singleton : ∀ (a : α) n, repeat a n ⊆ {a} := repeat_subset_singleton

theorem repeat_le_coe {a : α} {n} {l : list α} : repeat a n ≤ l ↔ list.repeat a n <+ l :=
⟨λ ⟨l', p, s⟩, (perm_repeat.1 p) ▸ s, sublist.subperm⟩

theorem nsmul_singleton (a : α) (n) : n • ({a} : multiset α) = repeat a n :=
begin
  refine eq_repeat.mpr ⟨_, λ b hb, mem_singleton.mp (mem_of_mem_nsmul hb)⟩,
  rw [card_nsmul, card_singleton, mul_one]
end

lemma nsmul_repeat {a : α} (n m : ℕ) : n • (repeat a m) = repeat a (n * m) :=
begin
  rw eq_repeat,
  split,
  { rw [card_nsmul, card_repeat] },
  { exact λ b hb, eq_of_mem_repeat (mem_of_mem_nsmul hb) },
end

/-! ### Erasing one copy of an element -/
section erase
variables [decidable_eq α] {s t : multiset α} {a b : α}

/-- `erase s a` is the multiset that subtracts 1 from the
  multiplicity of `a`. -/
def erase (s : multiset α) (a : α) : multiset α :=
quot.lift_on s (λ l, (l.erase a : multiset α))
  (λ l₁ l₂ p, quot.sound (p.erase a))

@[simp] theorem coe_erase (l : list α) (a : α) :
  erase (l : multiset α) a = l.erase a := rfl

@[simp] theorem erase_zero (a : α) : (0 : multiset α).erase a = 0 := rfl

@[simp] theorem erase_cons_head (a : α) (s : multiset α) : (a ::ₘ s).erase a = s :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_head a l

@[simp, priority 990]
theorem erase_cons_tail {a b : α} (s : multiset α) (h : b ≠ a) :
  (b ::ₘ s).erase a = b ::ₘ s.erase a :=
quot.induction_on s $ λ l, congr_arg coe $ erase_cons_tail l h

@[simp, priority 980]
theorem erase_of_not_mem {a : α} {s : multiset α} : a ∉ s → s.erase a = s :=
quot.induction_on s $ λ l h, congr_arg coe $ erase_of_not_mem h

@[simp, priority 980]
theorem cons_erase {s : multiset α} {a : α} : a ∈ s → a ::ₘ s.erase a = s :=
quot.induction_on s $ λ l h, quot.sound (perm_cons_erase h).symm

theorem le_cons_erase (s : multiset α) (a : α) : s ≤ a ::ₘ s.erase a :=
if h : a ∈ s then le_of_eq (cons_erase h).symm
else by rw erase_of_not_mem h; apply le_cons_self

theorem erase_add_left_pos {a : α} {s : multiset α} (t) : a ∈ s → (s + t).erase a = s.erase a + t :=
quotient.induction_on₂ s t $ λ l₁ l₂ h, congr_arg coe $ erase_append_left l₂ h

theorem erase_add_right_pos {a : α} (s) {t : multiset α} (h : a ∈ t) :
  (s + t).erase a = s + t.erase a :=
by rw [add_comm, erase_add_left_pos s h, add_comm]

theorem erase_add_right_neg {a : α} {s : multiset α} (t) :
  a ∉ s → (s + t).erase a = s + t.erase a :=
quotient.induction_on₂ s t $ λ l₁ l₂ h, congr_arg coe $ erase_append_right l₂ h

theorem erase_add_left_neg {a : α} (s) {t : multiset α} (h : a ∉ t) :
  (s + t).erase a = s.erase a + t :=
by rw [add_comm, erase_add_right_neg s h, add_comm]

theorem erase_le (a : α) (s : multiset α) : s.erase a ≤ s :=
quot.induction_on s $ λ l, (erase_sublist a l).subperm

@[simp] theorem erase_lt {a : α} {s : multiset α} : s.erase a < s ↔ a ∈ s :=
⟨λ h, not_imp_comm.1 erase_of_not_mem (ne_of_lt h),
 λ h, by simpa [h] using lt_cons_self (s.erase a) a⟩

theorem erase_subset (a : α) (s : multiset α) : s.erase a ⊆ s :=
subset_of_le (erase_le a s)

theorem mem_erase_of_ne {a b : α} {s : multiset α} (ab : a ≠ b) : a ∈ s.erase b ↔ a ∈ s :=
quot.induction_on s $ λ l, list.mem_erase_of_ne ab

theorem mem_of_mem_erase {a b : α} {s : multiset α} : a ∈ s.erase b → a ∈ s :=
mem_of_subset (erase_subset _ _)

theorem erase_comm (s : multiset α) (a b : α) : (s.erase a).erase b = (s.erase b).erase a :=
quot.induction_on s $ λ l, congr_arg coe $ l.erase_comm a b

theorem erase_le_erase {s t : multiset α} (a : α) (h : s ≤ t) : s.erase a ≤ t.erase a :=
le_induction_on h $ λ l₁ l₂ h, (h.erase _).subperm

theorem erase_le_iff_le_cons {s t : multiset α} {a : α} : s.erase a ≤ t ↔ s ≤ a ::ₘ t :=
⟨λ h, le_trans (le_cons_erase _ _) (cons_le_cons _ h),
 λ h, if m : a ∈ s
  then by rw ← cons_erase m at h; exact (cons_le_cons_iff _).1 h
  else le_trans (erase_le _ _) ((le_cons_of_not_mem m).1 h)⟩

@[simp] theorem card_erase_of_mem {a : α} {s : multiset α} :
  a ∈ s → card (s.erase a) = pred (card s) :=
quot.induction_on s $ λ l, length_erase_of_mem

@[simp] lemma card_erase_add_one {a : α} {s : multiset α} :
  a ∈ s → (s.erase a).card + 1 = s.card :=
quot.induction_on s $ λ l, length_erase_add_one

theorem card_erase_lt_of_mem {a : α} {s : multiset α} : a ∈ s → card (s.erase a) < card s :=
λ h, card_lt_of_lt (erase_lt.mpr h)

theorem card_erase_le {a : α} {s : multiset α} : card (s.erase a) ≤ card s :=
card_le_of_le (erase_le a s)

theorem card_erase_eq_ite {a : α} {s : multiset α} :
  card (s.erase a) = if a ∈ s then pred (card s) else card s :=
begin
  by_cases h : a ∈ s,
  { rwa [card_erase_of_mem h, if_pos] },
  { rwa [erase_of_not_mem h, if_neg] }
end

end erase

@[simp] theorem coe_reverse (l : list α) : (reverse l : multiset α) = l :=
quot.sound $ reverse_perm _

/-! ### `multiset.map` -/

/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
def map (f : α → β) (s : multiset α) : multiset β :=
quot.lift_on s (λ l : list α, (l.map f : multiset β))
  (λ l₁ l₂ p, quot.sound (p.map f))

@[congr]
theorem map_congr {f g : α → β} {s t : multiset α} :
  s = t → (∀ x ∈ t, f x = g x) → map f s = map g t :=
begin
  rintros rfl h,
  induction s using quot.induction_on,
  exact congr_arg coe (map_congr h)
end

lemma map_hcongr {β' : Type*} {m : multiset α} {f : α → β} {f' : α → β'}
  (h : β = β') (hf : ∀a∈m, f a == f' a) : map f m == map f' m :=
begin subst h, simp at hf, simp [map_congr rfl hf] end

theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : multiset α} :
  (∀ y ∈ s.map f, p y) ↔ (∀ x ∈ s, p (f x)) :=
quotient.induction_on' s $ λ L, list.forall_mem_map_iff

@[simp] theorem coe_map (f : α → β) (l : list α) : map f ↑l = l.map f := rfl

@[simp] theorem map_zero (f : α → β) : map f 0 = 0 := rfl

@[simp] theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
quot.induction_on s $ λ l, rfl

theorem map_comp_cons (f : α → β) (t) : map f ∘ cons t = cons (f t) ∘ map f :=
by { ext, simp }

@[simp] theorem map_singleton (f : α → β) (a : α) : ({a} : multiset α).map f = {f a} := rfl

theorem map_repeat (f : α → β) (a : α) (k : ℕ) : (repeat a k).map f = repeat (f a) k := by
{ induction k, simp, simpa }

@[simp] theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ map_append _ _ _

/-- If each element of `s : multiset α` can be lifted to `β`, then `s` can be lifted to
`multiset β`. -/
instance [can_lift α β] : can_lift (multiset α) (multiset β) :=
{ cond := λ s, ∀ x ∈ s, can_lift.cond β x,
  coe := map can_lift.coe,
  prf := by { rintro ⟨l⟩ hl, lift l to list β using hl, exact ⟨l, coe_map _ _⟩ } }

/-- `multiset.map` as an `add_monoid_hom`. -/
def map_add_monoid_hom (f : α → β) : multiset α →+ multiset β :=
{ to_fun := map f,
  map_zero' := map_zero _,
  map_add' := map_add _ }

@[simp] lemma coe_map_add_monoid_hom (f : α → β) :
  (map_add_monoid_hom f : multiset α → multiset β) = map f := rfl

theorem map_nsmul (f : α → β) (n : ℕ) (s) : map f (n • s) = n • (map f s) :=
(map_add_monoid_hom f).map_nsmul _ _

@[simp] theorem mem_map {f : α → β} {b : β} {s : multiset α} :
  b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
quot.induction_on s $ λ l, mem_map

@[simp] theorem card_map (f : α → β) (s) : card (map f s) = card s :=
quot.induction_on s $ λ l, length_map _ _

@[simp] theorem map_eq_zero {s : multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 :=
by rw [← multiset.card_eq_zero, multiset.card_map, multiset.card_eq_zero]

theorem mem_map_of_mem (f : α → β) {a : α} {s : multiset α} (h : a ∈ s) : f a ∈ map f s :=
mem_map.2 ⟨_, h, rfl⟩

lemma map_eq_singleton {f : α → β} {s : multiset α} {b : β} :
  map f s = {b} ↔ ∃ a : α, s = {a} ∧ f a = b :=
begin
  split,
  { intro h,
    obtain ⟨a, ha⟩ : ∃ a, s = {a},
    { rw [←card_eq_one, ←card_map, h, card_singleton] },
    refine ⟨a, ha, _⟩,
    rw [←mem_singleton, ←h, ha, map_singleton, mem_singleton] },
  { rintro ⟨a, rfl, rfl⟩,
    simp }
end

theorem mem_map_of_injective {f : α → β} (H : function.injective f) {a : α} {s : multiset α} :
  f a ∈ map f s ↔ a ∈ s :=
quot.induction_on s $ λ l, mem_map_of_injective H

@[simp] theorem map_map (g : β → γ) (f : α → β) (s : multiset α) :
  map g (map f s) = map (g ∘ f) s :=
quot.induction_on s $ λ l, congr_arg coe $ list.map_map _ _ _

theorem map_id (s : multiset α) : map id s = s :=
quot.induction_on s $ λ l, congr_arg coe $ map_id _

@[simp] lemma map_id' (s : multiset α) : map (λx, x) s = s := map_id s

@[simp] theorem map_const (s : multiset α) (b : β) : map (function.const α b) s = repeat b s.card :=
quot.induction_on s $ λ l, congr_arg coe $ map_const _ _

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : list α} (h : b₁ ∈ map (function.const α b₂) l) :
  b₁ = b₂ :=
eq_of_mem_repeat $ by rwa map_const at h

@[simp] theorem map_le_map {f : α → β} {s t : multiset α} (h : s ≤ t) : map f s ≤ map f t :=
le_induction_on h $ λ l₁ l₂ h, (h.map f).subperm

@[simp] lemma map_lt_map {f : α → β} {s t : multiset α} (h : s < t) : s.map f < t.map f :=
begin
  refine (map_le_map h.le).lt_of_not_le (λ H, h.ne $ eq_of_le_of_card_le h.le _),
  rw [←s.card_map f, ←t.card_map f],
  exact card_le_of_le H,
end

lemma map_mono (f : α → β) : monotone (map f) := λ _ _, map_le_map
lemma map_strict_mono (f : α → β) : strict_mono (map f) := λ _ _, map_lt_map

@[simp] theorem map_subset_map {f : α → β} {s t : multiset α} (H : s ⊆ t) : map f s ⊆ map f t :=
λ b m, let ⟨a, h, e⟩ := mem_map.1 m in mem_map.2 ⟨a, H h, e⟩

lemma map_erase [decidable_eq α] [decidable_eq β]
  (f : α → β) (hf : function.injective f) (x : α) (s : multiset α) :
  (s.erase x).map f = (s.map f).erase (f x) :=
begin
  induction s using multiset.induction_on with y s ih,
  { simp },
  by_cases hxy : y = x,
  { cases hxy, simp },
  { rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih] }
end

/-! ### `multiset.fold` -/

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
def foldl (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldl f b l)
  (λ l₁ l₂ p, p.foldl_eq H b)

@[simp] theorem foldl_zero (f : β → α → β) (H b) : foldl f H b 0 = b := rfl

@[simp] theorem foldl_cons (f : β → α → β) (H b a s) :
  foldl f H b (a ::ₘ s) = foldl f H (f b a) s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem foldl_add (f : β → α → β) (H b s t) :
  foldl f H b (s + t) = foldl f H (foldl f H b s) t :=
quotient.induction_on₂ s t $ λ l₁ l₂, foldl_append _ _ _ _

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
def foldr (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) : β :=
quot.lift_on s (λ l, foldr f b l)
  (λ l₁ l₂ p, p.foldr_eq H b)

@[simp] theorem foldr_zero (f : α → β → β) (H b) : foldr f H b 0 = b := rfl

@[simp] theorem foldr_cons (f : α → β → β) (H b a s) :
  foldr f H b (a ::ₘ s) = f a (foldr f H b s) :=
quot.induction_on s $ λ l, rfl

@[simp] theorem foldr_singleton (f : α → β → β) (H b a) :
  foldr f H b ({a} : multiset α) = f a b :=
rfl

@[simp] theorem foldr_add (f : α → β → β) (H b s t) :
  foldr f H b (s + t) = foldr f H (foldr f H b t) s :=
quotient.induction_on₂ s t $ λ l₁ l₂, foldr_append _ _ _ _

@[simp] theorem coe_foldr (f : α → β → β) (H : left_commutative f) (b : β) (l : list α) :
  foldr f H b l = l.foldr f b := rfl

@[simp] theorem coe_foldl (f : β → α → β) (H : right_commutative f) (b : β) (l : list α) :
  foldl f H b l = l.foldl f b := rfl

theorem coe_foldr_swap (f : α → β → β) (H : left_commutative f) (b : β) (l : list α) :
  foldr f H b l = l.foldl (λ x y, f y x) b :=
(congr_arg (foldr f H b) (coe_reverse l)).symm.trans $ foldr_reverse _ _ _

theorem foldr_swap (f : α → β → β) (H : left_commutative f) (b : β) (s : multiset α) :
  foldr f H b s = foldl (λ x y, f y x) (λ x y z, (H _ _ _).symm) b s :=
quot.induction_on s $ λ l, coe_foldr_swap _ _ _ _

theorem foldl_swap (f : β → α → β) (H : right_commutative f) (b : β) (s : multiset α) :
  foldl f H b s = foldr (λ x y, f y x) (λ x y z, (H _ _ _).symm) b s :=
(foldr_swap _ _ _ _).symm

lemma foldr_induction' (f : α → β → β) (H : left_commutative f) (x : β) (q : α → Prop)
  (p : β → Prop) (s : multiset α) (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x)
  (q_s : ∀ a ∈ s, q a) :
  p (foldr f H x s) :=
begin
  revert s,
  refine multiset.induction (by simp [px]) _,
  intros a s hs hsa,
  rw foldr_cons,
  have hps : ∀ (x : α), x ∈ s → q x, from λ x hxs, hsa x (mem_cons_of_mem hxs),
  exact hpqf a (foldr f H x s) (hsa a (mem_cons_self a s)) (hs hps),
end

lemma foldr_induction (f : α → α → α) (H : left_commutative f) (x : α) (p : α → Prop)
  (s : multiset α) (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀ a ∈ s, p a) :
  p (foldr f H x s) :=
foldr_induction' f H x p p s p_f px p_s

lemma foldl_induction' (f : β → α → β) (H : right_commutative f) (x : β) (q : α → Prop)
  (p : β → Prop) (s : multiset α) (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x)
  (q_s : ∀ a ∈ s, q a) :
  p (foldl f H x s) :=
begin
  rw foldl_swap,
  exact foldr_induction' (λ x y, f y x) (λ x y z, (H _ _ _).symm) x q p s hpqf px q_s,
end

lemma foldl_induction (f : α → α → α) (H : right_commutative f) (x : α) (p : α → Prop)
  (s : multiset α) (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀ a ∈ s, p a) :
  p (foldl f H x s) :=
foldl_induction' f H x p p s p_f px p_s

/-! ### Map for partial functions -/

/-- Lift of the list `pmap` operation. Map a partial function `f` over a multiset
  `s` whose elements are all in the domain of `f`. -/
def pmap {p : α → Prop} (f : Π a, p a → β) (s : multiset α) : (∀ a ∈ s, p a) → multiset β :=
quot.rec_on s (λ l H, ↑(pmap f l H)) $ λ l₁ l₂ (pp : l₁ ~ l₂),
funext $ λ (H₂ : ∀ a ∈ l₂, p a),
have H₁ : ∀ a ∈ l₁, p a, from λ a h, H₂ a (pp.subset h),
have ∀ {s₂ e H}, @eq.rec (multiset α) l₁
  (λ s, (∀ a ∈ s, p a) → multiset β) (λ _, ↑(pmap f l₁ H₁))
  s₂ e H = ↑(pmap f l₁ H₁), by intros s₂ e _; subst e,
this.trans $ quot.sound $ pp.pmap f

@[simp] theorem coe_pmap {p : α → Prop} (f : Π a, p a → β)
  (l : list α) (H : ∀ a ∈ l, p a) : pmap f l H = l.pmap f H := rfl

@[simp] lemma pmap_zero {p : α → Prop} (f : Π a, p a → β) (h : ∀a∈(0:multiset α), p a) :
  pmap f 0 h = 0 := rfl

@[simp] lemma pmap_cons {p : α → Prop} (f : Π a, p a → β) (a : α) (m : multiset α) :
  ∀(h : ∀b∈a ::ₘ m, p b), pmap f (a ::ₘ m) h =
    f a (h a (mem_cons_self a m)) ::ₘ pmap f m (λa ha, h a $ mem_cons_of_mem ha) :=
quotient.induction_on m $ assume l h, rfl

/-- "Attach" a proof that `a ∈ s` to each element `a` in `s` to produce
  a multiset on `{x // x ∈ s}`. -/
def attach (s : multiset α) : multiset {x // x ∈ s} := pmap subtype.mk s (λ a, id)

@[simp] theorem coe_attach (l : list α) :
 @eq (multiset {x // x ∈ l}) (@attach α l) l.attach := rfl

theorem sizeof_lt_sizeof_of_mem [has_sizeof α] {x : α} {s : multiset α} (hx : x ∈ s) :
  sizeof x < sizeof s := by
{ induction s with l a b, exact list.sizeof_lt_sizeof_of_mem hx, refl }

theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : multiset α) :
  ∀ H, @pmap _ _ p (λ a _, f a) s H = map f s :=
quot.induction_on s $ λ l H, congr_arg coe $ pmap_eq_map p f l H

theorem pmap_congr {p q : α → Prop} {f : Π a, p a → β} {g : Π a, q a → β}
  (s : multiset α) {H₁ H₂} (h : ∀ a h₁ h₂, f a h₁ = g a h₂) :
  pmap f s H₁ = pmap g s H₂ :=
quot.induction_on s (λ l H₁ H₂, congr_arg coe $ pmap_congr l h) H₁ H₂

theorem map_pmap {p : α → Prop} (g : β → γ) (f : Π a, p a → β)
  (s) : ∀ H, map g (pmap f s H) = pmap (λ a h, g (f a h)) s H :=
quot.induction_on s $ λ l H, congr_arg coe $ map_pmap g f l H

theorem pmap_eq_map_attach {p : α → Prop} (f : Π a, p a → β)
  (s) : ∀ H, pmap f s H = s.attach.map (λ x, f x.1 (H _ x.2)) :=
quot.induction_on s $ λ l H, congr_arg coe $ pmap_eq_map_attach f l H

theorem attach_map_val (s : multiset α) : s.attach.map subtype.val = s :=
quot.induction_on s $ λ l, congr_arg coe $ attach_map_val l

@[simp] theorem mem_attach (s : multiset α) : ∀ x, x ∈ s.attach :=
quot.induction_on s $ λ l, mem_attach _

@[simp] theorem mem_pmap {p : α → Prop} {f : Π a, p a → β}
  {s H b} : b ∈ pmap f s H ↔ ∃ a (h : a ∈ s), f a (H a h) = b :=
quot.induction_on s (λ l H, mem_pmap) H

@[simp] theorem card_pmap {p : α → Prop} (f : Π a, p a → β)
  (s H) : card (pmap f s H) = card s :=
quot.induction_on s (λ l H, length_pmap) H

@[simp] theorem card_attach {m : multiset α} : card (attach m) = card m := card_pmap _ _ _

@[simp] lemma attach_zero : (0 : multiset α).attach = 0 := rfl

lemma attach_cons (a : α) (m : multiset α) :
  (a ::ₘ m).attach = ⟨a, mem_cons_self a m⟩ ::ₘ (m.attach.map $ λp, ⟨p.1, mem_cons_of_mem p.2⟩) :=
quotient.induction_on m $ assume l, congr_arg coe $ congr_arg (list.cons _) $
  by rw [list.map_pmap]; exact list.pmap_congr _ (assume a' h₁ h₂, subtype.eq rfl)

section decidable_pi_exists
variables {m : multiset α}

/-- If `p` is a decidable predicate,
so is the predicate that all elements of a multiset satisfy `p`. -/
protected def decidable_forall_multiset {p : α → Prop} [hp : ∀a, decidable (p a)] :
  decidable (∀a∈m, p a) :=
quotient.rec_on_subsingleton m (λl, decidable_of_iff (∀a∈l, p a) $ by simp)

instance decidable_dforall_multiset {p : Πa∈m, Prop} [hp : ∀a (h : a ∈ m), decidable (p a h)] :
  decidable (∀a (h : a ∈ m), p a h) :=
decidable_of_decidable_of_iff
  (@multiset.decidable_forall_multiset {a // a ∈ m} m.attach (λa, p a.1 a.2) _)
  (iff.intro (assume h a ha, h ⟨a, ha⟩ (mem_attach _ _)) (assume h ⟨a, ha⟩ _, h _ _))

/-- decidable equality for functions whose domain is bounded by multisets -/
instance decidable_eq_pi_multiset {β : α → Type*} [h : ∀a, decidable_eq (β a)] :
  decidable_eq (Πa∈m, β a) :=
assume f g, decidable_of_iff (∀a (h : a ∈ m), f a h = g a h) (by simp [function.funext_iff])

/-- If `p` is a decidable predicate,
so is the existence of an element in a multiset satisfying `p`. -/
def decidable_exists_multiset {p : α → Prop} [decidable_pred p] :
  decidable (∃ x ∈ m, p x) :=
quotient.rec_on_subsingleton m list.decidable_exists_mem

instance decidable_dexists_multiset {p : Πa∈m, Prop} [hp : ∀a (h : a ∈ m), decidable (p a h)] :
  decidable (∃a (h : a ∈ m), p a h) :=
decidable_of_decidable_of_iff
  (@multiset.decidable_exists_multiset {a // a ∈ m} m.attach (λa, p a.1 a.2) _)
  (iff.intro (λ ⟨⟨a, ha₁⟩, _, ha₂⟩, ⟨a, ha₁, ha₂⟩)
    (λ ⟨a, ha₁, ha₂⟩, ⟨⟨a, ha₁⟩, mem_attach _ _, ha₂⟩))

end decidable_pi_exists

/-! ### Subtraction -/
section
variables [decidable_eq α] {s t u : multiset α} {a b : α}

/-- `s - t` is the multiset such that `count a (s - t) = count a s - count a t` for all `a`
  (note that it is truncated subtraction, so it is `0` if `count a t ≥ count a s`). -/
protected def sub (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.diff l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ p₁.diff p₂

instance : has_sub (multiset α) := ⟨multiset.sub⟩

@[simp] theorem coe_sub (s t : list α) : (s - t : multiset α) = (s.diff t : list α) := rfl

/-- This is a special case of `tsub_zero`, which should be used instead of this.
  This is needed to prove `has_ordered_sub (multiset α)`. -/
protected theorem sub_zero (s : multiset α) : s - 0 = s :=
quot.induction_on s $ λ l, rfl

@[simp] theorem sub_cons (a : α) (s t : multiset α) : s - a ::ₘ t = s.erase a - t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ diff_cons _ _ _

/-- This is a special case of `tsub_le_iff_right`, which should be used instead of this.
  This is needed to prove `has_ordered_sub (multiset α)`. -/
protected theorem sub_le_iff_le_add : s - t ≤ u ↔ s ≤ u + t :=
by revert s; exact
multiset.induction_on t (by simp [multiset.sub_zero])
  (λ a t IH s, by simp [IH, erase_le_iff_le_cons])

instance : has_ordered_sub (multiset α) :=
⟨λ n m k, multiset.sub_le_iff_le_add⟩

theorem sub_eq_fold_erase (s t : multiset α) : s - t = foldl erase erase_comm s t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
show ↑(l₁.diff l₂) = foldl erase erase_comm ↑l₁ ↑l₂,
by { rw diff_eq_foldl l₁ l₂, symmetry, exact foldl_hom _ _ _ _ _ (λ x y, rfl) }

@[simp] theorem card_sub {s t : multiset α} (h : t ≤ s) : card (s - t) = card s - card t :=
(tsub_eq_of_eq_add_rev $ by rw [add_comm, ← card_add, tsub_add_cancel_of_le h]).symm

/-! ### Union -/

/-- `s ∪ t` is the lattice join operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∪ t` is the maximum
  of the multiplicities in `s` and `t`. -/
def union (s t : multiset α) : multiset α := s - t + t

instance : has_union (multiset α) := ⟨union⟩

theorem union_def (s t : multiset α) : s ∪ t = s - t + t := rfl

theorem le_union_left (s t : multiset α) : s ≤ s ∪ t := le_tsub_add

theorem le_union_right (s t : multiset α) : t ≤ s ∪ t := le_add_left _ _

theorem eq_union_left : t ≤ s → s ∪ t = s := tsub_add_cancel_of_le

theorem union_le_union_right (h : s ≤ t) (u) : s ∪ u ≤ t ∪ u :=
add_le_add_right (tsub_le_tsub_right h _) u

theorem union_le (h₁ : s ≤ u) (h₂ : t ≤ u) : s ∪ t ≤ u :=
by rw ← eq_union_left h₂; exact union_le_union_right h₁ t

@[simp] theorem mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t :=
⟨λ h, (mem_add.1 h).imp_left (mem_of_le tsub_le_self),
 or.rec (mem_of_le $ le_union_left _ _) (mem_of_le $ le_union_right _ _)⟩

@[simp] theorem map_union [decidable_eq β] {f : α → β} (finj : function.injective f)
  {s t : multiset α} :
  map f (s ∪ t) = map f s ∪ map f t :=
quotient.induction_on₂ s t $ λ l₁ l₂,
congr_arg coe (by rw [list.map_append f, list.map_diff finj])

/-! ### Intersection -/

/-- `s ∩ t` is the lattice meet operation with respect to the
  multiset `≤`. The multiplicity of `a` in `s ∩ t` is the minimum
  of the multiplicities in `s` and `t`. -/
def inter (s t : multiset α) : multiset α :=
quotient.lift_on₂ s t (λ l₁ l₂, (l₁.bag_inter l₂ : multiset α)) $ λ v₁ v₂ w₁ w₂ p₁ p₂,
  quot.sound $ p₁.bag_inter p₂

instance : has_inter (multiset α) := ⟨inter⟩

@[simp] theorem inter_zero (s : multiset α) : s ∩ 0 = 0 :=
quot.induction_on s $ λ l, congr_arg coe l.bag_inter_nil

@[simp] theorem zero_inter (s : multiset α) : 0 ∩ s = 0 :=
quot.induction_on s $ λ l, congr_arg coe l.nil_bag_inter

@[simp] theorem cons_inter_of_pos {a} (s : multiset α) {t} :
  a ∈ t → (a ::ₘ s) ∩ t = a ::ₘ s ∩ t.erase a :=
quotient.induction_on₂ s t $ λ l₁ l₂ h,
congr_arg coe $ cons_bag_inter_of_pos _ h

@[simp] theorem cons_inter_of_neg {a} (s : multiset α) {t} :
  a ∉ t → (a ::ₘ s) ∩ t = s ∩ t :=
quotient.induction_on₂ s t $ λ l₁ l₂ h,
congr_arg coe $ cons_bag_inter_of_neg _ h

theorem inter_le_left (s t : multiset α) : s ∩ t ≤ s :=
quotient.induction_on₂ s t $ λ l₁ l₂,
(bag_inter_sublist_left _ _).subperm

theorem inter_le_right (s : multiset α) : ∀ t, s ∩ t ≤ t :=
multiset.induction_on s (λ t, (zero_inter t).symm ▸ zero_le _) $
λ a s IH t, if h : a ∈ t
  then by simpa [h] using cons_le_cons a (IH (t.erase a))
  else by simp [h, IH]

theorem le_inter (h₁ : s ≤ t) (h₂ : s ≤ u) : s ≤ t ∩ u :=
begin
  revert s u, refine multiset.induction_on t _ (λ a t IH, _); intros,
  { simp [h₁] },
  by_cases a ∈ u,
  { rw [cons_inter_of_pos _ h, ← erase_le_iff_le_cons],
    exact IH (erase_le_iff_le_cons.2 h₁) (erase_le_erase _ h₂) },
  { rw cons_inter_of_neg _ h,
    exact IH ((le_cons_of_not_mem $ mt (mem_of_le h₂) h).1 h₁) h₂ }
end

@[simp] theorem mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t :=
⟨λ h, ⟨mem_of_le (inter_le_left _ _) h, mem_of_le (inter_le_right _ _) h⟩,
 λ ⟨h₁, h₂⟩, by rw [← cons_erase h₁, cons_inter_of_pos _ h₂]; apply mem_cons_self⟩

instance : lattice (multiset α) :=
{ sup          := (∪),
  sup_le       := @union_le _ _,
  le_sup_left  := le_union_left,
  le_sup_right := le_union_right,
  inf          := (∩),
  le_inf       := @le_inter _ _,
  inf_le_left  := inter_le_left,
  inf_le_right := inter_le_right,
  ..@multiset.partial_order α }

@[simp] theorem sup_eq_union (s t : multiset α) : s ⊔ t = s ∪ t := rfl
@[simp] theorem inf_eq_inter (s t : multiset α) : s ⊓ t = s ∩ t := rfl

@[simp] theorem le_inter_iff : s ≤ t ∩ u ↔ s ≤ t ∧ s ≤ u := le_inf_iff
@[simp] theorem union_le_iff : s ∪ t ≤ u ↔ s ≤ u ∧ t ≤ u := sup_le_iff

theorem union_comm (s t : multiset α) : s ∪ t = t ∪ s := sup_comm
theorem inter_comm (s t : multiset α) : s ∩ t = t ∩ s := inf_comm

theorem eq_union_right (h : s ≤ t) : s ∪ t = t :=
by rw [union_comm, eq_union_left h]

theorem union_le_union_left (h : s ≤ t) (u) : u ∪ s ≤ u ∪ t :=
sup_le_sup_left h _

theorem union_le_add (s t : multiset α) : s ∪ t ≤ s + t :=
union_le (le_add_right _ _) (le_add_left _ _)

theorem union_add_distrib (s t u : multiset α) : (s ∪ t) + u = (s + u) ∪ (t + u) :=
by simpa [(∪), union, eq_comm, add_assoc] using show s + u - (t + u) = s - t,
by rw [add_comm t, tsub_add_eq_tsub_tsub, add_tsub_cancel_right]

theorem add_union_distrib (s t u : multiset α) : s + (t ∪ u) = (s + t) ∪ (s + u) :=
by rw [add_comm, union_add_distrib, add_comm s, add_comm s]

theorem cons_union_distrib (a : α) (s t : multiset α) : a ::ₘ (s ∪ t) = (a ::ₘ s) ∪ (a ::ₘ t) :=
by simpa using add_union_distrib (a ::ₘ 0) s t

theorem inter_add_distrib (s t u : multiset α) : (s ∩ t) + u = (s + u) ∩ (t + u) :=
begin
  by_contra h,
  cases lt_iff_cons_le.1 (lt_of_le_of_ne (le_inter
    (add_le_add_right (inter_le_left s t) u)
    (add_le_add_right (inter_le_right s t) u)) h) with a hl,
  rw ← cons_add at hl,
  exact not_le_of_lt (lt_cons_self (s ∩ t) a) (le_inter
    (le_of_add_le_add_right (le_trans hl (inter_le_left _ _)))
    (le_of_add_le_add_right (le_trans hl (inter_le_right _ _))))
end

theorem add_inter_distrib (s t u : multiset α) : s + (t ∩ u) = (s + t) ∩ (s + u) :=
by rw [add_comm, inter_add_distrib, add_comm s, add_comm s]

theorem cons_inter_distrib (a : α) (s t : multiset α) : a ::ₘ (s ∩ t) = (a ::ₘ s) ∩ (a ::ₘ t) :=
by simp

theorem union_add_inter (s t : multiset α) : s ∪ t + s ∩ t = s + t :=
begin
  apply le_antisymm,
  { rw union_add_distrib,
    refine union_le (add_le_add_left (inter_le_right _ _) _) _,
    rw add_comm, exact add_le_add_right (inter_le_left _ _) _ },
  { rw [add_comm, add_inter_distrib],
    refine le_inter (add_le_add_right (le_union_right _ _) _) _,
    rw add_comm, exact add_le_add_right (le_union_left _ _) _ }
end

theorem sub_add_inter (s t : multiset α) : s - t + s ∩ t = s :=
begin
  rw [inter_comm],
  revert s, refine multiset.induction_on t (by simp) (λ a t IH s, _),
  by_cases a ∈ s,
  { rw [cons_inter_of_pos _ h, sub_cons, add_cons, IH, cons_erase h] },
  { rw [cons_inter_of_neg _ h, sub_cons, erase_of_not_mem h, IH] }
end

theorem sub_inter (s t : multiset α) : s - (s ∩ t) = s - t :=
add_right_cancel $ by rw [sub_add_inter s t, tsub_add_cancel_of_le (inter_le_left s t)]

end

/-! ### `multiset.filter` -/
section
variables (p : α → Prop) [decidable_pred p]

/-- `filter p s` returns the elements in `s` (with the same multiplicities)
  which satisfy `p`, and removes the rest. -/
def filter (s : multiset α) : multiset α :=
quot.lift_on s (λ l, (filter p l : multiset α))
  (λ l₁ l₂ h, quot.sound $ h.filter p)

@[simp] theorem coe_filter (l : list α) : filter p (↑l) = l.filter p := rfl

@[simp] theorem filter_zero : filter p 0 = 0 := rfl

lemma filter_congr {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  {s : multiset α} : (∀ x ∈ s, p x ↔ q x) → filter p s = filter q s :=
quot.induction_on s $ λ l h, congr_arg coe $ filter_congr' h

@[simp] theorem filter_add (s t : multiset α) : filter p (s + t) = filter p s + filter p t :=
quotient.induction_on₂ s t $ λ l₁ l₂, congr_arg coe $ filter_append _ _

@[simp] theorem filter_le (s : multiset α) : filter p s ≤ s :=
quot.induction_on s $ λ l, (filter_sublist _).subperm

@[simp] theorem filter_subset (s : multiset α) : filter p s ⊆ s :=
subset_of_le $ filter_le _ _

theorem filter_le_filter {s t} (h : s ≤ t) : filter p s ≤ filter p t :=
le_induction_on h $ λ l₁ l₂ h, (h.filter p).subperm

lemma monotone_filter_left :
  monotone (filter p) :=
λ s t, filter_le_filter p

lemma monotone_filter_right (s : multiset α) ⦃p q : α → Prop⦄
  [decidable_pred p] [decidable_pred q] (h : p ≤ q) :
  s.filter p ≤ s.filter q :=
quotient.induction_on s (λ l, (l.monotone_filter_right h).subperm)

variable {p}

@[simp] theorem filter_cons_of_pos {a : α} (s) : p a → filter p (a ::ₘ s) = a ::ₘ filter p s :=
quot.induction_on s $ λ l h, congr_arg coe $ filter_cons_of_pos l h

@[simp] theorem filter_cons_of_neg {a : α} (s) : ¬ p a → filter p (a ::ₘ s) = filter p s :=
quot.induction_on s $ λ l h, @congr_arg _ _ _ _ coe $ filter_cons_of_neg l h

@[simp] theorem mem_filter {a : α} {s} : a ∈ filter p s ↔ a ∈ s ∧ p a :=
quot.induction_on s $ λ l, mem_filter

theorem of_mem_filter {a : α} {s} (h : a ∈ filter p s) : p a :=
(mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {s} (h : a ∈ filter p s) : a ∈ s :=
(mem_filter.1 h).1

theorem mem_filter_of_mem {a : α} {l} (m : a ∈ l) (h : p a) : a ∈ filter p l :=
mem_filter.2 ⟨m, h⟩

theorem filter_eq_self {s} : filter p s = s ↔ ∀ a ∈ s, p a :=
quot.induction_on s $ λ l, iff.trans ⟨λ h,
  eq_of_sublist_of_length_eq (filter_sublist _) (@congr_arg _ _ _ _ card h),
  congr_arg coe⟩ filter_eq_self

theorem filter_eq_nil {s} : filter p s = 0 ↔ ∀ a ∈ s, ¬p a :=
quot.induction_on s $ λ l, iff.trans ⟨λ h,
  eq_nil_of_length_eq_zero (@congr_arg _ _ _ _ card h),
  congr_arg coe⟩ filter_eq_nil

theorem le_filter {s t} : s ≤ filter p t ↔ s ≤ t ∧ ∀ a ∈ s, p a :=
⟨λ h, ⟨le_trans h (filter_le _ _), λ a m, of_mem_filter (mem_of_le h m)⟩,
 λ ⟨h, al⟩, filter_eq_self.2 al ▸ filter_le_filter p h⟩

theorem filter_cons {a : α} (s : multiset α) :
  filter p (a ::ₘ s) = (if p a then {a} else 0) + filter p s :=
begin
  split_ifs with h,
  { rw [filter_cons_of_pos _ h, singleton_add] },
  { rw [filter_cons_of_neg _ h, zero_add] },
end

lemma filter_nsmul (s : multiset α) (n : ℕ) :
  filter p (n • s) = n • filter p s :=
begin
  refine s.induction_on _ _,
  { simp only [filter_zero, nsmul_zero] },
  { intros a ha ih,
    rw [nsmul_cons, filter_add, ih, filter_cons, nsmul_add],
    congr,
    split_ifs with hp;
    { simp only [filter_eq_self, nsmul_zero, filter_eq_nil],
      intros b hb,
      rwa (mem_singleton.mp (mem_of_mem_nsmul hb)) } }
end

variable (p)

@[simp] theorem filter_sub [decidable_eq α] (s t : multiset α) :
  filter p (s - t) = filter p s - filter p t :=
begin
  revert s, refine multiset.induction_on t (by simp) (λ a t IH s, _),
  rw [sub_cons, IH],
  by_cases p a,
  { rw [filter_cons_of_pos _ h, sub_cons], congr,
    by_cases m : a ∈ s,
    { rw [← cons_inj_right a, ← filter_cons_of_pos _ h,
          cons_erase (mem_filter_of_mem m h), cons_erase m] },
    { rw [erase_of_not_mem m, erase_of_not_mem (mt mem_of_mem_filter m)] } },
  { rw [filter_cons_of_neg _ h],
    by_cases m : a ∈ s,
    { rw [(by rw filter_cons_of_neg _ h : filter p (erase s a) = filter p (a ::ₘ erase s a)),
          cons_erase m] },
    { rw [erase_of_not_mem m] } }
end

@[simp] theorem filter_union [decidable_eq α] (s t : multiset α) :
  filter p (s ∪ t) = filter p s ∪ filter p t :=
by simp [(∪), union]

@[simp] theorem filter_inter [decidable_eq α] (s t : multiset α) :
  filter p (s ∩ t) = filter p s ∩ filter p t :=
le_antisymm (le_inter
    (filter_le_filter _ $ inter_le_left _ _)
    (filter_le_filter _ $ inter_le_right _ _)) $ le_filter.2
⟨inf_le_inf (filter_le _ _) (filter_le _ _),
  λ a h, of_mem_filter (mem_of_le (inter_le_left _ _) h)⟩

@[simp] theorem filter_filter (q) [decidable_pred q] (s : multiset α) :
  filter p (filter q s) = filter (λ a, p a ∧ q a) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_filter p q l

theorem filter_add_filter (q) [decidable_pred q] (s : multiset α) :
  filter p s + filter q s = filter (λ a, p a ∨ q a) s + filter (λ a, p a ∧ q a) s :=
multiset.induction_on s rfl $ λ a s IH,
by by_cases p a; by_cases q a; simp *

theorem filter_add_not (s : multiset α) :
  filter p s + filter (λ a, ¬ p a) s = s :=
by rw [filter_add_filter, filter_eq_self.2, filter_eq_nil.2]; simp [decidable.em]

theorem map_filter (f : β → α) (s : multiset β) :
  filter p (map f s) = map f (filter (p ∘ f) s) :=
quot.induction_on s (λ l, by simp [map_filter])

/-! ### Simultaneously filter and map elements of a multiset -/

/-- `filter_map f s` is a combination filter/map operation on `s`.
  The function `f : α → option β` is applied to each element of `s`;
  if `f a` is `some b` then `b` is added to the result, otherwise
  `a` is removed from the resulting multiset. -/
def filter_map (f : α → option β) (s : multiset α) : multiset β :=
quot.lift_on s (λ l, (filter_map f l : multiset β))
  (λ l₁ l₂ h, quot.sound $ h.filter_map f)

@[simp] theorem coe_filter_map (f : α → option β) (l : list α) :
  filter_map f l = l.filter_map f := rfl

@[simp] theorem filter_map_zero (f : α → option β) : filter_map f 0 = 0 := rfl

@[simp] theorem filter_map_cons_none {f : α → option β} (a : α) (s : multiset α) (h : f a = none) :
  filter_map f (a ::ₘ s) = filter_map f s :=
quot.induction_on s $ λ l, @congr_arg _ _ _ _ coe $ filter_map_cons_none a l h

@[simp] theorem filter_map_cons_some (f : α → option β)
  (a : α) (s : multiset α) {b : β} (h : f a = some b) :
  filter_map f (a ::ₘ s) = b ::ₘ filter_map f s :=
quot.induction_on s $ λ l, @congr_arg _ _ _ _ coe $ filter_map_cons_some f a l h

theorem filter_map_eq_map (f : α → β) : filter_map (some ∘ f) = map f :=
funext $ λ s, quot.induction_on s $ λ l,
@congr_arg _ _ _ _ coe $ congr_fun (filter_map_eq_map f) l

theorem filter_map_eq_filter : filter_map (option.guard p) = filter p :=
funext $ λ s, quot.induction_on s $ λ l,
@congr_arg _ _ _ _ coe $ congr_fun (filter_map_eq_filter p) l

theorem filter_map_filter_map (f : α → option β) (g : β → option γ) (s : multiset α) :
  filter_map g (filter_map f s) = filter_map (λ x, (f x).bind g) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_filter_map f g l

theorem map_filter_map (f : α → option β) (g : β → γ) (s : multiset α) :
  map g (filter_map f s) = filter_map (λ x, (f x).map g) s :=
quot.induction_on s $ λ l, congr_arg coe $ map_filter_map f g l

theorem filter_map_map (f : α → β) (g : β → option γ) (s : multiset α) :
  filter_map g (map f s) = filter_map (g ∘ f) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_map f g l

theorem filter_filter_map (f : α → option β) (p : β → Prop) [decidable_pred p] (s : multiset α) :
  filter p (filter_map f s) = filter_map (λ x, (f x).filter p) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_filter_map f p l

theorem filter_map_filter (f : α → option β) (s : multiset α) :
  filter_map f (filter p s) = filter_map (λ x, if p x then f x else none) s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_filter p f l

@[simp] theorem filter_map_some (s : multiset α) : filter_map some s = s :=
quot.induction_on s $ λ l, congr_arg coe $ filter_map_some l

@[simp] theorem mem_filter_map (f : α → option β) (s : multiset α) {b : β} :
  b ∈ filter_map f s ↔ ∃ a, a ∈ s ∧ f a = some b :=
quot.induction_on s $ λ l, mem_filter_map f l

theorem map_filter_map_of_inv (f : α → option β) (g : β → α)
  (H : ∀ x : α, (f x).map g = some x) (s : multiset α) :
  map g (filter_map f s) = s :=
quot.induction_on s $ λ l, congr_arg coe $ map_filter_map_of_inv f g H l

theorem filter_map_le_filter_map (f : α → option β) {s t : multiset α}
  (h : s ≤ t) : filter_map f s ≤ filter_map f t :=
le_induction_on h $ λ l₁ l₂ h, (h.filter_map _).subperm

/-! ### countp -/

/-- `countp p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
def countp (s : multiset α) : ℕ :=
quot.lift_on s (countp p) (λ l₁ l₂, perm.countp_eq p)

@[simp] theorem coe_countp (l : list α) : countp p l = l.countp p := rfl

@[simp] theorem countp_zero : countp p 0 = 0 := rfl

variable {p}

@[simp] theorem countp_cons_of_pos {a : α} (s) : p a → countp p (a ::ₘ s) = countp p s + 1 :=
quot.induction_on s $ countp_cons_of_pos p

@[simp] theorem countp_cons_of_neg {a : α} (s) : ¬ p a → countp p (a ::ₘ s) = countp p s :=
quot.induction_on s $ countp_cons_of_neg p

variable (p)

theorem countp_cons (b : α) (s) : countp p (b ::ₘ s) = countp p s + (if p b then 1 else 0) :=
begin
  split_ifs with h;
  simp only [h, multiset.countp_cons_of_pos, add_zero, multiset.countp_cons_of_neg, not_false_iff],
end

theorem countp_eq_card_filter (s) : countp p s = card (filter p s) :=
quot.induction_on s $ λ l, countp_eq_length_filter _ _

@[simp] theorem countp_add (s t) : countp p (s + t) = countp p s + countp p t :=
by simp [countp_eq_card_filter]

/-- `countp p`, the number of elements of a multiset satisfying `p`, promoted to an
`add_monoid_hom`. -/
def countp_add_monoid_hom : multiset α →+ ℕ :=
{ to_fun := countp p,
  map_zero' := countp_zero _,
  map_add' := countp_add _ }

@[simp] lemma coe_countp_add_monoid_hom :
  (countp_add_monoid_hom p : multiset α → ℕ) = countp p := rfl

@[simp] theorem countp_sub [decidable_eq α] {s t : multiset α} (h : t ≤ s) :
  countp p (s - t) = countp p s - countp p t :=
by simp [countp_eq_card_filter, h, filter_le_filter]

theorem countp_le_of_le {s t} (h : s ≤ t) : countp p s ≤ countp p t :=
by simpa [countp_eq_card_filter] using card_le_of_le (filter_le_filter p h)

@[simp] theorem countp_filter (q) [decidable_pred q] (s : multiset α) :
  countp p (filter q s) = countp (λ a, p a ∧ q a) s :=
by simp [countp_eq_card_filter]

theorem countp_map (f : α → β) (s : multiset α) (p : β → Prop) [decidable_pred p] :
  countp p (map f s) = (s.filter (λ a, p (f a))).card :=
begin
  refine multiset.induction_on s _ (λ a t IH, _),
  { rw [map_zero, countp_zero, filter_zero, card_zero] },
  { rw [map_cons, countp_cons, IH, filter_cons, card_add, apply_ite card, card_zero,
      card_singleton, add_comm] },
end

variable {p}

theorem countp_pos {s} : 0 < countp p s ↔ ∃ a ∈ s, p a :=
by simp [countp_eq_card_filter, card_pos_iff_exists_mem]

theorem countp_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countp p s :=
countp_pos.2 ⟨_, h, pa⟩

end

/-! ### Multiplicity of an element -/

section
variable [decidable_eq α]

/-- `count a s` is the multiplicity of `a` in `s`. -/
def count (a : α) : multiset α → ℕ := countp (eq a)

@[simp] theorem coe_count (a : α) (l : list α) : count a (↑l) = l.count a := coe_countp _ _

@[simp] theorem count_zero (a : α) : count a 0 = 0 := rfl

@[simp] theorem count_cons_self (a : α) (s : multiset α) : count a (a ::ₘ s) = succ (count a s) :=
countp_cons_of_pos _ rfl

@[simp, priority 990]
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : multiset α) : count a (b ::ₘ s) = count a s :=
countp_cons_of_neg _ h

theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
countp_le_of_le _

theorem count_le_count_cons (a b : α) (s : multiset α) : count a s ≤ count a (b ::ₘ s) :=
count_le_of_le _ (le_cons_self _ _)

theorem count_cons (a b : α) (s : multiset α) :
  count a (b ::ₘ s) = count a s + (if a = b then 1 else 0) :=
by by_cases h : a = b; simp [h]

theorem count_singleton_self (a : α) : count a ({a} : multiset α) = 1 :=
by simp only [count_cons_self, singleton_eq_cons, eq_self_iff_true, count_zero]

theorem count_singleton (a b : α) : count a ({b} : multiset α) = if a = b then 1 else 0 :=
by simp only [count_cons, singleton_eq_cons, count_zero, zero_add]

@[simp] theorem count_add (a : α) : ∀ s t, count a (s + t) = count a s + count a t :=
countp_add _

/-- `count a`, the multiplicity of `a` in a multiset, promoted to an `add_monoid_hom`. -/
def count_add_monoid_hom (a : α) : multiset α →+ ℕ := countp_add_monoid_hom (eq a)

@[simp] lemma coe_count_add_monoid_hom {a : α} :
  (count_add_monoid_hom a : multiset α → ℕ) = count a := rfl

@[simp] theorem count_nsmul (a : α) (n s) : count a (n • s) = n * count a s :=
by induction n; simp [*, succ_nsmul', succ_mul, zero_nsmul]

theorem count_pos {a : α} {s : multiset α} : 0 < count a s ↔ a ∈ s :=
by simp [count, countp_pos]

theorem one_le_count_iff_mem {a : α} {s : multiset α} : 1 ≤ count a s ↔ a ∈ s :=
by rw [succ_le_iff, count_pos]

@[simp, priority 980]
theorem count_eq_zero_of_not_mem {a : α} {s : multiset α} (h : a ∉ s) : count a s = 0 :=
by_contradiction $ λ h', h $ count_pos.1 (nat.pos_of_ne_zero h')

@[simp] theorem count_eq_zero {a : α} {s : multiset α} : count a s = 0 ↔ a ∉ s :=
iff_not_comm.1 $ count_pos.symm.trans pos_iff_ne_zero

theorem count_ne_zero {a : α} {s : multiset α} : count a s ≠ 0 ↔ a ∈ s :=
by simp [ne.def, count_eq_zero]

@[simp] theorem count_repeat_self (a : α) (n : ℕ) : count a (repeat a n) = n :=
by simp [repeat]

theorem count_repeat (a b : α) (n : ℕ)  :
  count a (repeat b n) = if (a = b) then n else 0 :=
begin
  split_ifs with h₁,
  { rw [h₁, count_repeat_self] },
  { rw [count_eq_zero],
    apply mt eq_of_mem_repeat h₁ },
end

@[simp] theorem count_erase_self (a : α) (s : multiset α) :
  count a (erase s a) = pred (count a s) :=
begin
  by_cases a ∈ s,
  { rw [(by rw cons_erase h : count a s = count a (a ::ₘ erase s a)),
        count_cons_self]; refl },
  { rw [erase_of_not_mem h, count_eq_zero.2 h]; refl }
end

@[simp, priority 980] theorem count_erase_of_ne {a b : α} (ab : a ≠ b) (s : multiset α) :
  count a (erase s b) = count a s :=
begin
  by_cases b ∈ s,
  { rw [← count_cons_of_ne ab, cons_erase h] },
  { rw [erase_of_not_mem h] }
end

@[simp] theorem count_sub (a : α) (s t : multiset α) : count a (s - t) = count a s - count a t :=
begin
  revert s, refine multiset.induction_on t (by simp) (λ b t IH s, _),
  rw [sub_cons, IH],
  by_cases ab : a = b,
  { subst b, rw [count_erase_self, count_cons_self, sub_succ, pred_sub] },
  { rw [count_erase_of_ne ab, count_cons_of_ne ab] }
end

@[simp] theorem count_union (a : α) (s t : multiset α) :
  count a (s ∪ t) = max (count a s) (count a t) :=
by simp [(∪), union, tsub_add_eq_max, -add_comm]

@[simp] theorem count_inter (a : α) (s t : multiset α) :
  count a (s ∩ t) = min (count a s) (count a t) :=
begin
  apply @nat.add_left_cancel (count a (s - t)),
  rw [← count_add, sub_add_inter, count_sub, tsub_add_min],
end

theorem le_count_iff_repeat_le {a : α} {s : multiset α} {n : ℕ} : n ≤ count a s ↔ repeat a n ≤ s :=
quot.induction_on s $ λ l, le_count_iff_repeat_sublist.trans repeat_le_coe.symm

@[simp] theorem count_filter_of_pos {p} [decidable_pred p]
  {a} {s : multiset α} (h : p a) : count a (filter p s) = count a s :=
quot.induction_on s $ λ l, count_filter h

@[simp] theorem count_filter_of_neg {p} [decidable_pred p]
  {a} {s : multiset α} (h : ¬ p a) : count a (filter p s) = 0 :=
multiset.count_eq_zero_of_not_mem (λ t, h (of_mem_filter t))

theorem count_filter {p} [decidable_pred p] {a} {s : multiset α} :
  count a (filter p s) = if p a then count a s else 0 :=
begin
  split_ifs with h,
  { exact count_filter_of_pos h },
  { exact count_filter_of_neg h },
end

theorem ext {s t : multiset α} : s = t ↔ ∀ a, count a s = count a t :=
quotient.induction_on₂ s t $ λ l₁ l₂, quotient.eq.trans perm_iff_count

@[ext]
theorem ext' {s t : multiset α} : (∀ a, count a s = count a t) → s = t :=
ext.2

@[simp] theorem coe_inter (s t : list α) : (s ∩ t : multiset α) = (s.bag_inter t : list α) :=
by ext; simp

theorem le_iff_count {s t : multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
⟨λ h a, count_le_of_le a h, λ al,
 by rw ← (ext.2 (λ a, by simp [max_eq_right (al a)]) : s ∪ t = t);
    apply le_union_left⟩

instance : distrib_lattice (multiset α) :=
{ le_sup_inf := λ s t u, le_of_eq $ eq.symm $
    ext.2 $ λ a, by simp only [max_min_distrib_left,
      multiset.count_inter, multiset.sup_eq_union, multiset.count_union, multiset.inf_eq_inter],
  ..multiset.lattice }

theorem repeat_inf (s : multiset α) (a : α) (n : ℕ) :
  (repeat a n) ⊓ s = repeat a (min (s.count a) n) :=
begin
  ext x,
  rw [inf_eq_inter, count_inter, count_repeat, count_repeat],
  by_cases x = a,
    simp only [min_comm, h, if_true, eq_self_iff_true],
    simp only [h, if_false, zero_min],
end

theorem count_map {α β : Type*} (f : α → β) (s : multiset α) [decidable_eq β] (b : β) :
  count b (map f s) = (s.filter (λ a, b = f a)).card :=
countp_map _ _ _

/-- `multiset.map f` preserves `count` if `f` is injective on the set of elements contained in
the multiset -/
theorem count_map_eq_count [decidable_eq β] (f : α → β) (s : multiset α)
  (hf : set.inj_on f {x : α | x ∈ s}) (x ∈ s) : (s.map f).count (f x) = s.count x :=
begin
  suffices : (filter (λ (a : α), f x = f a) s).count x = card (filter (λ (a : α), f x = f a) s),
  { rw [count, countp_map, ← this],
    exact count_filter_of_pos rfl },
  { rw eq_repeat.2 ⟨rfl, λ b hb, eq_comm.1 ((hf H (mem_filter.1 hb).left) (mem_filter.1 hb).right)⟩,
    simp only [count_repeat, eq_self_iff_true, if_true, card_repeat]},
end

/-- `multiset.map f` preserves `count` if `f` is injective -/
theorem count_map_eq_count' [decidable_eq β] (f : α → β) (s : multiset α)
  (hf : function.injective f) (x : α) : (s.map f).count (f x) = s.count x :=
begin
  by_cases H : x ∈ s,
  { exact count_map_eq_count f _ (set.inj_on_of_injective hf _) _ H, },
  { rw [count_eq_zero_of_not_mem H, count_eq_zero, mem_map],
    rintro ⟨k, hks, hkx⟩,
    rw hf hkx at *,
    contradiction }
end

lemma filter_eq' (s : multiset α) (b : α) : s.filter (= b) = repeat b (count b s) :=
begin
  ext a,
  rw [count_repeat, count_filter],
  exact if_ctx_congr iff.rfl (λ h, congr_arg _ h) (λ h, rfl),
end

lemma filter_eq (s : multiset α) (b : α) : s.filter (eq b) = repeat b (count b s) :=
by simp_rw [←filter_eq', eq_comm]

end

lemma count_eq_card_filter_eq [decidable_eq α] (s : multiset α) (a : α) :
  s.count a = (s.filter (eq a)).card :=
by rw [count, countp_eq_card_filter]

/--
Mapping a multiset through a predicate and counting the `true`s yields the cardinality of the set
filtered by the predicate. Note that this uses the notion of a multiset of `Prop`s - due to the
decidability requirements of `count`, the decidability instance on the LHS is different from the
RHS. In particular, the decidability instance on the left leaks `classical.dec_eq`.
See [here](https://github.com/leanprover-community/mathlib/pull/11306#discussion_r782286812)
for more discussion.
-/
@[simp] lemma map_count_true_eq_filter_card (s : multiset α) (p : α → Prop) [decidable_pred p] :
  (s.map p).count true = (s.filter p).card :=
by simp only [count_eq_card_filter_eq, map_filter, card_map, function.comp.left_id, eq_true_eq_id]

/-! ### Lift a relation to `multiset`s -/

section rel

/-- `rel r s t` -- lift the relation `r` between two elements to a relation between `s` and `t`,
s.t. there is a one-to-one mapping betweem elements in `s` and `t` following `r`. -/
@[mk_iff] inductive rel (r : α → β → Prop) : multiset α → multiset β → Prop
| zero : rel 0 0
| cons {a b as bs} : r a b → rel as bs → rel (a ::ₘ as) (b ::ₘ bs)

variables {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

private lemma rel_flip_aux {s t} (h : rel r s t) : rel (flip r) t s :=
rel.rec_on h rel.zero (assume _ _ _ _ h₀ h₁ ih, rel.cons h₀ ih)

lemma rel_flip {s t} : rel (flip r) s t ↔ rel r t s :=
⟨rel_flip_aux, rel_flip_aux⟩

lemma rel_refl_of_refl_on {m : multiset α} {r : α → α → Prop} :
  (∀ x ∈ m, r x x) → rel r m m :=
begin
  apply m.induction_on,
  { intros, apply rel.zero },
  { intros a m ih h,
    exact rel.cons (h _ (mem_cons_self _ _)) (ih (λ _ ha, h _ (mem_cons_of_mem ha))) }
end

lemma rel_eq_refl {s : multiset α} : rel (=) s s :=
rel_refl_of_refl_on (λ x hx, rfl)

lemma rel_eq {s t : multiset α} : rel (=) s t ↔ s = t :=
begin
  split,
  { assume h, induction h; simp * },
  { assume h, subst h, exact rel_eq_refl }
end

lemma rel.mono {r p : α → β → Prop} {s t} (hst : rel r s t) (h : ∀(a ∈ s) (b ∈ t), r a b → p a b) :
  rel p s t :=
begin
  induction hst,
  case rel.zero { exact rel.zero },
  case rel.cons : a b s t hab hst ih
  { apply rel.cons (h a (mem_cons_self _ _) b (mem_cons_self _ _) hab),
    exact ih (λ a' ha' b' hb' h', h a' (mem_cons_of_mem ha') b' (mem_cons_of_mem hb') h') }
end

lemma rel.add {s t u v} (hst : rel r s t) (huv : rel r u v) : rel r (s + u) (t + v) :=
begin
  induction hst,
  case rel.zero { simpa using huv },
  case rel.cons : a b s t hab hst ih { simpa using ih.cons hab }
end

lemma rel_flip_eq  {s t : multiset α} : rel (λa b, b = a) s t ↔ s = t :=
show rel (flip (=)) s t ↔ s = t, by rw [rel_flip, rel_eq, eq_comm]

@[simp] lemma rel_zero_left {b : multiset β} : rel r 0 b ↔ b = 0 :=
by rw [rel_iff]; simp

@[simp] lemma rel_zero_right {a : multiset α} : rel r a 0 ↔ a = 0 :=
by rw [rel_iff]; simp

lemma rel_cons_left {a as bs} :
  rel r (a ::ₘ as) bs ↔ (∃b bs', r a b ∧ rel r as bs' ∧ bs = b ::ₘ bs') :=
begin
  split,
  { generalize hm : a ::ₘ as = m,
    assume h,
    induction h generalizing as,
    case rel.zero { simp at hm, contradiction },
    case rel.cons : a' b as' bs ha'b h ih
    { rcases cons_eq_cons.1 hm with ⟨eq₁, eq₂⟩ | ⟨h, cs, eq₁, eq₂⟩,
      { subst eq₁, subst eq₂, exact ⟨b, bs, ha'b, h, rfl⟩ },
      { rcases ih eq₂.symm with ⟨b', bs', h₁, h₂, eq⟩,
        exact ⟨b', b ::ₘ bs', h₁, eq₁.symm ▸ rel.cons ha'b h₂, eq.symm ▸ cons_swap _ _ _⟩ } } },
  { exact assume ⟨b, bs', hab, h, eq⟩, eq.symm ▸ rel.cons hab h }
end

lemma rel_cons_right {as b bs} :
  rel r as (b ::ₘ bs) ↔ (∃a as', r a b ∧ rel r as' bs ∧ as = a ::ₘ as') :=
begin
  rw [← rel_flip, rel_cons_left],
  refine exists₂_congr (λ a as', _),
  rw [rel_flip, flip]
end

lemma rel_add_left {as₀ as₁} :
  ∀{bs}, rel r (as₀ + as₁) bs ↔ (∃bs₀ bs₁, rel r as₀ bs₀ ∧ rel r as₁ bs₁ ∧ bs = bs₀ + bs₁) :=
multiset.induction_on as₀ (by simp)
  begin
    assume a s ih bs,
    simp only [ih, cons_add, rel_cons_left],
    split,
    { assume h,
      rcases h with ⟨b, bs', hab, h, rfl⟩,
      rcases h with ⟨bs₀, bs₁, h₀, h₁, rfl⟩,
      exact ⟨b ::ₘ bs₀, bs₁, ⟨b, bs₀, hab, h₀, rfl⟩, h₁, by simp⟩ },
    { assume h,
      rcases h with ⟨bs₀, bs₁, h, h₁, rfl⟩,
      rcases h with ⟨b, bs, hab, h₀, rfl⟩,
      exact ⟨b, bs + bs₁, hab, ⟨bs, bs₁, h₀, h₁, rfl⟩, by simp⟩ }
  end

lemma rel_add_right {as bs₀ bs₁} :
  rel r as (bs₀ + bs₁) ↔ (∃as₀ as₁, rel r as₀ bs₀ ∧ rel r as₁ bs₁ ∧ as = as₀ + as₁) :=
by rw [← rel_flip, rel_add_left]; simp [rel_flip]

lemma rel_map_left {s : multiset γ} {f : γ → α} :
  ∀{t}, rel r (s.map f) t ↔ rel (λa b, r (f a) b) s t :=
multiset.induction_on s (by simp) (by simp [rel_cons_left] {contextual := tt})

lemma rel_map_right {s : multiset α} {t : multiset γ} {f : γ → β} :
  rel r s (t.map f) ↔ rel (λa b, r a (f b)) s t :=
by rw [← rel_flip, rel_map_left, ← rel_flip]; refl

lemma rel_map {s : multiset α} {t : multiset β} {f : α → γ} {g : β → δ} :
  rel p (s.map f) (t.map g) ↔ rel (λa b, p (f a) (g b)) s t :=
rel_map_left.trans rel_map_right

lemma card_eq_card_of_rel {r : α → β → Prop} {s : multiset α} {t : multiset β} (h : rel r s t) :
  card s = card t :=
by induction h; simp [*]

lemma exists_mem_of_rel_of_mem {r : α → β → Prop} {s : multiset α} {t : multiset β}
  (h : rel r s t) :
  ∀ {a : α} (ha : a ∈ s), ∃ b ∈ t, r a b :=
begin
  induction h with x y s t hxy hst ih,
  { simp },
  { assume a ha,
    cases mem_cons.1 ha with ha ha,
    { exact ⟨y, mem_cons_self _ _, ha.symm ▸ hxy⟩ },
    { rcases ih ha with ⟨b, hbt, hab⟩,
      exact ⟨b, mem_cons.2 (or.inr hbt), hab⟩ } }
end

lemma rel_of_forall {m1 m2 : multiset α} {r : α → α → Prop} (h : ∀ a b, a ∈ m1 → b ∈ m2 → r a b)
   (hc : card m1 = card m2) :
   m1.rel r m2 :=
begin
  revert m1,
  apply m2.induction_on,
  { intros m h hc,
    rw [rel_zero_right, ← card_eq_zero, hc, card_zero] },
  { intros a t ih m h hc,
    rw card_cons at hc,
    obtain ⟨b, hb⟩ := card_pos_iff_exists_mem.1 (show 0 < card m, from hc.symm ▸ (nat.succ_pos _)),
    obtain ⟨m', rfl⟩ := exists_cons_of_mem hb,
    refine rel_cons_right.mpr ⟨b, m', h _ _ hb (mem_cons_self _ _), ih _ _, rfl⟩,
    { exact λ _ _ ha hb, h _ _ (mem_cons_of_mem ha) (mem_cons_of_mem hb) },
    { simpa using hc } }
end

lemma rel_repeat_left {m : multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
  (repeat a n).rel r m ↔ m.card = n ∧ ∀ x, x ∈ m → r a x :=
⟨λ h, ⟨(card_eq_card_of_rel h).symm.trans (card_repeat _ _), λ x hx, begin
    obtain ⟨b, hb1, hb2⟩ := exists_mem_of_rel_of_mem (rel_flip.2 h) hx,
    rwa eq_of_mem_repeat hb1 at hb2,
  end⟩,
  λ h, rel_of_forall (λ x y hx hy, (eq_of_mem_repeat hx).symm ▸ (h.2 _ hy))
  (eq.trans (card_repeat _ _) h.1.symm)⟩

lemma rel_repeat_right {m : multiset α} {a : α} {r : α → α → Prop} {n : ℕ} :
  m.rel r (repeat a n) ↔ m.card = n ∧ ∀ x, x ∈ m → r x a :=
by { rw [← rel_flip], exact rel_repeat_left }

end rel

section map

theorem map_eq_map {f : α → β} (hf : function.injective f) {s t : multiset α} :
  s.map f = t.map f ↔ s = t :=
by { rw [← rel_eq, ← rel_eq, rel_map], simp only [hf.eq_iff] }

theorem map_injective {f : α → β} (hf : function.injective f) :
  function.injective (multiset.map f) :=
assume x y, (map_eq_map hf).1

end map

section quot

theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : multiset α} (hst : s.rel r t) :
 s.map (quot.mk r) = t.map (quot.mk r) :=
rel.rec_on hst rfl $ assume a b s t hab hst ih, by simp [ih, quot.sound hab]

theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : multiset (quot r)) :
  ∃t:multiset α, s = t.map (quot.mk r) :=
multiset.induction_on s ⟨0, rfl⟩ $
  assume a s ⟨t, ht⟩, quot.induction_on a $ assume a, ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

theorem induction_on_multiset_quot
  {r : α → α → Prop} {p : multiset (quot r) → Prop} (s : multiset (quot r)) :
  (∀s:multiset α, p (s.map (quot.mk r))) → p s :=
match s, exists_multiset_eq_map_quot_mk s with _, ⟨t, rfl⟩ := assume h, h _ end

end quot

/-! ### Disjoint multisets -/

/-- `disjoint s t` means that `s` and `t` have no elements in common. -/
def disjoint (s t : multiset α) : Prop := ∀ ⦃a⦄, a ∈ s → a ∈ t → false

@[simp] theorem coe_disjoint (l₁ l₂ : list α) : @disjoint α l₁ l₂ ↔ l₁.disjoint l₂ := iff.rfl

theorem disjoint.symm {s t : multiset α} (d : disjoint s t) : disjoint t s
| a i₂ i₁ := d i₁ i₂

theorem disjoint_comm {s t : multiset α} : disjoint s t ↔ disjoint t s :=
⟨disjoint.symm, disjoint.symm⟩

theorem disjoint_left {s t : multiset α} : disjoint s t ↔ ∀ {a}, a ∈ s → a ∉ t := iff.rfl

theorem disjoint_right {s t : multiset α} : disjoint s t ↔ ∀ {a}, a ∈ t → a ∉ s :=
disjoint_comm

theorem disjoint_iff_ne {s t : multiset α} : disjoint s t ↔ ∀ a ∈ s, ∀ b ∈ t, a ≠ b :=
by simp [disjoint_left, imp_not_comm]

theorem disjoint_of_subset_left {s t u : multiset α} (h : s ⊆ u) (d : disjoint u t) : disjoint s t
| x m₁ := d (h m₁)

theorem disjoint_of_subset_right {s t u : multiset α} (h : t ⊆ u) (d : disjoint s u) : disjoint s t
| x m m₁ := d m (h m₁)

theorem disjoint_of_le_left {s t u : multiset α} (h : s ≤ u) : disjoint u t → disjoint s t :=
disjoint_of_subset_left (subset_of_le h)

theorem disjoint_of_le_right {s t u : multiset α} (h : t ≤ u) : disjoint s u → disjoint s t :=
disjoint_of_subset_right (subset_of_le h)

@[simp] theorem zero_disjoint (l : multiset α) : disjoint 0 l
| a := (not_mem_nil a).elim

@[simp, priority 1100]
theorem singleton_disjoint {l : multiset α} {a : α} : disjoint {a} l ↔ a ∉ l :=
by simp [disjoint]; refl

@[simp, priority 1100]
theorem disjoint_singleton {l : multiset α} {a : α} : disjoint l {a} ↔ a ∉ l :=
by rw [disjoint_comm, singleton_disjoint]

@[simp] theorem disjoint_add_left {s t u : multiset α} :
  disjoint (s + t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_add_right {s t u : multiset α} :
  disjoint s (t + u) ↔ disjoint s t ∧ disjoint s u :=
by rw [disjoint_comm, disjoint_add_left]; tauto

@[simp] theorem disjoint_cons_left {a : α} {s t : multiset α} :
  disjoint (a ::ₘ s) t ↔ a ∉ t ∧ disjoint s t :=
(@disjoint_add_left _ {a} s t).trans $ by rw singleton_disjoint

@[simp] theorem disjoint_cons_right {a : α} {s t : multiset α} :
  disjoint s (a ::ₘ t) ↔ a ∉ s ∧ disjoint s t :=
by rw [disjoint_comm, disjoint_cons_left]; tauto

theorem inter_eq_zero_iff_disjoint [decidable_eq α] {s t : multiset α} : s ∩ t = 0 ↔ disjoint s t :=
by rw ← subset_zero; simp [subset_iff, disjoint]

@[simp] theorem disjoint_union_left [decidable_eq α] {s t u : multiset α} :
  disjoint (s ∪ t) u ↔ disjoint s u ∧ disjoint t u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

@[simp] theorem disjoint_union_right [decidable_eq α] {s t u : multiset α} :
  disjoint s (t ∪ u) ↔ disjoint s t ∧ disjoint s u :=
by simp [disjoint, or_imp_distrib, forall_and_distrib]

lemma add_eq_union_iff_disjoint [decidable_eq α] {s t : multiset α} :
  s + t = s ∪ t ↔ disjoint s t :=
by simp_rw [←inter_eq_zero_iff_disjoint, ext, count_add, count_union, count_inter, count_zero,
            nat.min_eq_zero_iff, nat.add_eq_max_iff]

lemma disjoint_map_map {f : α → γ} {g : β → γ} {s : multiset α} {t : multiset β} :
  disjoint (s.map f) (t.map g) ↔ (∀a∈s, ∀b∈t, f a ≠ g b) :=
by { simp [disjoint, @eq_comm _ (f _) (g _)], refl }

/-- `pairwise r m` states that there exists a list of the elements s.t. `r` holds pairwise on this
list. -/
def pairwise (r : α → α → Prop) (m : multiset α) : Prop :=
∃l:list α, m = l ∧ l.pairwise r

lemma pairwise_coe_iff_pairwise {r : α → α → Prop} (hr : symmetric r) {l : list α} :
  multiset.pairwise r l ↔ l.pairwise r :=
iff.intro
  (assume ⟨l', eq, h⟩, ((quotient.exact eq).pairwise_iff hr).2 h)
  (assume h, ⟨l, rfl, h⟩)

end multiset

namespace multiset

section choose
variables (p : α → Prop) [decidable_pred p] (l : multiset α)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose_x p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
def choose_x : Π hp : (∃! a, a ∈ l ∧ p a), { a // a ∈ l ∧ p a } :=
quotient.rec_on l (λ l' ex_unique, list.choose_x p l' (exists_of_exists_unique ex_unique)) begin
  intros,
  funext hp,
  suffices all_equal : ∀ x y : { t // t ∈ b ∧ p t }, x = y,
  { apply all_equal },
  { rintros ⟨x, px⟩ ⟨y, py⟩,
    rcases hp with ⟨z, ⟨z_mem_l, pz⟩, z_unique⟩,
    congr,
    calc x = z : z_unique x px
    ...    = y : (z_unique y py).symm }
end

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α := choose_x p l hp

lemma choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
(choose_x p l hp).property

lemma choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l := (choose_spec _ _ _).1

lemma choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) := (choose_spec _ _ _).2

end choose

variable (α)

/-- The equivalence between lists and multisets of a subsingleton type. -/
def subsingleton_equiv [subsingleton α] : list α ≃ multiset α :=
{ to_fun := coe,
  inv_fun := quot.lift id $ λ (a b : list α) (h : a ~ b),
    list.ext_le h.length_eq $ λ n h₁ h₂, subsingleton.elim _ _,
  left_inv := λ l, rfl,
  right_inv := λ m, quot.induction_on m $ λ l, rfl }

variable {α}

@[simp]
lemma coe_subsingleton_equiv [subsingleton α] :
  (subsingleton_equiv α : list α → multiset α) = coe :=
rfl

end multiset
