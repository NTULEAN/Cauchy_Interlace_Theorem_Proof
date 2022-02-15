/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.monotone
import order.rel_classes
import tactic.simps
import tactic.pi_instances

/-!
# (Semi-)lattices

Semilattices are partially ordered sets with join (greatest lower bound, or `sup`) or
meet (least upper bound, or `inf`) operations. Lattices are posets that are both
join-semilattices and meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.

## Main declarations

* `has_sup`: type class for the `⊔` notation
* `has_inf`: type class for the `⊓` notation

* `semilattice_sup`: a type class for join semilattices
* `semilattice_sup.mk'`: an alternative constructor for `semilattice_sup` via proofs that `⊔` is
  commutative, associative and idempotent.
* `semilattice_inf`: a type class for meet semilattices
* `semilattice_sup.mk'`: an alternative constructor for `semilattice_inf` via proofs that `⊓` is
  commutative, associative and idempotent.

* `lattice`: a type class for lattices
* `lattice.mk'`: an alternative constructor for `lattice` via profs that `⊔` and `⊓` are
  commutative, associative and satisfy a pair of "absorption laws".

* `distrib_lattice`: a type class for distributive lattices.

## Notations

* `a ⊔ b`: the supremum or join of `a` and `b`
* `a ⊓ b`: the infimum or meet of `a` and `b`

## TODO

* (Semi-)lattice homomorphisms
* Alternative constructors for distributive lattices from the other distributive properties

## Tags

semilattice, lattice

-/
set_option old_structure_cmd true

universes u v w

variables {α : Type u} {β : Type v}

-- TODO: move this eventually, if we decide to use them
attribute [ematch] le_trans lt_of_le_of_lt lt_of_lt_of_le lt_trans

section
-- TODO: this seems crazy, but it also seems to work reasonably well
@[ematch] theorem le_antisymm' [partial_order α] : ∀ {a b : α}, (: a ≤ b :) → b ≤ a → a = b :=
@le_antisymm _ _
end

/- TODO: automatic construction of dual definitions / theorems -/

/-- Typeclass for the `⊔` (`\lub`) notation -/
@[notation_class] class has_sup (α : Type u) := (sup : α → α → α)
/-- Typeclass for the `⊓` (`\glb`) notation -/
@[notation_class] class has_inf (α : Type u) := (inf : α → α → α)

infix ⊔ := has_sup.sup
infix ⊓ := has_inf.inf

/-!
### Join-semilattices
-/

/-- A `semilattice_sup` is a join-semilattice, that is, a partial order
  with a join (a.k.a. lub / least upper bound, sup / supremum) operation
  `⊔` which is the least element larger than both factors. -/
class semilattice_sup (α : Type u) extends has_sup α, partial_order α :=
(le_sup_left : ∀ a b : α, a ≤ a ⊔ b)
(le_sup_right : ∀ a b : α, b ≤ a ⊔ b)
(sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c)

/--
A type with a commutative, associative and idempotent binary `sup` operation has the structure of a
join-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def semilattice_sup.mk' {α : Type*} [has_sup α]
  (sup_comm : ∀ (a b : α), a ⊔ b = b ⊔ a)
  (sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
  (sup_idem : ∀ (a : α), a ⊔ a = a) : semilattice_sup α :=
{ sup := (⊔),
  le := λ a b, a ⊔ b = b,
  le_refl := sup_idem,
  le_trans := λ a b c hab hbc,
    begin
      dsimp only [(≤)] at *,
      rwa [←hbc, ←sup_assoc, hab],
    end,
  le_antisymm := λ a b hab hba,
    begin
      dsimp only [(≤)] at *,
      rwa [←hba, sup_comm],
    end,
  le_sup_left  := λ a b, show a ⊔ (a ⊔ b) = (a ⊔ b), by rw [←sup_assoc, sup_idem],
  le_sup_right := λ a b, show b ⊔ (a ⊔ b) = (a ⊔ b), by rw [sup_comm, sup_assoc, sup_idem],
  sup_le := λ a b c hac hbc,
    begin
      dsimp only [(≤), preorder.le] at *,
      rwa [sup_assoc, hbc],
    end }

instance (α : Type*) [has_inf α] : has_sup (order_dual α) := ⟨((⊓) : α → α → α)⟩
instance (α : Type*) [has_sup α] : has_inf (order_dual α) := ⟨((⊔) : α → α → α)⟩

section semilattice_sup
variables [semilattice_sup α] {a b c d : α}

@[simp] theorem le_sup_left : a ≤ a ⊔ b :=
semilattice_sup.le_sup_left a b

@[ematch] theorem le_sup_left' : a ≤ (: a ⊔ b :) :=
le_sup_left

@[simp] theorem le_sup_right : b ≤ a ⊔ b :=
semilattice_sup.le_sup_right a b

@[ematch] theorem le_sup_right' : b ≤ (: a ⊔ b :) :=
le_sup_right

theorem le_sup_of_le_left (h : c ≤ a) : c ≤ a ⊔ b :=
le_trans h le_sup_left

theorem le_sup_of_le_right (h : c ≤ b) : c ≤ a ⊔ b :=
le_trans h le_sup_right

theorem lt_sup_of_lt_left (h : c < a) : c < a ⊔ b :=
h.trans_le le_sup_left

theorem lt_sup_of_lt_right (h : c < b) : c < a ⊔ b :=
h.trans_le le_sup_right

theorem sup_le : a ≤ c → b ≤ c → a ⊔ b ≤ c :=
semilattice_sup.sup_le a b c

@[simp] theorem sup_le_iff : a ⊔ b ≤ c ↔ a ≤ c ∧ b ≤ c :=
⟨assume h : a ⊔ b ≤ c, ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩,
  assume ⟨h₁, h₂⟩, sup_le h₁ h₂⟩

@[simp] theorem sup_eq_left : a ⊔ b = a ↔ b ≤ a :=
le_antisymm_iff.trans $ by simp [le_refl]

theorem sup_of_le_left (h : b ≤ a) : a ⊔ b = a :=
sup_eq_left.2 h

@[simp] theorem left_eq_sup : a = a ⊔ b ↔ b ≤ a :=
eq_comm.trans sup_eq_left

@[simp] theorem sup_eq_right : a ⊔ b = b ↔ a ≤ b :=
le_antisymm_iff.trans $ by simp [le_refl]

theorem sup_of_le_right (h : a ≤ b) : a ⊔ b = b :=
sup_eq_right.2 h

@[simp] theorem right_eq_sup : b = a ⊔ b ↔ a ≤ b :=
eq_comm.trans sup_eq_right

theorem sup_le_sup (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊔ c ≤ b ⊔ d :=
sup_le (le_sup_of_le_left h₁) (le_sup_of_le_right h₂)

theorem sup_le_sup_left (h₁ : a ≤ b) (c) : c ⊔ a ≤ c ⊔ b :=
sup_le_sup le_rfl h₁

theorem sup_le_sup_right (h₁ : a ≤ b) (c) : a ⊔ c ≤ b ⊔ c :=
sup_le_sup h₁ le_rfl

theorem le_of_sup_eq (h : a ⊔ b = b) : a ≤ b :=
by { rw ← h, simp }

lemma sup_ind [is_total α (≤)] (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊔ b) :=
(is_total.total a b).elim (λ h : a ≤ b, by rwa sup_eq_right.2 h) (λ h, by rwa sup_eq_left.2 h)

@[simp] lemma sup_lt_iff [is_total α (≤)] {a b c : α} : b ⊔ c < a ↔ b < a ∧ c < a :=
⟨λ h, ⟨le_sup_left.trans_lt h, le_sup_right.trans_lt h⟩, λ h, sup_ind b c h.1 h.2⟩

@[simp] lemma le_sup_iff [is_total α (≤)] {a b c : α} : a ≤ b ⊔ c ↔ a ≤ b ∨ a ≤ c :=
⟨λ h, (total_of (≤) c b).imp
  (λ bc, by rwa sup_eq_left.2 bc at h)
  (λ bc, by rwa sup_eq_right.2 bc at h),
 λ h, h.elim le_sup_of_le_left le_sup_of_le_right⟩

@[simp] lemma lt_sup_iff [is_total α (≤)] {a b c : α} : a < b ⊔ c ↔ a < b ∨ a < c :=
⟨λ h, (total_of (≤) c b).imp
  (λ bc, by rwa sup_eq_left.2 bc at h)
  (λ bc, by rwa sup_eq_right.2 bc at h),
 λ h, h.elim lt_sup_of_lt_left lt_sup_of_lt_right⟩

@[simp] theorem sup_idem : a ⊔ a = a :=
by apply le_antisymm; simp

instance sup_is_idempotent : is_idempotent α (⊔) := ⟨@sup_idem _ _⟩

theorem sup_comm : a ⊔ b = b ⊔ a :=
by apply le_antisymm; simp

instance sup_is_commutative : is_commutative α (⊔) := ⟨@sup_comm _ _⟩

theorem sup_assoc : a ⊔ b ⊔ c = a ⊔ (b ⊔ c) :=
le_antisymm
  (sup_le
    (sup_le le_sup_left (le_sup_of_le_right le_sup_left))
    (le_sup_of_le_right le_sup_right))
  (sup_le
    (le_sup_of_le_left le_sup_left)
    (sup_le (le_sup_of_le_left le_sup_right) le_sup_right))

instance sup_is_associative : is_associative α (⊔) := ⟨@sup_assoc _ _⟩

lemma sup_left_right_swap (a b c : α) : a ⊔ b ⊔ c = c ⊔ b ⊔ a :=
by rw [sup_comm, @sup_comm _ _ a, sup_assoc]

@[simp] lemma sup_left_idem : a ⊔ (a ⊔ b) = a ⊔ b :=
by rw [← sup_assoc, sup_idem]

@[simp] lemma sup_right_idem : (a ⊔ b) ⊔ b = a ⊔ b :=
by rw [sup_assoc, sup_idem]

lemma sup_left_comm (a b c : α) : a ⊔ (b ⊔ c) = b ⊔ (a ⊔ c) :=
by rw [← sup_assoc, ← sup_assoc, @sup_comm α _ a]

lemma sup_right_comm (a b c : α) : a ⊔ b ⊔ c = a ⊔ c ⊔ b :=
by rw [sup_assoc, sup_assoc, @sup_comm _ _ b]

lemma sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔ c ⊔ (b ⊔ d) :=
by rw [sup_assoc, sup_left_comm b, ←sup_assoc]

lemma forall_le_or_exists_lt_sup (a : α) : (∀b, b ≤ a) ∨ (∃b, a < b) :=
suffices (∃b, ¬b ≤ a) → (∃b, a < b),
  by rwa [or_iff_not_imp_left, not_forall],
assume ⟨b, hb⟩,
⟨a ⊔ b, lt_of_le_of_ne le_sup_left $ mt left_eq_sup.1 hb⟩

/-- If `f` is monotone, `g` is antitone, and `f ≤ g`, then for all `a`, `b` we have `f a ≤ g b`. -/
theorem monotone.forall_le_of_antitone {β : Type*} [preorder β] {f g : α → β}
  (hf : monotone f) (hg : antitone g) (h : f ≤ g) (m n : α) :
  f m ≤ g n :=
calc f m ≤ f (m ⊔ n) : hf le_sup_left
     ... ≤ g (m ⊔ n) : h _
     ... ≤ g n       : hg le_sup_right

theorem semilattice_sup.ext_sup {α} {A B : semilattice_sup α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y)
  (x y : α) : (by haveI := A; exact (x ⊔ y)) = x ⊔ y :=
eq_of_forall_ge_iff $ λ c,
by simp only [sup_le_iff]; rw [← H, @sup_le_iff α A, H, H]

theorem semilattice_sup.ext {α} {A B : semilattice_sup α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  have := partial_order.ext H,
  have ss := funext (λ x, funext $ semilattice_sup.ext_sup H x),
  casesI A, casesI B,
  injection this; congr'
end

theorem exists_lt_of_sup (α : Type*) [semilattice_sup α] [nontrivial α] : ∃ a b : α, a < b :=
begin
  rcases exists_pair_ne α with ⟨a, b, hne⟩,
  rcases forall_le_or_exists_lt_sup b with (hb|H),
  exacts [⟨a, b, (hb a).lt_of_ne hne⟩, ⟨b, H⟩]
end

lemma ite_le_sup (s s' : α) (P : Prop) [decidable P] : ite P s s' ≤ s ⊔ s' :=
if h : P then (if_pos h).trans_le le_sup_left else (if_neg h).trans_le le_sup_right

end semilattice_sup

/-!
### Meet-semilattices
-/

/-- A `semilattice_inf` is a meet-semilattice, that is, a partial order
  with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
  `⊓` which is the greatest element smaller than both factors. -/
class semilattice_inf (α : Type u) extends has_inf α, partial_order α :=
(inf_le_left : ∀ a b : α, a ⊓ b ≤ a)
(inf_le_right : ∀ a b : α, a ⊓ b ≤ b)
(le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c)

instance (α) [semilattice_inf α] : semilattice_sup (order_dual α) :=
{ le_sup_left  := semilattice_inf.inf_le_left,
  le_sup_right := semilattice_inf.inf_le_right,
  sup_le := assume a b c hca hcb, @semilattice_inf.le_inf α _ _ _ _ hca hcb,
  .. order_dual.partial_order α, .. order_dual.has_sup α }

instance (α) [semilattice_sup α] : semilattice_inf (order_dual α) :=
{ inf_le_left  := @le_sup_left α _,
  inf_le_right := @le_sup_right α _,
  le_inf := assume a b c hca hcb, @sup_le α _ _ _ _ hca hcb,
  .. order_dual.partial_order α, .. order_dual.has_inf α }

theorem semilattice_sup.dual_dual (α : Type*) [H : semilattice_sup α] :
  order_dual.semilattice_sup (order_dual α) = H :=
semilattice_sup.ext $ λ _ _, iff.rfl

section semilattice_inf
variables [semilattice_inf α] {a b c d : α}

@[simp] theorem inf_le_left : a ⊓ b ≤ a :=
semilattice_inf.inf_le_left a b

@[ematch] theorem inf_le_left' : (: a ⊓ b :) ≤ a :=
semilattice_inf.inf_le_left a b

@[simp] theorem inf_le_right : a ⊓ b ≤ b :=
semilattice_inf.inf_le_right a b

@[ematch] theorem inf_le_right' : (: a ⊓ b :) ≤ b :=
semilattice_inf.inf_le_right a b

theorem le_inf : a ≤ b → a ≤ c → a ≤ b ⊓ c :=
semilattice_inf.le_inf a b c

theorem inf_le_of_left_le (h : a ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_left h

theorem inf_le_of_right_le (h : b ≤ c) : a ⊓ b ≤ c :=
le_trans inf_le_right h

theorem inf_lt_of_left_lt (h : a < c) : a ⊓ b < c :=
lt_of_le_of_lt inf_le_left h

theorem inf_lt_of_right_lt (h : b < c) : a ⊓ b < c :=
lt_of_le_of_lt inf_le_right h

@[simp] theorem le_inf_iff : a ≤ b ⊓ c ↔ a ≤ b ∧ a ≤ c :=
@sup_le_iff (order_dual α) _ _ _ _

@[simp] theorem inf_eq_left : a ⊓ b = a ↔ a ≤ b :=
le_antisymm_iff.trans $ by simp [le_refl]

theorem inf_of_le_left (h : a ≤ b) : a ⊓ b = a :=
inf_eq_left.2 h

@[simp] theorem left_eq_inf : a = a ⊓ b ↔ a ≤ b :=
eq_comm.trans inf_eq_left

@[simp] theorem inf_eq_right : a ⊓ b = b ↔ b ≤ a :=
le_antisymm_iff.trans $ by simp [le_refl]

theorem inf_of_le_right (h : b ≤ a) : a ⊓ b = b :=
inf_eq_right.2 h

@[simp] theorem right_eq_inf : b = a ⊓ b ↔ b ≤ a :=
eq_comm.trans inf_eq_right

theorem inf_le_inf (h₁ : a ≤ b) (h₂ : c ≤ d) : a ⊓ c ≤ b ⊓ d :=
le_inf (inf_le_of_left_le h₁) (inf_le_of_right_le h₂)

lemma inf_le_inf_right (a : α) {b c : α} (h : b ≤ c) : b ⊓ a ≤ c ⊓ a :=
inf_le_inf h le_rfl

lemma inf_le_inf_left (a : α) {b c : α} (h : b ≤ c) : a ⊓ b ≤ a ⊓ c :=
inf_le_inf le_rfl h

theorem le_of_inf_eq (h : a ⊓ b = a) : a ≤ b :=
by { rw ← h, simp }

lemma inf_ind [is_total α (≤)] (a b : α) {p : α → Prop} (ha : p a) (hb : p b) : p (a ⊓ b) :=
@sup_ind (order_dual α) _ _ _ _ _ ha hb

@[simp] lemma lt_inf_iff [is_total α (≤)] {a b c : α} : a < b ⊓ c ↔ a < b ∧ a < c :=
@sup_lt_iff (order_dual α) _ _ _ _ _

@[simp] lemma inf_le_iff [is_total α (≤)] {a b c : α} : b ⊓ c ≤ a ↔ b ≤ a ∨ c ≤ a :=
@le_sup_iff (order_dual α) _ _ _ _ _

@[simp] theorem inf_idem : a ⊓ a = a :=
@sup_idem (order_dual α) _ _

instance inf_is_idempotent : is_idempotent α (⊓) := ⟨@inf_idem _ _⟩

theorem inf_comm : a ⊓ b = b ⊓ a :=
@sup_comm (order_dual α) _ _ _

instance inf_is_commutative : is_commutative α (⊓) := ⟨@inf_comm _ _⟩

theorem inf_assoc : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) :=
@sup_assoc (order_dual α) _ a b c

instance inf_is_associative : is_associative α (⊓) := ⟨@inf_assoc _ _⟩

lemma inf_left_right_swap (a b c : α) : a ⊓ b ⊓ c = c ⊓ b ⊓ a :=
by rw [inf_comm, @inf_comm _ _ a, inf_assoc]

@[simp] lemma inf_left_idem : a ⊓ (a ⊓ b) = a ⊓ b :=
@sup_left_idem (order_dual α) _ a b

@[simp] lemma inf_right_idem : (a ⊓ b) ⊓ b = a ⊓ b :=
@sup_right_idem (order_dual α) _ a b

lemma inf_left_comm (a b c : α) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) :=
@sup_left_comm (order_dual α) _ a b c

lemma inf_right_comm (a b c : α) : a ⊓ b ⊓ c = a ⊓ c ⊓ b :=
@sup_right_comm (order_dual α) _ a b c

lemma inf_inf_inf_comm (a b c d : α) : a ⊓ b ⊓ (c ⊓ d) = a ⊓ c ⊓ (b ⊓ d) :=
@sup_sup_sup_comm (order_dual α) _ _ _ _ _

lemma forall_le_or_exists_lt_inf (a : α) : (∀b, a ≤ b) ∨ (∃b, b < a) :=
@forall_le_or_exists_lt_sup (order_dual α) _ a

theorem semilattice_inf.ext_inf {α} {A B : semilattice_inf α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y)
  (x y : α) : (by haveI := A; exact (x ⊓ y)) = x ⊓ y :=
eq_of_forall_le_iff $ λ c,
by simp only [le_inf_iff]; rw [← H, @le_inf_iff α A, H, H]

theorem semilattice_inf.ext {α} {A B : semilattice_inf α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  have := partial_order.ext H,
  have ss := funext (λ x, funext $ semilattice_inf.ext_inf H x),
  casesI A, casesI B,
  injection this; congr'
end

theorem semilattice_inf.dual_dual (α : Type*) [H : semilattice_inf α] :
  order_dual.semilattice_inf (order_dual α) = H :=
semilattice_inf.ext $ λ _ _, iff.rfl

theorem exists_lt_of_inf (α : Type*) [semilattice_inf α] [nontrivial α] :
  ∃ a b : α, a < b :=
let ⟨a, b, h⟩ := exists_lt_of_sup (order_dual α) in ⟨b, a, h⟩

lemma inf_le_ite (s s' : α) (P : Prop) [decidable P] : s ⊓ s' ≤ ite P s s' :=
if h : P then inf_le_left.trans_eq (if_pos h).symm else inf_le_right.trans_eq (if_neg h).symm

end semilattice_inf

/--
A type with a commutative, associative and idempotent binary `inf` operation has the structure of a
meet-semilattice.

The partial order is defined so that `a ≤ b` unfolds to `b ⊓ a = a`; cf. `inf_eq_right`.
-/
def semilattice_inf.mk' {α : Type*} [has_inf α]
  (inf_comm : ∀ (a b : α), a ⊓ b = b ⊓ a)
  (inf_assoc : ∀ (a b c : α), a ⊓ b ⊓ c = a ⊓ (b ⊓ c))
  (inf_idem : ∀ (a : α), a ⊓ a = a) : semilattice_inf α :=
begin
  haveI : semilattice_sup (order_dual α) := semilattice_sup.mk' inf_comm inf_assoc inf_idem,
  haveI i := order_dual.semilattice_inf (order_dual α),
  exact i,
end

/-!
### Lattices
-/

/-- A lattice is a join-semilattice which is also a meet-semilattice. -/
@[protect_proj] class lattice (α : Type u) extends semilattice_sup α, semilattice_inf α

instance (α) [lattice α] : lattice (order_dual α) :=
{ .. order_dual.semilattice_sup α, .. order_dual.semilattice_inf α }

/-- The partial orders from `semilattice_sup_mk'` and `semilattice_inf_mk'` agree
if `sup` and `inf` satisfy the lattice absorption laws `sup_inf_self` (`a ⊔ a ⊓ b = a`)
and `inf_sup_self` (`a ⊓ (a ⊔ b) = a`). -/
lemma semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order {α : Type*}
  [has_sup α] [has_inf α]
  (sup_comm : ∀ (a b : α), a ⊔ b = b ⊔ a)
  (sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
  (sup_idem : ∀ (a : α), a ⊔ a = a)
  (inf_comm : ∀ (a b : α), a ⊓ b = b ⊓ a)
  (inf_assoc : ∀ (a b c : α), a ⊓ b ⊓ c = a ⊓ (b ⊓ c))
  (inf_idem : ∀ (a : α), a ⊓ a = a)
  (sup_inf_self : ∀ (a b : α), a ⊔ a ⊓ b = a)
  (inf_sup_self : ∀ (a b : α), a ⊓ (a ⊔ b) = a) :
  @semilattice_sup.to_partial_order _ (semilattice_sup.mk' sup_comm sup_assoc sup_idem) =
    @semilattice_inf.to_partial_order _ (semilattice_inf.mk' inf_comm inf_assoc inf_idem) :=
partial_order.ext $ λ a b, show a ⊔ b = b ↔ b ⊓ a = a, from
  ⟨λ h, by rw [←h, inf_comm, inf_sup_self],
   λ h, by rw [←h, sup_comm, sup_inf_self]⟩

/--
A type with a pair of commutative and associative binary operations which satisfy two absorption
laws relating the two operations has the structure of a lattice.

The partial order is defined so that `a ≤ b` unfolds to `a ⊔ b = b`; cf. `sup_eq_right`.
-/
def lattice.mk' {α : Type*} [has_sup α] [has_inf α]
  (sup_comm : ∀ (a b : α), a ⊔ b = b ⊔ a)
  (sup_assoc : ∀ (a b c : α), a ⊔ b ⊔ c = a ⊔ (b ⊔ c))
  (inf_comm : ∀ (a b : α), a ⊓ b = b ⊓ a)
  (inf_assoc : ∀ (a b c : α), a ⊓ b ⊓ c = a ⊓ (b ⊓ c))
  (sup_inf_self : ∀ (a b : α), a ⊔ a ⊓ b = a)
  (inf_sup_self : ∀ (a b : α), a ⊓ (a ⊔ b) = a) : lattice α :=
have sup_idem : ∀ (b : α), b ⊔ b = b := λ b,
  calc b ⊔ b = b ⊔ b ⊓ (b ⊔ b) : by rw inf_sup_self
         ... = b               : by rw sup_inf_self,
have inf_idem : ∀ (b : α), b ⊓ b = b := λ b,
  calc b ⊓ b = b ⊓ (b ⊔ b ⊓ b) : by rw sup_inf_self
         ... = b               : by rw inf_sup_self,
let semilatt_inf_inst := semilattice_inf.mk' inf_comm inf_assoc inf_idem,
    semilatt_sup_inst := semilattice_sup.mk' sup_comm sup_assoc sup_idem,
-- here we help Lean to see that the two partial orders are equal
  partial_order_inst := @semilattice_sup.to_partial_order _ semilatt_sup_inst in
have partial_order_eq :
  partial_order_inst = @semilattice_inf.to_partial_order _ semilatt_inf_inst :=
  semilattice_sup_mk'_partial_order_eq_semilattice_inf_mk'_partial_order _ _ _ _ _ _
    sup_inf_self inf_sup_self,
{ inf_le_left  := λ a b, by { rw partial_order_eq, apply inf_le_left },
  inf_le_right := λ a b, by { rw partial_order_eq, apply inf_le_right },
  le_inf := λ a b c, by { rw partial_order_eq, apply le_inf },
  ..partial_order_inst,
  ..semilatt_sup_inst,
  ..semilatt_inf_inst, }

section lattice
variables [lattice α] {a b c d : α}

lemma inf_le_sup : a ⊓ b ≤ a ⊔ b := inf_le_left.trans le_sup_left

@[simp] lemma inf_lt_sup : a ⊓ b < a ⊔ b ↔ a ≠ b :=
begin
  split,
  { rintro H rfl, simpa using H },
  { refine λ Hne, lt_iff_le_and_ne.2 ⟨inf_le_sup, λ Heq, Hne _⟩,
    refine le_antisymm _ _,
    exacts [le_sup_left.trans (Heq.symm.trans_le inf_le_right),
      le_sup_right.trans (Heq.symm.trans_le inf_le_left)] }
end

/-!
#### Distributivity laws
-/
/- TODO: better names? -/
theorem sup_inf_le : a ⊔ (b ⊓ c) ≤ (a ⊔ b) ⊓ (a ⊔ c) :=
le_inf (sup_le_sup_left inf_le_left _) (sup_le_sup_left inf_le_right _)

theorem le_inf_sup : (a ⊓ b) ⊔ (a ⊓ c) ≤ a ⊓ (b ⊔ c) :=
sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)

theorem inf_sup_self : a ⊓ (a ⊔ b) = a :=
by simp

theorem sup_inf_self : a ⊔ (a ⊓ b) = a :=
by simp

theorem sup_eq_iff_inf_eq : a ⊔ b = b ↔ a ⊓ b = a :=
by rw [sup_eq_right, ←inf_eq_left]

theorem lattice.ext {α} {A B : lattice α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
begin
  have SS : @lattice.to_semilattice_sup α A =
            @lattice.to_semilattice_sup α B := semilattice_sup.ext H,
  have II := semilattice_inf.ext H,
  casesI A, casesI B,
  injection SS; injection II; congr'
end

end lattice

/-!
### Distributive lattices
-/

/-- A distributive lattice is a lattice that satisfies any of four
equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
on the left or right).

The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`.

A classic example of a distributive lattice
is the lattice of subsets of a set, and in fact this example is
generic in the sense that every distributive lattice is realizable
as a sublattice of a powerset lattice. -/
class distrib_lattice α extends lattice α :=
(le_sup_inf : ∀x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z))

/- TODO: alternative constructors from the other distributive properties,
and perhaps a `tfae` statement -/

section distrib_lattice
variables [distrib_lattice α] {x y z : α}

theorem le_sup_inf : ∀{x y z : α}, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z) :=
distrib_lattice.le_sup_inf

theorem sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z) :=
le_antisymm sup_inf_le le_sup_inf

theorem sup_inf_right : (y ⊓ z) ⊔ x = (y ⊔ x) ⊓ (z ⊔ x) :=
by simp only [sup_inf_left, λy:α, @sup_comm α _ y x, eq_self_iff_true]

theorem inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) :=
calc x ⊓ (y ⊔ z) = (x ⊓ (x ⊔ z)) ⊓ (y ⊔ z)       : by rw [inf_sup_self]
             ... = x ⊓ ((x ⊓ y) ⊔ z)             : by simp only [inf_assoc, sup_inf_right,
                                                                 eq_self_iff_true]
             ... = (x ⊔ (x ⊓ y)) ⊓ ((x ⊓ y) ⊔ z) : by rw [sup_inf_self]
             ... = ((x ⊓ y) ⊔ x) ⊓ ((x ⊓ y) ⊔ z) : by rw [sup_comm]
             ... = (x ⊓ y) ⊔ (x ⊓ z)             : by rw [sup_inf_left]

instance (α : Type*) [distrib_lattice α] : distrib_lattice (order_dual α) :=
{ le_sup_inf := assume x y z, le_of_eq inf_sup_left.symm,
  .. order_dual.lattice α }

theorem inf_sup_right : (y ⊔ z) ⊓ x = (y ⊓ x) ⊔ (z ⊓ x) :=
by simp only [inf_sup_left, λy:α, @inf_comm α _ y x, eq_self_iff_true]

lemma le_of_inf_le_sup_le (h₁ : x ⊓ z ≤ y ⊓ z) (h₂ : x ⊔ z ≤ y ⊔ z) : x ≤ y :=
calc x ≤ (y ⊓ z) ⊔ x : le_sup_right
... = (y ⊔ x) ⊓ (x ⊔ z) : by rw [sup_inf_right, @sup_comm _ _ x]
... ≤ (y ⊔ x) ⊓ (y ⊔ z) : inf_le_inf_left _ h₂
... = y ⊔ (x ⊓ z) : sup_inf_left.symm
... ≤ y ⊔ (y ⊓ z) : sup_le_sup_left h₁ _
... ≤ _ : sup_le (le_refl y) inf_le_left

lemma eq_of_inf_eq_sup_eq {α : Type u} [distrib_lattice α] {a b c : α}
  (h₁ : b ⊓ a = c ⊓ a) (h₂ : b ⊔ a = c ⊔ a) : b = c :=
le_antisymm
  (le_of_inf_le_sup_le (le_of_eq h₁) (le_of_eq h₂))
  (le_of_inf_le_sup_le (le_of_eq h₁.symm) (le_of_eq h₂.symm))

end distrib_lattice

/-!
### Lattices derived from linear orders
-/

@[priority 100] -- see Note [lower instance priority]
instance linear_order.to_lattice {α : Type u} [o : linear_order α] :
  lattice α :=
{ sup          := max,
  le_sup_left  := le_max_left,
  le_sup_right := le_max_right,
  sup_le       := assume a b c, max_le,

  inf          := min,
  inf_le_left  := min_le_left,
  inf_le_right := min_le_right,
  le_inf       := assume a b c, le_min,
  ..o }

theorem sup_eq_max [linear_order α] {x y : α} : x ⊔ y = max x y := rfl
theorem inf_eq_min [linear_order α] {x y : α} : x ⊓ y = min x y := rfl

lemma sup_eq_max_default [semilattice_sup α] [decidable_rel ((≤) : α → α → Prop)]
  [is_total α (≤)] : (⊔) = (max_default : α → α → α) :=
begin
  ext x y,
  dunfold max_default,
  split_ifs with h',
  exacts [sup_of_le_left h', sup_of_le_right $ (total_of (≤) x y).resolve_right h']
end

lemma inf_eq_min_default [semilattice_inf α] [decidable_rel ((≤) : α → α → Prop)]
  [is_total α (≤)] : (⊓) = (min_default : α → α → α) :=
@sup_eq_max_default (order_dual α) _ _ _

/-- A lattice with total order is a linear order.

See note [reducible non-instances]. -/
@[reducible] def lattice.to_linear_order (α : Type u) [lattice α] [decidable_eq α]
  [decidable_rel ((≤) : α → α → Prop)] [decidable_rel ((<) : α → α → Prop)]
  [is_total α (≤)] :
  linear_order α :=
{ decidable_le := ‹_›, decidable_eq := ‹_›, decidable_lt := ‹_›,
  le_total := total_of (≤),
  max := (⊔),
  max_def := sup_eq_max_default,
  min := (⊓),
  min_def := inf_eq_min_default,
  ..‹lattice α› }

@[priority 100] -- see Note [lower instance priority]
instance linear_order.to_distrib_lattice {α : Type u} [o : linear_order α] :
  distrib_lattice α :=
{ le_sup_inf := assume a b c,
    match le_total b c with
    | or.inl h := inf_le_of_left_le $ sup_le_sup_left (le_inf (le_refl b) h) _
    | or.inr h := inf_le_of_right_le $ sup_le_sup_left (le_inf h (le_refl c)) _
    end,
  ..linear_order.to_lattice }

instance nat.distrib_lattice : distrib_lattice ℕ :=
by apply_instance

/-! ### Function lattices -/

namespace pi
variables {ι : Type*} {α' : ι → Type*}

instance [Π i, has_sup (α' i)] : has_sup (Π i, α' i) := ⟨λ f g i, f i ⊔ g i⟩

@[simp] lemma sup_apply [Π i, has_sup (α' i)] (f g : Π i, α' i) (i : ι) : (f ⊔ g) i = f i ⊔ g i :=
rfl

lemma sup_def [Π i, has_sup (α' i)] (f g : Π i, α' i) : f ⊔ g = λ i, f i ⊔ g i := rfl

instance [Π i, has_inf (α' i)] : has_inf (Π i, α' i) := ⟨λ f g i, f i ⊓ g i⟩

@[simp] lemma inf_apply [Π i, has_inf (α' i)] (f g : Π i, α' i) (i : ι) : (f ⊓ g) i = f i ⊓ g i :=
rfl

lemma inf_def [Π i, has_inf (α' i)] (f g : Π i, α' i) : f ⊓ g = λ i, f i ⊓ g i := rfl

instance [Π i, semilattice_sup (α' i)] : semilattice_sup (Π i, α' i) :=
by refine_struct { sup := (⊔), .. pi.partial_order }; tactic.pi_instance_derive_field

instance [Π i, semilattice_inf (α' i)] : semilattice_inf (Π i, α' i) :=
by refine_struct { inf := (⊓), .. pi.partial_order }; tactic.pi_instance_derive_field

instance [Π i, lattice (α' i)] : lattice (Π i, α' i) :=
{ .. pi.semilattice_sup, .. pi.semilattice_inf }

instance [Π i, distrib_lattice (α' i)] : distrib_lattice (Π i, α' i) :=
by refine_struct { .. pi.lattice }; tactic.pi_instance_derive_field

end pi

/-!
### Monotone functions and lattices
-/
namespace monotone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected lemma sup [preorder α] [semilattice_sup β] {f g : α → β} (hf : monotone f)
  (hg : monotone g) : monotone (f ⊔ g) :=
λ x y h, sup_le_sup (hf h) (hg h)

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected lemma inf [preorder α] [semilattice_inf β] {f g : α → β} (hf : monotone f)
  (hg : monotone g) : monotone (f ⊓ g) :=
λ x y h, inf_le_inf (hf h) (hg h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected lemma max [preorder α] [linear_order β] {f g : α → β} (hf : monotone f)
  (hg : monotone g) : monotone (λ x, max (f x) (g x)) :=
hf.sup hg

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected lemma min [preorder α] [linear_order β] {f g : α → β} (hf : monotone f)
  (hg : monotone g) : monotone (λ x, min (f x) (g x)) :=
hf.inf hg

lemma le_map_sup [semilattice_sup α] [semilattice_sup β]
  {f : α → β} (h : monotone f) (x y : α) :
  f x ⊔ f y ≤ f (x ⊔ y) :=
sup_le (h le_sup_left) (h le_sup_right)

lemma map_sup [semilattice_sup α] [is_total α (≤)] [semilattice_sup β] {f : α → β}
  (hf : monotone f) (x y : α) :
  f (x ⊔ y) = f x ⊔ f y :=
(is_total.total x y).elim
  (λ h : x ≤ y, by simp only [h, hf h, sup_of_le_right])
  (λ h, by simp only [h, hf h, sup_of_le_left])

lemma map_inf_le [semilattice_inf α] [semilattice_inf β]
  {f : α → β} (h : monotone f) (x y : α) :
  f (x ⊓ y) ≤ f x ⊓ f y :=
le_inf (h inf_le_left) (h inf_le_right)

lemma map_inf [semilattice_inf α] [is_total α (≤)] [semilattice_inf β] {f : α → β}
  (hf : monotone f) (x y : α) :
  f (x ⊓ y) = f x ⊓ f y :=
@monotone.map_sup (order_dual α) _ _ _ _ _ hf.dual x y

end monotone

namespace antitone

/-- Pointwise supremum of two monotone functions is a monotone function. -/
protected lemma sup [preorder α] [semilattice_sup β] {f g : α → β} (hf : antitone f)
  (hg : antitone g) : antitone (f ⊔ g) :=
λ x y h, sup_le_sup (hf h) (hg h)

/-- Pointwise infimum of two monotone functions is a monotone function. -/
protected lemma inf [preorder α] [semilattice_inf β] {f g : α → β} (hf : antitone f)
  (hg : antitone g) : antitone (f ⊓ g) :=
λ x y h, inf_le_inf (hf h) (hg h)

/-- Pointwise maximum of two monotone functions is a monotone function. -/
protected lemma max [preorder α] [linear_order β] {f g : α → β} (hf : antitone f)
  (hg : antitone g) : antitone (λ x, max (f x) (g x)) :=
hf.sup hg

/-- Pointwise minimum of two monotone functions is a monotone function. -/
protected lemma min [preorder α] [linear_order β] {f g : α → β} (hf : antitone f)
  (hg : antitone g) : antitone (λ x, min (f x) (g x)) :=
hf.inf hg

lemma map_sup_le [semilattice_sup α] [semilattice_inf β]
  {f : α → β} (h : antitone f) (x y : α) :
  f (x ⊔ y) ≤ f x ⊓ f y :=
h.dual_right.le_map_sup x y

lemma map_sup [semilattice_sup α] [is_total α (≤)] [semilattice_inf β] {f : α → β}
  (hf : antitone f) (x y : α) :
  f (x ⊔ y) = f x ⊓ f y :=
hf.dual_right.map_sup x y

lemma le_map_inf [semilattice_inf α] [semilattice_sup β]
  {f : α → β} (h : antitone f) (x y : α) :
  f x ⊔ f y ≤ f (x ⊓ y) :=
h.dual_right.map_inf_le x y

lemma map_inf [semilattice_inf α] [is_total α (≤)] [semilattice_sup β] {f : α → β}
  (hf : antitone f) (x y : α) :
  f (x ⊓ y) = f x ⊔ f y :=
hf.dual_right.map_inf x y

end antitone

/-!
### Products of (semi-)lattices
-/

namespace prod
variables (α β)

instance [has_sup α] [has_sup β] : has_sup (α × β) := ⟨λp q, ⟨p.1 ⊔ q.1, p.2 ⊔ q.2⟩⟩
instance [has_inf α] [has_inf β] : has_inf (α × β) := ⟨λp q, ⟨p.1 ⊓ q.1, p.2 ⊓ q.2⟩⟩

instance [semilattice_sup α] [semilattice_sup β] : semilattice_sup (α × β) :=
{ sup_le := assume a b c h₁ h₂, ⟨sup_le h₁.1 h₂.1, sup_le h₁.2 h₂.2⟩,
  le_sup_left  := assume a b, ⟨le_sup_left, le_sup_left⟩,
  le_sup_right := assume a b, ⟨le_sup_right, le_sup_right⟩,
  .. prod.partial_order α β, .. prod.has_sup α β }

instance [semilattice_inf α] [semilattice_inf β] : semilattice_inf (α × β) :=
{ le_inf := assume a b c h₁ h₂, ⟨le_inf h₁.1 h₂.1, le_inf h₁.2 h₂.2⟩,
  inf_le_left  := assume a b, ⟨inf_le_left, inf_le_left⟩,
  inf_le_right := assume a b, ⟨inf_le_right, inf_le_right⟩,
  .. prod.partial_order α β, .. prod.has_inf α β }

instance [lattice α] [lattice β] : lattice (α × β) :=
{ .. prod.semilattice_inf α β, .. prod.semilattice_sup α β }

instance [distrib_lattice α] [distrib_lattice β] : distrib_lattice (α × β) :=
{ le_sup_inf := assume a b c, ⟨le_sup_inf, le_sup_inf⟩,
  .. prod.lattice α β }

end prod

/-!
### Subtypes of (semi-)lattices
-/

namespace subtype

/-- A subtype forms a `⊔`-semilattice if `⊔` preserves the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilattice_sup [semilattice_sup α] {P : α → Prop}
  (Psup : ∀⦃x y⦄, P x → P y → P (x ⊔ y)) : semilattice_sup {x : α // P x} :=
{ sup := λ x y, ⟨x.1 ⊔ y.1, Psup x.2 y.2⟩,
  le_sup_left := λ x y, @le_sup_left _ _ (x : α) y,
  le_sup_right := λ x y, @le_sup_right _ _ (x : α) y,
  sup_le := λ x y z h1 h2, @sup_le α _ _ _ _ h1 h2,
  ..subtype.partial_order P }

/-- A subtype forms a `⊓`-semilattice if `⊓` preserves the property.
See note [reducible non-instances]. -/
@[reducible]
protected def semilattice_inf [semilattice_inf α] {P : α → Prop}
  (Pinf : ∀⦃x y⦄, P x → P y → P (x ⊓ y)) : semilattice_inf {x : α // P x} :=
{ inf := λ x y, ⟨x.1 ⊓ y.1, Pinf x.2 y.2⟩,
  inf_le_left := λ x y, @inf_le_left _ _ (x : α) y,
  inf_le_right := λ x y, @inf_le_right _ _ (x : α) y,
  le_inf := λ x y z h1 h2, @le_inf α _ _ _ _ h1 h2,
  ..subtype.partial_order P }

/-- A subtype forms a lattice if `⊔` and `⊓` preserve the property.
See note [reducible non-instances]. -/
@[reducible]
protected def lattice [lattice α] {P : α → Prop}
  (Psup : ∀⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀⦃x y⦄, P x → P y → P (x ⊓ y)) :
  lattice {x : α // P x} :=
{ ..subtype.semilattice_inf Pinf, ..subtype.semilattice_sup Psup }

end subtype

section lift

/-- A type endowed with `⊔` is a `semilattice_sup`, if it admits an injective map that
preserves `⊔` to a `semilattice_sup`.
See note [reducible non-instances]. -/
@[reducible] protected def function.injective.semilattice_sup [has_sup α] [semilattice_sup β]
  (f : α → β) (hf_inj : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) :
  semilattice_sup α :=
{ sup := has_sup.sup,
  le_sup_left := λ a b, by { change f a ≤ f (a ⊔ b), rw map_sup, exact le_sup_left, },
  le_sup_right := λ a b, by { change f b ≤ f (a ⊔ b), rw map_sup, exact le_sup_right, },
  sup_le := λ a b c ha hb, by { change f (a ⊔ b) ≤ f c, rw map_sup, exact sup_le ha hb, },
  ..partial_order.lift f hf_inj}

/-- A type endowed with `⊓` is a `semilattice_inf`, if it admits an injective map that
preserves `⊓` to a `semilattice_inf`.
See note [reducible non-instances]. -/
@[reducible] protected def function.injective.semilattice_inf [has_inf α] [semilattice_inf β]
  (f : α → β) (hf_inj : function.injective f) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
  semilattice_inf α :=
{ inf := has_inf.inf,
  inf_le_left := λ a b,  by { change f (a ⊓ b) ≤ f a, rw map_inf, exact inf_le_left, },
  inf_le_right := λ a b, by { change f (a ⊓ b) ≤ f b, rw map_inf, exact inf_le_right, },
  le_inf := λ a b c ha hb, by { change f a ≤ f (b ⊓ c), rw map_inf, exact le_inf ha hb, },
  ..partial_order.lift f hf_inj}

/-- A type endowed with `⊔` and `⊓` is a `lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `lattice`.
See note [reducible non-instances]. -/
@[reducible] protected def function.injective.lattice [has_sup α] [has_inf α] [lattice β]
  (f : α → β) (hf_inj : function.injective f) (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b)
  (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
  lattice α :=
{ ..hf_inj.semilattice_sup f map_sup, ..hf_inj.semilattice_inf f map_inf}

/-- A type endowed with `⊔` and `⊓` is a `distrib_lattice`, if it admits an injective map that
preserves `⊔` and `⊓` to a `distrib_lattice`.
See note [reducible non-instances]. -/
@[reducible] protected def function.injective.distrib_lattice [has_sup α] [has_inf α]
  [distrib_lattice β] (f : α → β) (hf_inj : function.injective f)
  (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
  distrib_lattice α :=
{ le_sup_inf := λ a b c, by { change f ((a ⊔ b) ⊓ (a ⊔ c)) ≤ f (a ⊔ b ⊓ c),
    rw [map_inf, map_sup, map_sup, map_sup, map_inf], exact le_sup_inf, },
  ..hf_inj.lattice f map_sup map_inf, }

end lift

--To avoid noncomputability poisoning from `bool.complete_boolean_algebra`
instance : distrib_lattice bool := linear_order.to_distrib_lattice
