/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import tactic.doc_commands
import tactic.reserved_notation

/-!
# Basic logic properties

This file is one of the earliest imports in mathlib.

## Implementation notes

Theorems that require decidability hypotheses are in the namespace "decidable".
Classical versions are in the namespace "classical".

In the presence of automation, this whole file may be unnecessary. On the other hand,
maybe it is useful for writing automation.
-/

open function
local attribute [instance, priority 10] classical.prop_decidable

section miscellany

/- We add the `inline` attribute to optimize VM computation using these declarations. For example,
  `if p ∧ q then ... else ...` will not evaluate the decidability of `q` if `p` is false. -/
attribute [inline] and.decidable or.decidable decidable.false xor.decidable iff.decidable
  decidable.true implies.decidable not.decidable ne.decidable
  bool.decidable_eq decidable.to_bool

attribute [simp] cast_eq cast_heq

variables {α : Type*} {β : Type*}

/-- An identity function with its main argument implicit. This will be printed as `hidden` even
if it is applied to a large term, so it can be used for elision,
as done in the `elide` and `unelide` tactics. -/
@[reducible] def hidden {α : Sort*} {a : α} := a

/-- Ex falso, the nondependent eliminator for the `empty` type. -/
def empty.elim {C : Sort*} : empty → C.

instance : subsingleton empty := ⟨λa, a.elim⟩

instance subsingleton.prod {α β : Type*} [subsingleton α] [subsingleton β] : subsingleton (α × β) :=
⟨by { intros a b, cases a, cases b, congr, }⟩

instance : decidable_eq empty := λa, a.elim

instance sort.inhabited : inhabited (Sort*) := ⟨punit⟩
instance sort.inhabited' : inhabited (default) := ⟨punit.star⟩

instance psum.inhabited_left {α β} [inhabited α] : inhabited (psum α β) := ⟨psum.inl default⟩
instance psum.inhabited_right {α β} [inhabited β] : inhabited (psum α β) := ⟨psum.inr default⟩

@[priority 10] instance decidable_eq_of_subsingleton
  {α} [subsingleton α] : decidable_eq α
| a b := is_true (subsingleton.elim a b)

@[simp] lemma eq_iff_true_of_subsingleton {α : Sort*} [subsingleton α] (x y : α) :
  x = y ↔ true :=
by cc

/-- If all points are equal to a given point `x`, then `α` is a subsingleton. -/
lemma subsingleton_of_forall_eq {α : Sort*} (x : α) (h : ∀ y, y = x) : subsingleton α :=
⟨λ a b, (h a).symm ▸ (h b).symm ▸ rfl⟩

lemma subsingleton_iff_forall_eq {α : Sort*} (x : α) : subsingleton α ↔ ∀ y, y = x :=
⟨λ h y, @subsingleton.elim _ h y x, subsingleton_of_forall_eq x⟩

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subtype.subsingleton (α : Sort*) [subsingleton α] (p : α → Prop) : subsingleton (subtype p) :=
⟨λ ⟨x,_⟩ ⟨y,_⟩, have x = y, from subsingleton.elim _ _, by { cases this, refl }⟩

/-- Add an instance to "undo" coercion transitivity into a chain of coercions, because
   most simp lemmas are stated with respect to simple coercions and will not match when
   part of a chain. -/
@[simp] theorem coe_coe {α β γ} [has_coe α β] [has_coe_t β γ]
  (a : α) : (a : γ) = (a : β) := rfl

theorem coe_fn_coe_trans
  {α β γ δ} [has_coe α β] [has_coe_t_aux β γ] [has_coe_to_fun γ δ]
  (x : α) : @coe_fn α _ _ x = @coe_fn β _ _ x := rfl

/-- Non-dependent version of `coe_fn_coe_trans`, helps `rw` figure out the argument. -/
theorem coe_fn_coe_trans'
  {α β γ} {δ : out_param $ _} [has_coe α β] [has_coe_t_aux β γ] [has_coe_to_fun γ (λ _, δ)]
  (x : α) : @coe_fn α _ _ x = @coe_fn β _ _ x := rfl

@[simp] theorem coe_fn_coe_base
  {α β γ} [has_coe α β] [has_coe_to_fun β γ]
  (x : α) : @coe_fn α _ _ x = @coe_fn β _ _ x := rfl

/-- Non-dependent version of `coe_fn_coe_base`, helps `rw` figure out the argument. -/
theorem coe_fn_coe_base'
  {α β} {γ : out_param $ _} [has_coe α β] [has_coe_to_fun β (λ _, γ)]
  (x : α) : @coe_fn α _ _ x = @coe_fn β _ _ x := rfl

theorem coe_sort_coe_trans
  {α β γ δ} [has_coe α β] [has_coe_t_aux β γ] [has_coe_to_sort γ δ]
  (x : α) : @coe_sort α _ _ x = @coe_sort β _ _ x := rfl

/--
Many structures such as bundled morphisms coerce to functions so that you can
transparently apply them to arguments. For example, if `e : α ≃ β` and `a : α`
then you can write `e a` and this is elaborated as `⇑e a`. This type of
coercion is implemented using the `has_coe_to_fun` type class. There is one
important consideration:

If a type coerces to another type which in turn coerces to a function,
then it **must** implement `has_coe_to_fun` directly:
```lean
structure sparkling_equiv (α β) extends α ≃ β

-- if we add a `has_coe` instance,
instance {α β} : has_coe (sparkling_equiv α β) (α ≃ β) :=
⟨sparkling_equiv.to_equiv⟩

-- then a `has_coe_to_fun` instance **must** be added as well:
instance {α β} : has_coe_to_fun (sparkling_equiv α β) :=
⟨λ _, α → β, λ f, f.to_equiv.to_fun⟩
```

(Rationale: if we do not declare the direct coercion, then `⇑e a` is not in
simp-normal form. The lemma `coe_fn_coe_base` will unfold it to `⇑↑e a`. This
often causes loops in the simplifier.)
-/
library_note "function coercion"

@[simp] theorem coe_sort_coe_base
  {α β γ} [has_coe α β] [has_coe_to_sort β γ]
  (x : α) : @coe_sort α _ _ x = @coe_sort β _ _ x := rfl

/-- `pempty` is the universe-polymorphic analogue of `empty`. -/
@[derive decidable_eq]
inductive {u} pempty : Sort u

/-- Ex falso, the nondependent eliminator for the `pempty` type. -/
def pempty.elim {C : Sort*} : pempty → C.

instance subsingleton_pempty : subsingleton pempty := ⟨λa, a.elim⟩

@[simp] lemma not_nonempty_pempty : ¬ nonempty pempty :=
assume ⟨h⟩, h.elim

@[simp] theorem forall_pempty {P : pempty → Prop} : (∀ x : pempty, P x) ↔ true :=
⟨λ h, trivial, λ h x, by cases x⟩

@[simp] theorem exists_pempty {P : pempty → Prop} : (∃ x : pempty, P x) ↔ false :=
⟨λ h, by { cases h with w, cases w }, false.elim⟩

lemma congr_arg_heq {α} {β : α → Sort*} (f : ∀ a, β a) : ∀ {a₁ a₂ : α}, a₁ = a₂ → f a₁ == f a₂
| a _ rfl := heq.rfl

lemma plift.down_inj {α : Sort*} : ∀ (a b : plift α), a.down = b.down → a = b
| ⟨a⟩ ⟨b⟩ rfl := rfl

-- missing [symm] attribute for ne in core.
attribute [symm] ne.symm

lemma ne_comm {α} {a b : α} : a ≠ b ↔ b ≠ a := ⟨ne.symm, ne.symm⟩

@[simp] lemma eq_iff_eq_cancel_left {b c : α} :
  (∀ {a}, a = b ↔ a = c) ↔ (b = c) :=
⟨λ h, by rw [← h], λ h a, by rw h⟩

@[simp] lemma eq_iff_eq_cancel_right {a b : α} :
  (∀ {c}, a = c ↔ b = c) ↔ (a = b) :=
⟨λ h, by rw h, λ h a, by rw h⟩

/-- Wrapper for adding elementary propositions to the type class systems.
Warning: this can easily be abused. See the rest of this docstring for details.

Certain propositions should not be treated as a class globally,
but sometimes it is very convenient to be able to use the type class system
in specific circumstances.

For example, `zmod p` is a field if and only if `p` is a prime number.
In order to be able to find this field instance automatically by type class search,
we have to turn `p.prime` into an instance implicit assumption.

On the other hand, making `nat.prime` a class would require a major refactoring of the library,
and it is questionable whether making `nat.prime` a class is desirable at all.
The compromise is to add the assumption `[fact p.prime]` to `zmod.field`.

In particular, this class is not intended for turning the type class system
into an automated theorem prover for first order logic. -/
class fact (p : Prop) : Prop := (out [] : p)

/--
In most cases, we should not have global instances of `fact`; typeclass search only reads the head
symbol and then tries any instances, which means that adding any such instance will cause slowdowns
everywhere. We instead make them as lemmata and make them local instances as required.
-/
library_note "fact non-instances"

lemma fact.elim {p : Prop} (h : fact p) : p := h.1
lemma fact_iff {p : Prop} : fact p ↔ p := ⟨λ h, h.1, λ h, ⟨h⟩⟩

end miscellany

/-!
### Declarations about propositional connectives
-/

theorem false_ne_true : false ≠ true
| h := h.symm ▸ trivial

section propositional
variables {a b c d e f : Prop}

/-! ### Declarations about `implies` -/

instance : is_refl Prop iff := ⟨iff.refl⟩
instance : is_trans Prop iff := ⟨λ _ _ _, iff.trans⟩

theorem iff_of_eq (e : a = b) : a ↔ b := e ▸ iff.rfl

theorem iff_iff_eq : (a ↔ b) ↔ a = b := ⟨propext, iff_of_eq⟩

@[simp] lemma eq_iff_iff {p q : Prop} : (p = q) ↔ (p ↔ q) := iff_iff_eq.symm

@[simp] theorem imp_self : (a → a) ↔ true := iff_true_intro id

lemma iff.imp (h₁ : a ↔ b) (h₂ : c ↔ d) : (a → c) ↔ (b → d) := imp_congr h₁ h₂

@[simp] lemma eq_true_eq_id : eq true = id :=
by { funext, simp only [true_iff, id.def, iff_self, eq_iff_iff], }

theorem imp_intro {α β : Prop} (h : α) : β → α := λ _, h

theorem imp_false : (a → false) ↔ ¬ a := iff.rfl

theorem imp_and_distrib {α} : (α → b ∧ c) ↔ (α → b) ∧ (α → c) :=
⟨λ h, ⟨λ ha, (h ha).left, λ ha, (h ha).right⟩,
 λ h ha, ⟨h.left ha, h.right ha⟩⟩

@[simp] theorem and_imp : (a ∧ b → c) ↔ (a → b → c) :=
iff.intro (λ h ha hb, h ⟨ha, hb⟩) (λ h ⟨ha, hb⟩, h ha hb)

theorem iff_def : (a ↔ b) ↔ (a → b) ∧ (b → a) :=
iff_iff_implies_and_implies _ _

theorem iff_def' : (a ↔ b) ↔ (b → a) ∧ (a → b) :=
iff_def.trans and.comm

theorem imp_true_iff {α : Sort*} : (α → true) ↔ true :=
iff_true_intro $ λ_, trivial

theorem imp_iff_right (ha : a) : (a → b) ↔ b :=
⟨λf, f ha, imp_intro⟩

lemma imp_iff_not (hb : ¬ b) : a → b ↔ ¬ a := imp_congr_right $ λ _, iff_false_intro hb

theorem decidable.imp_iff_right_iff [decidable a] : ((a → b) ↔ b) ↔ (a ∨ b) :=
⟨λ H, (decidable.em a).imp_right $ λ ha', H.1 $ λ ha, (ha' ha).elim,
  λ H, H.elim imp_iff_right $ λ hb, ⟨λ hab, hb, λ _ _, hb⟩⟩

@[simp] theorem imp_iff_right_iff : ((a → b) ↔ b) ↔ (a ∨ b) :=
decidable.imp_iff_right_iff

lemma decidable.and_or_imp [decidable a] : (a ∧ b) ∨ (a → c) ↔ a → (b ∨ c) :=
if ha : a then by simp only [ha, true_and, true_implies_iff]
          else by simp only [ha, false_or, false_and, false_implies_iff]

@[simp] theorem and_or_imp : (a ∧ b) ∨ (a → c) ↔ a → (b ∨ c) :=
decidable.and_or_imp

/-! ### Declarations about `not` -/

/-- Ex falso for negation. From `¬ a` and `a` anything follows. This is the same as `absurd` with
the arguments flipped, but it is in the `not` namespace so that projection notation can be used. -/
def not.elim {α : Sort*} (H1 : ¬a) (H2 : a) : α := absurd H2 H1

@[reducible] theorem not.imp {a b : Prop} (H2 : ¬b) (H1 : a → b) : ¬a := mt H1 H2

lemma iff.not (h : a ↔ b) : ¬ a ↔ ¬ b := not_congr h

theorem not_not_of_not_imp : ¬(a → b) → ¬¬a :=
mt not.elim

theorem not_of_not_imp {a : Prop} : ¬(a → b) → ¬b :=
mt imp_intro

theorem dec_em (p : Prop) [decidable p] : p ∨ ¬p := decidable.em p

theorem dec_em' (p : Prop) [decidable p] : ¬p ∨ p := (dec_em p).swap

theorem em (p : Prop) : p ∨ ¬p := classical.em _

theorem em' (p : Prop) : ¬p ∨ p := (em p).swap

theorem or_not {p : Prop} : p ∨ ¬p := em _

section eq_or_ne

variables {α : Sort*} (x y : α)

theorem decidable.eq_or_ne [decidable (x = y)] : x = y ∨ x ≠ y := dec_em $ x = y

theorem decidable.ne_or_eq [decidable (x = y)] : x ≠ y ∨ x = y := dec_em' $ x = y

theorem eq_or_ne : x = y ∨ x ≠ y := em $ x = y

theorem ne_or_eq : x ≠ y ∨ x = y := em' $ x = y

end eq_or_ne

theorem by_contradiction {p} : (¬p → false) → p := decidable.by_contradiction

-- alias by_contradiction ← by_contra
theorem by_contra {p} : (¬p → false) → p := decidable.by_contradiction

/--
In most of mathlib, we use the law of excluded middle (LEM) and the axiom of choice (AC) freely.
The `decidable` namespace contains versions of lemmas from the root namespace that explicitly
attempt to avoid the axiom of choice, usually by adding decidability assumptions on the inputs.

You can check if a lemma uses the axiom of choice by using `#print axioms foo` and seeing if
`classical.choice` appears in the list.
-/
library_note "decidable namespace"

/--
As mathlib is primarily classical,
if the type signature of a `def` or `lemma` does not require any `decidable` instances to state,
it is preferable not to introduce any `decidable` instances that are needed in the proof
as arguments, but rather to use the `classical` tactic as needed.

In the other direction, when `decidable` instances do appear in the type signature,
it is better to use explicitly introduced ones rather than allowing Lean to automatically infer
classical ones, as these may cause instance mismatch errors later.
-/
library_note "decidable arguments"

-- See Note [decidable namespace]
protected theorem decidable.not_not [decidable a] : ¬¬a ↔ a :=
iff.intro decidable.by_contradiction not_not_intro

/-- The Double Negation Theorem: `¬ ¬ P` is equivalent to `P`.
The left-to-right direction, double negation elimination (DNE),
is classically true but not constructively. -/
@[simp] theorem not_not : ¬¬a ↔ a := decidable.not_not

theorem of_not_not : ¬¬a → a := by_contra

lemma not_ne_iff {α : Sort*} {a b : α} : ¬ a ≠ b ↔ a = b := not_not

-- See Note [decidable namespace]
protected theorem decidable.of_not_imp [decidable a] (h : ¬ (a → b)) : a :=
decidable.by_contradiction (not_not_of_not_imp h)

theorem of_not_imp : ¬ (a → b) → a := decidable.of_not_imp

-- See Note [decidable namespace]
protected theorem decidable.not_imp_symm [decidable a] (h : ¬a → b) (hb : ¬b) : a :=
decidable.by_contradiction $ hb ∘ h

theorem not.decidable_imp_symm [decidable a] : (¬a → b) → ¬b → a := decidable.not_imp_symm

theorem not.imp_symm : (¬a → b) → ¬b → a := not.decidable_imp_symm

-- See Note [decidable namespace]
protected theorem decidable.not_imp_comm [decidable a] [decidable b] : (¬a → b) ↔ (¬b → a) :=
⟨not.decidable_imp_symm, not.decidable_imp_symm⟩

theorem not_imp_comm : (¬a → b) ↔ (¬b → a) := decidable.not_imp_comm

@[simp] theorem imp_not_self : (a → ¬a) ↔ ¬a := ⟨λ h ha, h ha ha, λ h _, h⟩

theorem decidable.not_imp_self [decidable a] : (¬a → a) ↔ a :=
by { have := @imp_not_self (¬a), rwa decidable.not_not at this }

@[simp] theorem not_imp_self : (¬a → a) ↔ a := decidable.not_imp_self

theorem imp.swap : (a → b → c) ↔ (b → a → c) :=
⟨swap, swap⟩

theorem imp_not_comm : (a → ¬b) ↔ (b → ¬a) :=
imp.swap

/-! ### Declarations about `xor` -/

@[simp] theorem xor_true : xor true = not := funext $ λ a, by simp [xor]

@[simp] theorem xor_false : xor false = id := funext $ λ a, by simp [xor]

theorem xor_comm (a b) : xor a b = xor b a := by simp [xor, and_comm, or_comm]

instance : is_commutative Prop xor := ⟨xor_comm⟩

@[simp] theorem xor_self (a : Prop) : xor a a = false := by simp [xor]

/-! ### Declarations about `and` -/

lemma iff.and (h₁ : a ↔ b) (h₂ : c ↔ d) : a ∧ c ↔ b ∧ d := and_congr h₁ h₂

theorem and_congr_left (h : c → (a ↔ b)) : a ∧ c ↔ b ∧ c :=
and.comm.trans $ (and_congr_right h).trans and.comm

theorem and_congr_left' (h : a ↔ b) : a ∧ c ↔ b ∧ c := h.and iff.rfl

theorem and_congr_right' (h : b ↔ c) : a ∧ b ↔ a ∧ c := iff.rfl.and h

theorem not_and_of_not_left (b : Prop) : ¬a → ¬(a ∧ b) :=
mt and.left

theorem not_and_of_not_right (a : Prop) {b : Prop} : ¬b → ¬(a ∧ b) :=
mt and.right

theorem and.imp_left (h : a → b) : a ∧ c → b ∧ c :=
and.imp h id

theorem and.imp_right (h : a → b) : c ∧ a → c ∧ b :=
and.imp id h

lemma and.right_comm : (a ∧ b) ∧ c ↔ (a ∧ c) ∧ b :=
by simp only [and.left_comm, and.comm]

lemma and_and_and_comm (a b c d : Prop) : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d :=
by rw [←and_assoc, @and.right_comm a, and_assoc]

lemma and.rotate : a ∧ b ∧ c ↔ b ∧ c ∧ a :=
by simp only [and.left_comm, and.comm]

theorem and_not_self_iff (a : Prop) : a ∧ ¬ a ↔ false :=
iff.intro (assume h, (h.right) (h.left)) (assume h, h.elim)

theorem not_and_self_iff (a : Prop) : ¬ a ∧ a ↔ false :=
iff.intro (assume ⟨hna, ha⟩, hna ha) false.elim

theorem and_iff_left_of_imp {a b : Prop} (h : a → b) : (a ∧ b) ↔ a :=
iff.intro and.left (λ ha, ⟨ha, h ha⟩)

theorem and_iff_right_of_imp {a b : Prop} (h : b → a) : (a ∧ b) ↔ b :=
iff.intro and.right (λ hb, ⟨h hb, hb⟩)

@[simp] theorem and_iff_left_iff_imp {a b : Prop} : ((a ∧ b) ↔ a) ↔ (a → b) :=
⟨λ h ha, (h.2 ha).2, and_iff_left_of_imp⟩

@[simp] theorem and_iff_right_iff_imp {a b : Prop} : ((a ∧ b) ↔ b) ↔ (b → a) :=
⟨λ h ha, (h.2 ha).1, and_iff_right_of_imp⟩

@[simp] lemma iff_self_and {p q : Prop} : (p ↔ p ∧ q) ↔ (p → q) :=
by rw [@iff.comm p, and_iff_left_iff_imp]

@[simp] lemma iff_and_self {p q : Prop} : (p ↔ q ∧ p) ↔ (p → q) :=
by rw [and_comm, iff_self_and]

@[simp] lemma and.congr_right_iff : (a ∧ b ↔ a ∧ c) ↔ (a → (b ↔ c)) :=
⟨λ h ha, by simp [ha] at h; exact h, and_congr_right⟩

@[simp] lemma and.congr_left_iff : (a ∧ c ↔ b ∧ c) ↔ c → (a ↔ b) :=
by simp only [and.comm, ← and.congr_right_iff]

@[simp] lemma and_self_left : a ∧ a ∧ b ↔ a ∧ b :=
⟨λ h, ⟨h.1, h.2.2⟩, λ h, ⟨h.1, h.1, h.2⟩⟩

@[simp] lemma and_self_right : (a ∧ b) ∧ b ↔ a ∧ b :=
⟨λ h, ⟨h.1.1, h.2⟩, λ h, ⟨⟨h.1, h.2⟩, h.2⟩⟩

/-! ### Declarations about `or` -/

lemma iff.or (h₁ : a ↔ b) (h₂ : c ↔ d) : a ∨ c ↔ b ∨ d := or_congr h₁ h₂

theorem or_congr_left (h : a ↔ b) : a ∨ c ↔ b ∨ c := h.or iff.rfl

theorem or_congr_right (h : b ↔ c) : a ∨ b ↔ a ∨ c := iff.rfl.or h

theorem or.right_comm : (a ∨ b) ∨ c ↔ (a ∨ c) ∨ b := by rw [or_assoc, or_assoc, or_comm b]

theorem or_of_or_of_imp_of_imp (h₁ : a ∨ b) (h₂ : a → c) (h₃ : b → d) : c ∨ d :=
or.imp h₂ h₃ h₁

theorem or_of_or_of_imp_left (h₁ : a ∨ c) (h : a → b) : b ∨ c :=
or.imp_left h h₁

theorem or_of_or_of_imp_right (h₁ : c ∨ a) (h : a → b) : c ∨ b :=
or.imp_right h h₁

theorem or.elim3 (h : a ∨ b ∨ c) (ha : a → d) (hb : b → d) (hc : c → d) : d :=
or.elim h ha (assume h₂, or.elim h₂ hb hc)

lemma or.imp3 (had : a → d) (hbe : b → e) (hcf : c → f) : a ∨ b ∨ c → d ∨ e ∨ f :=
or.imp had $ or.imp hbe hcf

theorem or_imp_distrib : (a ∨ b → c) ↔ (a → c) ∧ (b → c) :=
⟨assume h, ⟨assume ha, h (or.inl ha), assume hb, h (or.inr hb)⟩,
  assume ⟨ha, hb⟩, or.rec ha hb⟩

-- See Note [decidable namespace]
protected theorem decidable.or_iff_not_imp_left [decidable a] : a ∨ b ↔ (¬ a → b) :=
⟨or.resolve_left, λ h, dite _ or.inl (or.inr ∘ h)⟩

theorem or_iff_not_imp_left : a ∨ b ↔ (¬ a → b) := decidable.or_iff_not_imp_left

-- See Note [decidable namespace]
protected theorem decidable.or_iff_not_imp_right [decidable b] : a ∨ b ↔ (¬ b → a) :=
or.comm.trans decidable.or_iff_not_imp_left

theorem or_iff_not_imp_right : a ∨ b ↔ (¬ b → a) := decidable.or_iff_not_imp_right

-- See Note [decidable namespace]
protected theorem decidable.not_imp_not [decidable a] : (¬ a → ¬ b) ↔ (b → a) :=
⟨assume h hb, decidable.by_contradiction $ assume na, h na hb, mt⟩

theorem not_imp_not : (¬ a → ¬ b) ↔ (b → a) := decidable.not_imp_not

@[simp] theorem or_iff_left_iff_imp : (a ∨ b ↔ a) ↔ (b → a) :=
⟨λ h hb, h.1 (or.inr hb), or_iff_left_of_imp⟩

@[simp] theorem or_iff_right_iff_imp : (a ∨ b ↔ b) ↔ (a → b) :=
by rw [or_comm, or_iff_left_iff_imp]

lemma or_iff_left (hb : ¬ b) : a ∨ b ↔ a := ⟨λ h, h.resolve_right hb, or.inl⟩
lemma or_iff_right (ha : ¬ a) : a ∨ b ↔ b := ⟨λ h, h.resolve_left ha, or.inr⟩

/-! ### Declarations about distributivity -/

/-- `∧` distributes over `∨` (on the left). -/
theorem and_or_distrib_left : a ∧ (b ∨ c) ↔ (a ∧ b) ∨ (a ∧ c) :=
⟨λ ⟨ha, hbc⟩, hbc.imp (and.intro ha) (and.intro ha),
 or.rec (and.imp_right or.inl) (and.imp_right or.inr)⟩

/-- `∧` distributes over `∨` (on the right). -/
theorem or_and_distrib_right : (a ∨ b) ∧ c ↔ (a ∧ c) ∨ (b ∧ c) :=
(and.comm.trans and_or_distrib_left).trans (and.comm.or and.comm)

/-- `∨` distributes over `∧` (on the left). -/
theorem or_and_distrib_left : a ∨ (b ∧ c) ↔ (a ∨ b) ∧ (a ∨ c) :=
⟨or.rec (λha, and.intro (or.inl ha) (or.inl ha)) (and.imp or.inr or.inr),
 and.rec $ or.rec (imp_intro ∘ or.inl) (or.imp_right ∘ and.intro)⟩

/-- `∨` distributes over `∧` (on the right). -/
theorem and_or_distrib_right : (a ∧ b) ∨ c ↔ (a ∨ c) ∧ (b ∨ c) :=
(or.comm.trans or_and_distrib_left).trans (or.comm.and or.comm)

@[simp] lemma or_self_left : a ∨ a ∨ b ↔ a ∨ b :=
⟨λ h, h.elim or.inl id, λ h, h.elim or.inl (or.inr ∘ or.inr)⟩

@[simp] lemma or_self_right : (a ∨ b) ∨ b ↔ a ∨ b :=
⟨λ h, h.elim id or.inr, λ h, h.elim (or.inl ∘ or.inl) or.inr⟩

/-! Declarations about `iff` -/

lemma iff.iff (h₁ : a ↔ b) (h₂ : c ↔ d) : (a ↔ c) ↔ (b ↔ d) := iff_congr h₁ h₂

theorem iff_of_true (ha : a) (hb : b) : a ↔ b :=
⟨λ_, hb, λ _, ha⟩

theorem iff_of_false (ha : ¬a) (hb : ¬b) : a ↔ b :=
⟨ha.elim, hb.elim⟩

theorem iff_true_left (ha : a) : (a ↔ b) ↔ b :=
⟨λ h, h.1 ha, iff_of_true ha⟩

theorem iff_true_right (ha : a) : (b ↔ a) ↔ b :=
iff.comm.trans (iff_true_left ha)

theorem iff_false_left (ha : ¬a) : (a ↔ b) ↔ ¬b :=
⟨λ h, mt h.2 ha, iff_of_false ha⟩

theorem iff_false_right (ha : ¬a) : (b ↔ a) ↔ ¬b :=
iff.comm.trans (iff_false_left ha)

@[simp]
lemma iff_mpr_iff_true_intro {P : Prop} (h : P) : iff.mpr (iff_true_intro h) true.intro = h := rfl

-- See Note [decidable namespace]
protected theorem decidable.not_or_of_imp [decidable a] (h : a → b) : ¬ a ∨ b :=
if ha : a then or.inr (h ha) else or.inl ha

theorem not_or_of_imp : (a → b) → ¬ a ∨ b := decidable.not_or_of_imp

-- See Note [decidable namespace]
protected theorem decidable.imp_iff_not_or [decidable a] : (a → b) ↔ (¬ a ∨ b) :=
⟨decidable.not_or_of_imp, or.neg_resolve_left⟩

theorem imp_iff_not_or : (a → b) ↔ (¬ a ∨ b) := decidable.imp_iff_not_or

-- See Note [decidable namespace]
protected theorem decidable.imp_or_distrib [decidable a] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
by simp [decidable.imp_iff_not_or, or.comm, or.left_comm]

theorem imp_or_distrib : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := decidable.imp_or_distrib

-- See Note [decidable namespace]
protected theorem decidable.imp_or_distrib' [decidable b] : (a → b ∨ c) ↔ (a → b) ∨ (a → c) :=
by by_cases b; simp [h, or_iff_right_of_imp ((∘) false.elim)]

theorem imp_or_distrib' : (a → b ∨ c) ↔ (a → b) ∨ (a → c) := decidable.imp_or_distrib'

theorem not_imp_of_and_not : a ∧ ¬ b → ¬ (a → b)
| ⟨ha, hb⟩ h := hb $ h ha

-- See Note [decidable namespace]
protected theorem decidable.not_imp [decidable a] : ¬(a → b) ↔ a ∧ ¬b :=
⟨λ h, ⟨decidable.of_not_imp h, not_of_not_imp h⟩, not_imp_of_and_not⟩

theorem not_imp : ¬(a → b) ↔ a ∧ ¬b := decidable.not_imp

-- for monotonicity
lemma imp_imp_imp (h₀ : c → a) (h₁ : b → d) : (a → b) → (c → d) :=
assume (h₂ : a → b), h₁ ∘ h₂ ∘ h₀

-- See Note [decidable namespace]
protected theorem decidable.peirce (a b : Prop) [decidable a] : ((a → b) → a) → a :=
if ha : a then λ h, ha else λ h, h ha.elim

theorem peirce (a b : Prop) : ((a → b) → a) → a := decidable.peirce _ _

theorem peirce' {a : Prop} (H : ∀ b : Prop, (a → b) → a) : a := H _ id

-- See Note [decidable namespace]
protected theorem decidable.not_iff_not [decidable a] [decidable b] : (¬ a ↔ ¬ b) ↔ (a ↔ b) :=
by rw [@iff_def (¬ a), @iff_def' a]; exact decidable.not_imp_not.and decidable.not_imp_not

theorem not_iff_not : (¬ a ↔ ¬ b) ↔ (a ↔ b) := decidable.not_iff_not

-- See Note [decidable namespace]
protected theorem decidable.not_iff_comm [decidable a] [decidable b] : (¬ a ↔ b) ↔ (¬ b ↔ a) :=
by rw [@iff_def (¬ a), @iff_def (¬ b)]; exact decidable.not_imp_comm.and imp_not_comm

theorem not_iff_comm : (¬ a ↔ b) ↔ (¬ b ↔ a) := decidable.not_iff_comm

-- See Note [decidable namespace]
protected theorem decidable.not_iff : ∀ [decidable b], ¬ (a ↔ b) ↔ (¬ a ↔ b) :=
by intro h; cases h; simp only [h, iff_true, iff_false]

theorem not_iff : ¬ (a ↔ b) ↔ (¬ a ↔ b) := decidable.not_iff

-- See Note [decidable namespace]
protected theorem decidable.iff_not_comm [decidable a] [decidable b] : (a ↔ ¬ b) ↔ (b ↔ ¬ a) :=
by rw [@iff_def a, @iff_def b]; exact imp_not_comm.and decidable.not_imp_comm

theorem iff_not_comm : (a ↔ ¬ b) ↔ (b ↔ ¬ a) := decidable.iff_not_comm

-- See Note [decidable namespace]
protected theorem decidable.iff_iff_and_or_not_and_not [decidable b] :
  (a ↔ b) ↔ (a ∧ b) ∨ (¬ a ∧ ¬ b) :=
by { split; intro h,
     { rw h; by_cases b; [left,right]; split; assumption },
     { cases h with h h; cases h; split; intro; { contradiction <|> assumption } } }

theorem iff_iff_and_or_not_and_not : (a ↔ b) ↔ (a ∧ b) ∨ (¬ a ∧ ¬ b) :=
decidable.iff_iff_and_or_not_and_not

lemma decidable.iff_iff_not_or_and_or_not [decidable a] [decidable b] :
  (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) :=
begin
  rw [iff_iff_implies_and_implies a b],
  simp only [decidable.imp_iff_not_or, or.comm]
end

lemma iff_iff_not_or_and_or_not : (a ↔ b) ↔ ((¬a ∨ b) ∧ (a ∨ ¬b)) :=
decidable.iff_iff_not_or_and_or_not

-- See Note [decidable namespace]
protected theorem decidable.not_and_not_right [decidable b] : ¬(a ∧ ¬b) ↔ (a → b) :=
⟨λ h ha, h.decidable_imp_symm $ and.intro ha, λ h ⟨ha, hb⟩, hb $ h ha⟩

theorem not_and_not_right : ¬(a ∧ ¬b) ↔ (a → b) := decidable.not_and_not_right

/-- Transfer decidability of `a` to decidability of `b`, if the propositions are equivalent.
**Important**: this function should be used instead of `rw` on `decidable b`, because the
kernel will get stuck reducing the usage of `propext` otherwise,
and `dec_trivial` will not work. -/
@[inline] def decidable_of_iff (a : Prop) (h : a ↔ b) [D : decidable a] : decidable b :=
decidable_of_decidable_of_iff D h

/-- Transfer decidability of `b` to decidability of `a`, if the propositions are equivalent.
This is the same as `decidable_of_iff` but the iff is flipped. -/
@[inline] def decidable_of_iff' (b : Prop) (h : a ↔ b) [D : decidable b] : decidable a :=
decidable_of_decidable_of_iff D h.symm

/-- Prove that `a` is decidable by constructing a boolean `b` and a proof that `b ↔ a`.
(This is sometimes taken as an alternate definition of decidability.) -/
def decidable_of_bool : ∀ (b : bool) (h : b ↔ a), decidable a
| tt h := is_true (h.1 rfl)
| ff h := is_false (mt h.2 bool.ff_ne_tt)

/-! ### De Morgan's laws -/

theorem not_and_of_not_or_not (h : ¬ a ∨ ¬ b) : ¬ (a ∧ b)
| ⟨ha, hb⟩ := or.elim h (absurd ha) (absurd hb)

-- See Note [decidable namespace]
protected theorem decidable.not_and_distrib [decidable a] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
⟨λ h, if ha : a then or.inr (λ hb, h ⟨ha, hb⟩) else or.inl ha, not_and_of_not_or_not⟩

-- See Note [decidable namespace]
protected theorem decidable.not_and_distrib' [decidable b] : ¬ (a ∧ b) ↔ ¬a ∨ ¬b :=
⟨λ h, if hb : b then or.inl (λ ha, h ⟨ha, hb⟩) else or.inr hb, not_and_of_not_or_not⟩

/-- One of de Morgan's laws: the negation of a conjunction is logically equivalent to the
disjunction of the negations. -/
theorem not_and_distrib : ¬ (a ∧ b) ↔ ¬a ∨ ¬b := decidable.not_and_distrib

@[simp] theorem not_and : ¬ (a ∧ b) ↔ (a → ¬ b) := and_imp

theorem not_and' : ¬ (a ∧ b) ↔ b → ¬a :=
not_and.trans imp_not_comm

/-- One of de Morgan's laws: the negation of a disjunction is logically equivalent to the
conjunction of the negations. -/
theorem not_or_distrib : ¬ (a ∨ b) ↔ ¬ a ∧ ¬ b :=
⟨λ h, ⟨λ ha, h (or.inl ha), λ hb, h (or.inr hb)⟩,
 λ ⟨h₁, h₂⟩ h, or.elim h h₁ h₂⟩

-- See Note [decidable namespace]
protected theorem decidable.or_iff_not_and_not [decidable a] [decidable b] : a ∨ b ↔ ¬ (¬a ∧ ¬b) :=
by rw [← not_or_distrib, decidable.not_not]

theorem or_iff_not_and_not : a ∨ b ↔ ¬ (¬a ∧ ¬b) := decidable.or_iff_not_and_not

-- See Note [decidable namespace]
protected theorem decidable.and_iff_not_or_not [decidable a] [decidable b] :
  a ∧ b ↔ ¬ (¬ a ∨ ¬ b) :=
by rw [← decidable.not_and_distrib, decidable.not_not]

theorem and_iff_not_or_not : a ∧ b ↔ ¬ (¬ a ∨ ¬ b) := decidable.and_iff_not_or_not

@[simp] theorem not_xor (P Q : Prop) : ¬ xor P Q ↔ (P ↔ Q) :=
by simp only [not_and, xor, not_or_distrib, not_not, ← iff_iff_implies_and_implies]

theorem xor_iff_not_iff (P Q : Prop) : xor P Q ↔ ¬ (P ↔ Q) :=
by rw [iff_not_comm, not_xor]


end propositional

/-! ### Declarations about equality -/

section equality
variables {α : Sort*} {a b : α}

@[simp] theorem heq_iff_eq : a == b ↔ a = b :=
⟨eq_of_heq, heq_of_eq⟩

theorem proof_irrel_heq {p q : Prop} (hp : p) (hq : q) : hp == hq :=
have p = q, from propext ⟨λ _, hq, λ _, hp⟩,
by subst q; refl

theorem ne_of_mem_of_not_mem {α β} [has_mem α β] {s : β} {a b : α}
  (h : a ∈ s) : b ∉ s → a ≠ b :=
mt $ λ e, e ▸ h

-- todo: change name
lemma ball_cond_comm {α} {s : α → Prop} {p : α → α → Prop} :
  (∀ a, s a → ∀ b, s b → p a b) ↔ (∀ a b, s a → s b → p a b) :=
⟨λ h a b ha hb, h a ha b hb, λ h a ha b hb, h a b ha hb⟩

lemma ball_mem_comm {α β} [has_mem α β] {s : β} {p : α → α → Prop} :
  (∀ a b ∈ s, p a b) ↔ (∀ a b, a ∈ s → b ∈ s → p a b) :=
ball_cond_comm

lemma ne_of_apply_ne {α β : Sort*} (f : α → β) {x y : α} (h : f x ≠ f y) : x ≠ y :=
λ (w : x = y), h (congr_arg f w)

theorem eq_equivalence : equivalence (@eq α) :=
⟨eq.refl, @eq.symm _, @eq.trans _⟩

/-- Transport through trivial families is the identity. -/
@[simp]
lemma eq_rec_constant {α : Sort*} {a a' : α} {β : Sort*} (y : β) (h : a = a') :
  (@eq.rec α a (λ a, β) y a' h) = y :=
by { cases h, refl, }

@[simp]
lemma eq_mp_eq_cast {α β : Sort*} (h : α = β) : eq.mp h = cast h := rfl

@[simp]
lemma eq_mpr_eq_cast {α β : Sort*} (h : α = β) : eq.mpr h = cast h.symm := rfl

@[simp]
lemma cast_cast : ∀ {α β γ : Sort*} (ha : α = β) (hb : β = γ) (a : α),
  cast hb (cast ha a) = cast (ha.trans hb) a
| _ _ _ rfl rfl a := rfl

@[simp] lemma congr_refl_left {α β : Sort*} (f : α → β) {a b : α} (h : a = b) :
  congr (eq.refl f) h = congr_arg f h :=
rfl

@[simp] lemma congr_refl_right {α β : Sort*} {f g : α → β} (h : f = g) (a : α) :
  congr h (eq.refl a) = congr_fun h a :=
rfl

@[simp] lemma congr_arg_refl {α β : Sort*} (f : α → β) (a : α) :
  congr_arg f (eq.refl a) = eq.refl (f a) :=
rfl

@[simp] lemma congr_fun_rfl {α β : Sort*} (f : α → β) (a : α) :
  congr_fun (eq.refl f) a = eq.refl (f a) :=
rfl

@[simp] lemma congr_fun_congr_arg {α β γ : Sort*} (f : α → β → γ) {a a' : α} (p : a = a') (b : β) :
  congr_fun (congr_arg f p) b = congr_arg (λ a, f a b) p :=
rfl

lemma heq_of_cast_eq :
  ∀ {α β : Sort*} {a : α} {a' : β} (e : α = β) (h₂ : cast e a = a'), a == a'
| α ._ a a' rfl h := eq.rec_on h (heq.refl _)

lemma cast_eq_iff_heq {α β : Sort*} {a : α} {a' : β} {e : α = β} : cast e a = a' ↔ a == a' :=
⟨heq_of_cast_eq _, λ h, by cases h; refl⟩

lemma rec_heq_of_heq {β} {C : α → Sort*} {x : C a} {y : β} (eq : a = b) (h : x == y) :
  @eq.rec α a C x b eq == y :=
by subst eq; exact h

protected lemma eq.congr {x₁ x₂ y₁ y₂ : α} (h₁ : x₁ = y₁) (h₂ : x₂ = y₂) :
  (x₁ = x₂) ↔ (y₁ = y₂) :=
by { subst h₁, subst h₂ }

lemma eq.congr_left {x y z : α} (h : x = y) : x = z ↔ y = z := by rw [h]
lemma eq.congr_right {x y z : α} (h : x = y) : z = x ↔ z = y := by rw [h]

lemma congr_arg2 {α β γ : Sort*} (f : α → β → γ) {x x' : α} {y y' : β}
  (hx : x = x') (hy : y = y') : f x y = f x' y' :=
by { subst hx, subst hy }

end equality

/-! ### Declarations about quantifiers -/

section quantifiers
variables {α : Sort*}

section congr
variables {β : α → Sort*} {γ : Π a, β a → Sort*} {δ : Π a b, γ a b → Sort*}
  {ε : Π a b c, δ a b c → Sort*}

lemma forall₂_congr {p q : Π a, β a → Prop} (h : ∀ a b, p a b ↔ q a b) :
  (∀ a b, p a b) ↔ ∀ a b, q a b :=
forall_congr $ λ a, forall_congr $ h a

lemma forall₃_congr {p q : Π a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
  (∀ a b c, p a b c) ↔ ∀ a b c, q a b c :=
forall_congr $ λ a, forall₂_congr $ h a

lemma forall₄_congr {p q : Π a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
  (∀ a b c d, p a b c d) ↔ ∀ a b c d, q a b c d :=
forall_congr $ λ a, forall₃_congr $ h a

lemma forall₅_congr {p q : Π a b c d, ε a b c d → Prop}
  (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
  (∀ a b c d e, p a b c d e) ↔ ∀ a b c d e, q a b c d e :=
forall_congr $ λ a, forall₄_congr $ h a

lemma exists₂_congr {p q : Π a, β a → Prop}  (h : ∀ a b, p a b ↔ q a b) :
  (∃ a b, p a b) ↔ ∃ a b, q a b :=
exists_congr $ λ a, exists_congr $ h a

lemma exists₃_congr {p q : Π a b, γ a b → Prop} (h : ∀ a b c, p a b c ↔ q a b c) :
  (∃ a b c, p a b c) ↔ ∃ a b c, q a b c :=
exists_congr $ λ a, exists₂_congr $ h a

lemma exists₄_congr {p q : Π a b c, δ a b c → Prop} (h : ∀ a b c d, p a b c d ↔ q a b c d) :
  (∃ a b c d, p a b c d) ↔ ∃ a b c d, q a b c d :=
exists_congr $ λ a, exists₃_congr $ h a

lemma exists₅_congr {p q : Π a b c d, ε a b c d → Prop}
  (h : ∀ a b c d e, p a b c d e ↔ q a b c d e) :
  (∃ a b c d e, p a b c d e) ↔ ∃ a b c d e, q a b c d e :=
exists_congr $ λ a, exists₄_congr $ h a

end congr

variables {β : Sort*} {p q : α → Prop} {b : Prop}

lemma forall_imp (h : ∀ a, p a → q a) : (∀ a, p a) → ∀ a, q a :=
λ h' a, h a (h' a)

lemma Exists.imp (h : ∀ a, (p a → q a)) (p : ∃ a, p a) : ∃ a, q a := exists_imp_exists h p

lemma exists_imp_exists' {p : α → Prop} {q : β → Prop} (f : α → β) (hpq : ∀ a, p a → q (f a))
  (hp : ∃ a, p a) : ∃ b, q b :=
exists.elim hp (λ a hp', ⟨_, hpq _ hp'⟩)

theorem forall_swap {p : α → β → Prop} : (∀ x y, p x y) ↔ ∀ y x, p x y :=
⟨swap, swap⟩

/-- We intentionally restrict the type of `α` in this lemma so that this is a safer to use in simp
than `forall_swap`. -/
lemma imp_forall_iff {α : Type*} {p : Prop} {q : α → Prop} : (p → ∀ x, q x) ↔ (∀ x, p → q x) :=
forall_swap

theorem exists_swap {p : α → β → Prop} : (∃ x y, p x y) ↔ ∃ y x, p x y :=
⟨λ ⟨x, y, h⟩, ⟨y, x, h⟩, λ ⟨y, x, h⟩, ⟨x, y, h⟩⟩

@[simp] theorem forall_exists_index {q : (∃ x, p x) → Prop} :
  (∀ h, q h) ↔ ∀ x (h : p x), q ⟨x, h⟩ :=
⟨λ h x hpx, h ⟨x, hpx⟩, λ h ⟨x, hpx⟩, h x hpx⟩

theorem exists_imp_distrib : ((∃ x, p x) → b) ↔ ∀ x, p x → b :=
forall_exists_index

/--
Extract an element from a existential statement, using `classical.some`.
-/
-- This enables projection notation.
@[reducible] noncomputable def Exists.some {p : α → Prop} (P : ∃ a, p a) : α := classical.some P

/--
Show that an element extracted from `P : ∃ a, p a` using `P.some` satisfies `p`.
-/
lemma Exists.some_spec {p : α → Prop} (P : ∃ a, p a) : p (P.some) := classical.some_spec P

--theorem forall_not_of_not_exists (h : ¬ ∃ x, p x) : ∀ x, ¬ p x :=
--forall_imp_of_exists_imp h

theorem not_exists_of_forall_not (h : ∀ x, ¬ p x) : ¬ ∃ x, p x :=
exists_imp_distrib.2 h

@[simp] theorem not_exists : (¬ ∃ x, p x) ↔ ∀ x, ¬ p x :=
exists_imp_distrib

theorem not_forall_of_exists_not : (∃ x, ¬ p x) → ¬ ∀ x, p x
| ⟨x, hn⟩ h := hn (h x)

-- See Note [decidable namespace]
protected theorem decidable.not_forall {p : α → Prop}
  [decidable (∃ x, ¬ p x)] [∀ x, decidable (p x)] : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x :=
⟨not.decidable_imp_symm $ λ nx x, nx.decidable_imp_symm $ λ h, ⟨x, h⟩,
 not_forall_of_exists_not⟩

@[simp] theorem not_forall {p : α → Prop} : (¬ ∀ x, p x) ↔ ∃ x, ¬ p x := decidable.not_forall

-- See Note [decidable namespace]
protected theorem decidable.not_forall_not [decidable (∃ x, p x)] :
  (¬ ∀ x, ¬ p x) ↔ ∃ x, p x :=
(@decidable.not_iff_comm _ _ _ (decidable_of_iff (¬ ∃ x, p x) not_exists)).1 not_exists

theorem not_forall_not : (¬ ∀ x, ¬ p x) ↔ ∃ x, p x := decidable.not_forall_not

-- See Note [decidable namespace]
protected theorem decidable.not_exists_not [∀ x, decidable (p x)] : (¬ ∃ x, ¬ p x) ↔ ∀ x, p x :=
by simp [decidable.not_not]

@[simp] theorem not_exists_not : (¬ ∃ x, ¬ p x) ↔ ∀ x, p x := decidable.not_exists_not

theorem forall_imp_iff_exists_imp [ha : nonempty α] : ((∀ x, p x) → b) ↔ ∃ x, p x → b :=
let ⟨a⟩ := ha in
⟨λ h, not_forall_not.1 $ λ h', classical.by_cases (λ hb : b, h' a $ λ _, hb)
  (λ hb, hb $ h $ λ x, (not_imp.1 (h' x)).1), λ ⟨x, hx⟩ h, hx (h x)⟩

-- TODO: duplicate of a lemma in core
theorem forall_true_iff : (α → true) ↔ true :=
implies_true_iff α

-- Unfortunately this causes simp to loop sometimes, so we
-- add the 2 and 3 cases as simp lemmas instead
theorem forall_true_iff' (h : ∀ a, p a ↔ true) : (∀ a, p a) ↔ true :=
iff_true_intro (λ _, of_iff_true (h _))

@[simp] theorem forall_2_true_iff {β : α → Sort*} : (∀ a, β a → true) ↔ true :=
forall_true_iff' $ λ _, forall_true_iff

@[simp] theorem forall_3_true_iff {β : α → Sort*} {γ : Π a, β a → Sort*} :
  (∀ a (b : β a), γ a b → true) ↔ true :=
forall_true_iff' $ λ _, forall_2_true_iff

lemma exists_unique.exists {α : Sort*} {p : α → Prop} (h : ∃! x, p x) : ∃ x, p x :=
exists.elim h (λ x hx, ⟨x, and.left hx⟩)

@[simp] lemma exists_unique_iff_exists {α : Sort*} [subsingleton α] {p : α → Prop} :
  (∃! x, p x) ↔ ∃ x, p x :=
⟨λ h, h.exists, Exists.imp $ λ x hx, ⟨hx, λ y _, subsingleton.elim y x⟩⟩

@[simp] theorem forall_const (α : Sort*) [i : nonempty α] : (α → b) ↔ b :=
⟨i.elim, λ hb x, hb⟩

@[simp] theorem exists_const (α : Sort*) [i : nonempty α] : (∃ x : α, b) ↔ b :=
⟨λ ⟨x, h⟩, h, i.elim exists.intro⟩

theorem exists_unique_const (α : Sort*) [i : nonempty α] [subsingleton α] :
  (∃! x : α, b) ↔ b :=
by simp

theorem forall_and_distrib : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
⟨λ h, ⟨λ x, (h x).left, λ x, (h x).right⟩, λ ⟨h₁, h₂⟩ x, ⟨h₁ x, h₂ x⟩⟩

theorem exists_or_distrib : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
⟨λ ⟨x, hpq⟩, hpq.elim (λ hpx, or.inl ⟨x, hpx⟩) (λ hqx, or.inr ⟨x, hqx⟩),
 λ hepq, hepq.elim (λ ⟨x, hpx⟩, ⟨x, or.inl hpx⟩) (λ ⟨x, hqx⟩, ⟨x, or.inr hqx⟩)⟩

@[simp] theorem exists_and_distrib_left {q : Prop} {p : α → Prop} :
  (∃x, q ∧ p x) ↔ q ∧ (∃x, p x) :=
⟨λ ⟨x, hq, hp⟩, ⟨hq, x, hp⟩, λ ⟨hq, x, hp⟩, ⟨x, hq, hp⟩⟩

@[simp] theorem exists_and_distrib_right {q : Prop} {p : α → Prop} :
  (∃x, p x ∧ q) ↔ (∃x, p x) ∧ q :=
by simp [and_comm]

@[simp] theorem forall_eq {a' : α} : (∀a, a = a' → p a) ↔ p a' :=
⟨λ h, h a' rfl, λ h a e, e.symm ▸ h⟩

@[simp] theorem forall_eq' {a' : α} : (∀a, a' = a → p a) ↔ p a' :=
by simp [@eq_comm _ a']

theorem and_forall_ne (a : α) : (p a ∧ ∀ b ≠ a, p b) ↔ ∀ b, p b :=
by simp only [← @forall_eq _ p a, ← forall_and_distrib, ← or_imp_distrib, classical.em,
  forall_const]

-- this lemma is needed to simplify the output of `list.mem_cons_iff`
@[simp] theorem forall_eq_or_imp {a' : α} : (∀ a, a = a' ∨ q a → p a) ↔ p a' ∧ ∀ a, q a → p a :=
by simp only [or_imp_distrib, forall_and_distrib, forall_eq]

theorem exists_eq {a' : α} : ∃ a, a = a' := ⟨_, rfl⟩

@[simp] theorem exists_eq' {a' : α} : ∃ a, a' = a := ⟨_, rfl⟩

@[simp] theorem exists_unique_eq {a' : α} : ∃! a, a = a' :=
by simp only [eq_comm, exists_unique, and_self, forall_eq', exists_eq']

@[simp] theorem exists_unique_eq' {a' : α} : ∃! a, a' = a :=
by simp only [exists_unique, and_self, forall_eq', exists_eq']

@[simp] theorem exists_eq_left {a' : α} : (∃ a, a = a' ∧ p a) ↔ p a' :=
⟨λ ⟨a, e, h⟩, e ▸ h, λ h, ⟨_, rfl, h⟩⟩

@[simp] theorem exists_eq_right {a' : α} : (∃ a, p a ∧ a = a') ↔ p a' :=
(exists_congr $ by exact λ a, and.comm).trans exists_eq_left

@[simp] theorem exists_eq_right_right {a' : α} :
  (∃ (a : α), p a ∧ b ∧ a = a') ↔ p a' ∧ b :=
⟨λ ⟨_, hp, hq, rfl⟩, ⟨hp, hq⟩, λ ⟨hp, hq⟩, ⟨a', hp, hq, rfl⟩⟩

@[simp] theorem exists_eq_right_right' {a' : α} :
  (∃ (a : α), p a ∧ b ∧ a' = a) ↔ p a' ∧ b :=
⟨λ ⟨_, hp, hq, rfl⟩, ⟨hp, hq⟩, λ ⟨hp, hq⟩, ⟨a', hp, hq, rfl⟩⟩

@[simp] theorem exists_apply_eq_apply (f : α → β) (a' : α) : ∃ a, f a = f a' := ⟨a', rfl⟩

@[simp] theorem exists_apply_eq_apply' (f : α → β) (a' : α) : ∃ a, f a' = f a := ⟨a', rfl⟩

@[simp] theorem exists_exists_and_eq_and {f : α → β} {p : α → Prop} {q : β → Prop} :
  (∃ b, (∃ a, p a ∧ f a = b) ∧ q b) ↔ ∃ a, p a ∧ q (f a) :=
⟨λ ⟨b, ⟨a, ha, hab⟩, hb⟩, ⟨a, ha, hab.symm ▸ hb⟩, λ ⟨a, hp, hq⟩, ⟨f a, ⟨a, hp, rfl⟩, hq⟩⟩

@[simp] theorem exists_exists_eq_and {f : α → β} {p : β → Prop} :
  (∃ b, (∃ a, f a = b) ∧ p b) ↔ ∃ a, p (f a) :=
⟨λ ⟨b, ⟨a, ha⟩, hb⟩, ⟨a, ha.symm ▸ hb⟩, λ ⟨a, ha⟩, ⟨f a, ⟨a, rfl⟩, ha⟩⟩

@[simp] lemma exists_or_eq_left (y : α) (p : α → Prop) : ∃ (x : α), x = y ∨ p x :=
⟨y, or.inl rfl⟩

@[simp] lemma exists_or_eq_right (y : α) (p : α → Prop) : ∃ (x : α), p x ∨ x = y :=
⟨y, or.inr rfl⟩

@[simp] lemma exists_or_eq_left' (y : α) (p : α → Prop) : ∃ (x : α), y = x ∨ p x :=
⟨y, or.inl rfl⟩

@[simp] lemma exists_or_eq_right' (y : α) (p : α → Prop) : ∃ (x : α), p x ∨ y = x :=
⟨y, or.inr rfl⟩

@[simp] theorem forall_apply_eq_imp_iff {f : α → β} {p : β → Prop} :
  (∀ a, ∀ b, f a = b → p b) ↔ (∀ a, p (f a)) :=
⟨λ h a, h a (f a) rfl, λ h a b hab, hab ▸ h a⟩

@[simp] theorem forall_apply_eq_imp_iff' {f : α → β} {p : β → Prop} :
  (∀ b, ∀ a, f a = b → p b) ↔ (∀ a, p (f a)) :=
by { rw forall_swap, simp }

@[simp] theorem forall_eq_apply_imp_iff {f : α → β} {p : β → Prop} :
  (∀ a, ∀ b, b = f a → p b) ↔ (∀ a, p (f a)) :=
by simp [@eq_comm _ _ (f _)]

@[simp] theorem forall_eq_apply_imp_iff' {f : α → β} {p : β → Prop} :
  (∀ b, ∀ a, b = f a → p b) ↔ (∀ a, p (f a)) :=
by { rw forall_swap, simp }

@[simp] theorem forall_apply_eq_imp_iff₂ {f : α → β} {p : α → Prop} {q : β → Prop} :
  (∀ b, ∀ a, p a → f a = b → q b) ↔ ∀ a, p a → q (f a) :=
⟨λ h a ha, h (f a) a ha rfl, λ h b a ha hb, hb ▸ h a ha⟩

@[simp] theorem exists_eq_left' {a' : α} : (∃ a, a' = a ∧ p a) ↔ p a' :=
by simp [@eq_comm _ a']

@[simp] theorem exists_eq_right' {a' : α} : (∃ a, p a ∧ a' = a) ↔ p a' :=
by simp [@eq_comm _ a']

theorem exists_comm {p : α → β → Prop} : (∃ a b, p a b) ↔ ∃ b a, p a b :=
⟨λ ⟨a, b, h⟩, ⟨b, a, h⟩, λ ⟨b, a, h⟩, ⟨a, b, h⟩⟩

theorem and.exists {p q : Prop} {f : p ∧ q → Prop} : (∃ h, f h) ↔ ∃ hp hq, f ⟨hp, hq⟩ :=
⟨λ ⟨h, H⟩, ⟨h.1, h.2, H⟩, λ ⟨hp, hq, H⟩, ⟨⟨hp, hq⟩, H⟩⟩

theorem forall_or_of_or_forall (h : b ∨ ∀x, p x) (x) : b ∨ p x :=
h.imp_right $ λ h₂, h₂ x

-- See Note [decidable namespace]
protected theorem decidable.forall_or_distrib_left {q : Prop} {p : α → Prop} [decidable q] :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) :=
⟨λ h, if hq : q then or.inl hq else or.inr $ λ x, (h x).resolve_left hq,
  forall_or_of_or_forall⟩

theorem forall_or_distrib_left {q : Prop} {p : α → Prop} :
  (∀x, q ∨ p x) ↔ q ∨ (∀x, p x) := decidable.forall_or_distrib_left

-- See Note [decidable namespace]
protected theorem decidable.forall_or_distrib_right {q : Prop} {p : α → Prop} [decidable q] :
  (∀x, p x ∨ q) ↔ (∀x, p x) ∨ q :=
by simp [or_comm, decidable.forall_or_distrib_left]

theorem forall_or_distrib_right {q : Prop} {p : α → Prop} :
  (∀x, p x ∨ q) ↔ (∀x, p x) ∨ q := decidable.forall_or_distrib_right

@[simp] theorem exists_prop {p q : Prop} : (∃ h : p, q) ↔ p ∧ q :=
⟨λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩, λ ⟨h₁, h₂⟩, ⟨h₁, h₂⟩⟩

theorem exists_unique_prop {p q : Prop} : (∃! h : p, q) ↔ p ∧ q :=
by simp

@[simp] theorem exists_false : ¬ (∃a:α, false) := assume ⟨a, h⟩, h

@[simp] lemma exists_unique_false : ¬ (∃! (a : α), false) := assume ⟨a, h, h'⟩, h

theorem Exists.fst {p : b → Prop} : Exists p → b
| ⟨h, _⟩ := h

theorem Exists.snd {p : b → Prop} : ∀ h : Exists p, p h.fst
| ⟨_, h⟩ := h

theorem forall_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∀ h' : p, q h') ↔ q h :=
@forall_const (q h) p ⟨h⟩

theorem exists_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃ h' : p, q h') ↔ q h :=
@exists_const (q h) p ⟨h⟩

lemma exists_iff_of_forall {p : Prop} {q : p → Prop} (h : ∀ h, q h) : (∃ h, q h) ↔ p :=
⟨Exists.fst, λ H, ⟨H, h H⟩⟩

theorem exists_unique_prop_of_true {p : Prop} {q : p → Prop} (h : p) : (∃! h' : p, q h') ↔ q h :=
@exists_unique_const (q h) p ⟨h⟩ _

theorem forall_prop_of_false {p : Prop} {q : p → Prop} (hn : ¬ p) :
  (∀ h' : p, q h') ↔ true :=
iff_true_intro $ λ h, hn.elim h

theorem exists_prop_of_false {p : Prop} {q : p → Prop} : ¬ p → ¬ (∃ h' : p, q h') :=
mt Exists.fst

@[congr] lemma exists_prop_congr {p p' : Prop} {q q' : p → Prop}
  (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') : Exists q ↔ ∃ h : p', q' (hp.2 h) :=
⟨λ ⟨_, _⟩, ⟨hp.1 ‹_›, (hq _).1 ‹_›⟩, λ ⟨_, _⟩, ⟨_, (hq _).2 ‹_›⟩⟩

@[congr] lemma exists_prop_congr' {p p' : Prop} {q q' : p → Prop}
  (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') : Exists q = ∃ h : p', q' (hp.2 h) :=
propext (exists_prop_congr hq _)

@[simp] lemma exists_true_left (p : true → Prop) : (∃ x, p x) ↔ p true.intro :=
exists_prop_of_true _

@[simp] lemma exists_false_left (p : false → Prop) : ¬ ∃ x, p x :=
exists_prop_of_false not_false

lemma exists_unique.unique {α : Sort*} {p : α → Prop} (h : ∃! x, p x)
  {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂ :=
unique_of_exists_unique h py₁ py₂

@[congr] lemma forall_prop_congr {p p' : Prop} {q q' : p → Prop}
  (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') : (∀ h, q h) ↔ ∀ h : p', q' (hp.2 h) :=
⟨λ h1 h2, (hq _).1 (h1 (hp.2 _)), λ h1 h2, (hq _).2 (h1 (hp.1 h2))⟩

@[congr] lemma forall_prop_congr' {p p' : Prop} {q q' : p → Prop}
  (hq : ∀ h, q h ↔ q' h) (hp : p ↔ p') : (∀ h, q h) = ∀ h : p', q' (hp.2 h) :=
propext (forall_prop_congr hq _)

@[simp] lemma forall_true_left (p : true → Prop) : (∀ x, p x) ↔ p true.intro :=
forall_prop_of_true _

@[simp] lemma forall_false_left (p : false → Prop) : (∀ x, p x) ↔ true :=
forall_prop_of_false not_false

lemma exists_unique.elim2 {α : Sort*} {p : α → Sort*} [∀ x, subsingleton (p x)]
  {q : Π x (h : p x), Prop} {b : Prop} (h₂ : ∃! x (h : p x), q x h)
  (h₁ : ∀ x (h : p x), q x h → (∀ y (hy : p y), q y hy → y = x) → b) : b :=
begin
  simp only [exists_unique_iff_exists] at h₂,
  apply h₂.elim,
  exact λ x ⟨hxp, hxq⟩ H, h₁ x hxp hxq (λ y hyp hyq, H y ⟨hyp, hyq⟩)
end

lemma exists_unique.intro2 {α : Sort*} {p : α → Sort*} [∀ x, subsingleton (p x)]
  {q : Π (x : α) (h : p x), Prop} (w : α) (hp : p w) (hq : q w hp)
  (H : ∀ y (hy : p y), q y hy → y = w) :
  ∃! x (hx : p x), q x hx :=
begin
  simp only [exists_unique_iff_exists],
  exact exists_unique.intro w ⟨hp, hq⟩ (λ y ⟨hyp, hyq⟩, H y hyp hyq)
end

lemma exists_unique.exists2 {α : Sort*} {p : α → Sort*} {q : Π (x : α) (h : p x), Prop}
  (h : ∃! x (hx : p x), q x hx) :
  ∃ x (hx : p x), q x hx :=
h.exists.imp (λ x hx, hx.exists)

lemma exists_unique.unique2 {α : Sort*} {p : α → Sort*} [∀ x, subsingleton (p x)]
  {q : Π (x : α) (hx : p x), Prop} (h : ∃! x (hx : p x), q x hx)
  {y₁ y₂ : α} (hpy₁ : p y₁) (hqy₁ : q y₁ hpy₁)
  (hpy₂ : p y₂) (hqy₂ : q y₂ hpy₂) : y₁ = y₂ :=
begin
  simp only [exists_unique_iff_exists] at h,
  exact h.unique ⟨hpy₁, hqy₁⟩ ⟨hpy₂, hqy₂⟩
end

end quantifiers

/-! ### Classical lemmas -/

namespace classical
variables {α : Sort*} {p : α → Prop}

theorem cases {p : Prop → Prop} (h1 : p true) (h2 : p false) : ∀a, p a :=
assume a, cases_on a h1 h2

/- use shortened names to avoid conflict when classical namespace is open. -/
/-- Any prop `p` is decidable classically. A shorthand for `classical.prop_decidable`. -/
noncomputable def dec (p : Prop) : decidable p :=
by apply_instance
/-- Any predicate `p` is decidable classically. -/
noncomputable def dec_pred (p : α → Prop) : decidable_pred p :=
by apply_instance
/-- Any relation `p` is decidable classically. -/
noncomputable def dec_rel (p : α → α → Prop) : decidable_rel p :=
by apply_instance
/-- Any type `α` has decidable equality classically. -/
noncomputable def dec_eq (α : Sort*) : decidable_eq α :=
by apply_instance

/-- Construct a function from a default value `H0`, and a function to use if there exists a value
satisfying the predicate. -/
@[elab_as_eliminator]
noncomputable def {u} exists_cases {C : Sort u} (H0 : C) (H : ∀ a, p a → C) : C :=
if h : ∃ a, p a then H (classical.some h) (classical.some_spec h) else H0

lemma some_spec2 {α : Sort*} {p : α → Prop} {h : ∃a, p a}
  (q : α → Prop) (hpq : ∀a, p a → q a) : q (some h) :=
hpq _ $ some_spec _

/-- A version of classical.indefinite_description which is definitionally equal to a pair -/
noncomputable def subtype_of_exists {α : Type*} {P : α → Prop} (h : ∃ x, P x) : {x // P x} :=
⟨classical.some h, classical.some_spec h⟩

/-- A version of `by_contradiction` that uses types instead of propositions. -/
protected noncomputable def by_contradiction' {α : Sort*} (H : ¬ (α → false)) : α :=
classical.choice $ peirce _ false $ λ h, (H $ λ a, h ⟨a⟩).elim

/-- `classical.by_contradiction'` is equivalent to lean's axiom `classical.choice`. -/
def choice_of_by_contradiction' {α : Sort*} (contra : ¬ (α → false) → α) : nonempty α → α :=
λ H, contra H.elim

end classical

/-- This function has the same type as `exists.rec_on`, and can be used to case on an equality,
but `exists.rec_on` can only eliminate into Prop, while this version eliminates into any universe
using the axiom of choice. -/
@[elab_as_eliminator]
noncomputable def {u} exists.classical_rec_on
 {α} {p : α → Prop} (h : ∃ a, p a) {C : Sort u} (H : ∀ a, p a → C) : C :=
H (classical.some h) (classical.some_spec h)

/-! ### Declarations about bounded quantifiers -/

section bounded_quantifiers
variables {α : Sort*} {r p q : α → Prop} {P Q : ∀ x, p x → Prop} {b : Prop}

theorem bex_def : (∃ x (h : p x), q x) ↔ ∃ x, p x ∧ q x :=
⟨λ ⟨x, px, qx⟩, ⟨x, px, qx⟩, λ ⟨x, px, qx⟩, ⟨x, px, qx⟩⟩

theorem bex.elim {b : Prop} : (∃ x h, P x h) → (∀ a h, P a h → b) → b
| ⟨a, h₁, h₂⟩ h' := h' a h₁ h₂

theorem bex.intro (a : α) (h₁ : p a) (h₂ : P a h₁) : ∃ x (h : p x), P x h :=
⟨a, h₁, h₂⟩

theorem ball_congr (H : ∀ x h, P x h ↔ Q x h) :
  (∀ x h, P x h) ↔ (∀ x h, Q x h) :=
forall_congr $ λ x, forall_congr (H x)

theorem bex_congr (H : ∀ x h, P x h ↔ Q x h) :
  (∃ x h, P x h) ↔ (∃ x h, Q x h) :=
exists_congr $ λ x, exists_congr (H x)

theorem bex_eq_left {a : α} : (∃ x (_ : x = a), p x) ↔ p a :=
by simp only [exists_prop, exists_eq_left]

theorem ball.imp_right (H : ∀ x h, (P x h → Q x h))
  (h₁ : ∀ x h, P x h) (x h) : Q x h :=
H _ _ $ h₁ _ _

theorem bex.imp_right (H : ∀ x h, (P x h → Q x h)) :
  (∃ x h, P x h) → ∃ x h, Q x h
| ⟨x, h, h'⟩ := ⟨_, _, H _ _ h'⟩

theorem ball.imp_left (H : ∀ x, p x → q x)
  (h₁ : ∀ x, q x → r x) (x) (h : p x) : r x :=
h₁ _ $ H _ h

theorem bex.imp_left (H : ∀ x, p x → q x) :
  (∃ x (_ : p x), r x) → ∃ x (_ : q x), r x
| ⟨x, hp, hr⟩ := ⟨x, H _ hp, hr⟩

theorem ball_of_forall (h : ∀ x, p x) (x) : p x :=
h x

theorem forall_of_ball (H : ∀ x, p x) (h : ∀ x, p x → q x) (x) : q x :=
h x $ H x

theorem bex_of_exists (H : ∀ x, p x) : (∃ x, q x) → ∃ x (_ : p x), q x
| ⟨x, hq⟩ := ⟨x, H x, hq⟩

theorem exists_of_bex : (∃ x (_ : p x), q x) → ∃ x, q x
| ⟨x, _, hq⟩ := ⟨x, hq⟩

@[simp] theorem bex_imp_distrib : ((∃ x h, P x h) → b) ↔ (∀ x h, P x h → b) :=
by simp

theorem not_bex : (¬ ∃ x h, P x h) ↔ ∀ x h, ¬ P x h :=
bex_imp_distrib

theorem not_ball_of_bex_not : (∃ x h, ¬ P x h) → ¬ ∀ x h, P x h
| ⟨x, h, hp⟩ al := hp $ al x h

-- See Note [decidable namespace]
protected theorem decidable.not_ball [decidable (∃ x h, ¬ P x h)] [∀ x h, decidable (P x h)] :
  (¬ ∀ x h, P x h) ↔ (∃ x h, ¬ P x h) :=
⟨not.decidable_imp_symm $ λ nx x h, nx.decidable_imp_symm $ λ h', ⟨x, h, h'⟩,
 not_ball_of_bex_not⟩

theorem not_ball : (¬ ∀ x h, P x h) ↔ (∃ x h, ¬ P x h) := decidable.not_ball

theorem ball_true_iff (p : α → Prop) : (∀ x, p x → true) ↔ true :=
iff_true_intro (λ h hrx, trivial)

theorem ball_and_distrib : (∀ x h, P x h ∧ Q x h) ↔ (∀ x h, P x h) ∧ (∀ x h, Q x h) :=
iff.trans (forall_congr $ λ x, forall_and_distrib) forall_and_distrib

theorem bex_or_distrib : (∃ x h, P x h ∨ Q x h) ↔ (∃ x h, P x h) ∨ (∃ x h, Q x h) :=
iff.trans (exists_congr $ λ x, exists_or_distrib) exists_or_distrib

theorem ball_or_left_distrib : (∀ x, p x ∨ q x → r x) ↔ (∀ x, p x → r x) ∧ (∀ x, q x → r x) :=
iff.trans (forall_congr $ λ x, or_imp_distrib) forall_and_distrib

theorem bex_or_left_distrib :
  (∃ x (_ : p x ∨ q x), r x) ↔ (∃ x (_ : p x), r x) ∨ (∃ x (_ : q x), r x) :=
by simp only [exists_prop]; exact
iff.trans (exists_congr $ λ x, or_and_distrib_right) exists_or_distrib

end bounded_quantifiers

namespace classical
local attribute [instance] prop_decidable

theorem not_ball {α : Sort*} {p : α → Prop} {P : Π (x : α), p x → Prop} :
  (¬ ∀ x h, P x h) ↔ (∃ x h, ¬ P x h) := _root_.not_ball

end classical

section ite
variables {α β γ : Sort*} {σ : α → Sort*} (f : α → β) {P Q : Prop} [decidable P] [decidable Q]
  {a b c : α} {A : P → α} {B : ¬ P → α}

lemma dite_eq_iff : dite P A B = c ↔ (∃ h, A h = c) ∨ ∃ h, B h = c := by by_cases P; simp *
lemma ite_eq_iff : ite P a b = c ↔ P ∧ a = c ∨ ¬ P ∧ b = c :=
dite_eq_iff.trans $ by rw [exists_prop, exists_prop]

@[simp] lemma dite_eq_left_iff : dite P (λ _, a) B = a ↔ ∀ h, B h = a := by by_cases P; simp *
@[simp] lemma dite_eq_right_iff : dite P A (λ _, b) = b ↔ ∀ h, A h = b := by by_cases P; simp *
@[simp] lemma ite_eq_left_iff : ite P a b = a ↔ (¬ P → b = a) := dite_eq_left_iff
@[simp] lemma ite_eq_right_iff : ite P a b = b ↔ (P → a = b) := dite_eq_right_iff

lemma dite_ne_left_iff : dite P (λ _, a) B ≠ a ↔ ∃ h, a ≠ B h :=
by { rw [ne.def, dite_eq_left_iff, not_forall], exact exists_congr (λ h, by rw ne_comm) }

lemma dite_ne_right_iff : dite P A (λ _, b) ≠ b ↔ ∃ h, A h ≠ b :=
by simp only [ne.def, dite_eq_right_iff, not_forall]

lemma ite_ne_left_iff : ite P a b ≠ a ↔ ¬ P ∧ a ≠ b := dite_ne_left_iff.trans $ by rw exists_prop
lemma ite_ne_right_iff : ite P a b ≠ b ↔ P ∧ a ≠ b := dite_ne_right_iff.trans $ by rw exists_prop

protected lemma ne.dite_eq_left_iff (h : ∀ h, a ≠ B h) : dite P (λ _, a) B = a ↔ P :=
dite_eq_left_iff.trans $ ⟨λ H, of_not_not $ λ h', h h' (H h').symm, λ h H, (H h).elim⟩

protected lemma ne.dite_eq_right_iff (h : ∀ h, A h ≠ b) : dite P A (λ _, b) = b ↔ ¬ P :=
dite_eq_right_iff.trans $ ⟨λ H h', h h' (H h'), λ h' H, (h' H).elim⟩

protected lemma ne.ite_eq_left_iff (h : a ≠ b) : ite P a b = a ↔ P := ne.dite_eq_left_iff $ λ _, h
protected lemma ne.ite_eq_right_iff (h : a ≠ b) : ite P a b = b ↔ ¬ P :=
ne.dite_eq_right_iff $ λ _, h

protected lemma ne.dite_ne_left_iff (h : ∀ h, a ≠ B h) : dite P (λ _, a) B ≠ a ↔ ¬ P :=
dite_ne_left_iff.trans $ exists_iff_of_forall h

protected lemma ne.dite_ne_right_iff (h : ∀ h, A h ≠ b) : dite P A (λ _, b) ≠ b ↔ P :=
dite_ne_right_iff.trans $ exists_iff_of_forall h

protected lemma ne.ite_ne_left_iff (h : a ≠ b) : ite P a b ≠ a ↔ ¬ P := ne.dite_ne_left_iff $ λ _, h

protected lemma ne.ite_ne_right_iff (h : a ≠ b) : ite P a b ≠ b ↔ P := ne.dite_ne_right_iff $ λ _, h

variables (P Q) (a b)

/-- A `dite` whose results do not actually depend on the condition may be reduced to an `ite`. -/
@[simp] lemma dite_eq_ite : dite P (λ h, a) (λ h, b) = ite P a b := rfl

lemma dite_eq_or_eq : (∃ h, dite P A B = A h) ∨ ∃ h, dite P A B = B h :=
decidable.by_cases (λ h, or.inl ⟨h, dif_pos h⟩) (λ h, or.inr ⟨h, dif_neg h⟩)

lemma ite_eq_or_eq : ite P a b = a ∨ ite P a b = b :=
decidable.by_cases (λ h, or.inl (if_pos h)) (λ h, or.inr (if_neg h))

/-- A function applied to a `dite` is a `dite` of that function applied to each of the branches. -/
lemma apply_dite (x : P → α) (y : ¬P → α) : f (dite P x y) = dite P (λ h, f (x h)) (λ h, f (y h)) :=
by by_cases h : P; simp [h]

/-- A function applied to a `ite` is a `ite` of that function applied to each of the branches. -/
lemma apply_ite : f (ite P a b) = ite P (f a) (f b) := apply_dite f P (λ _, a) (λ _, b)

/-- A two-argument function applied to two `dite`s is a `dite` of that two-argument function
applied to each of the branches. -/
lemma apply_dite2 (f : α → β → γ) (P : Prop) [decidable P] (a : P → α) (b : ¬P → α) (c : P → β)
  (d : ¬P → β) :
  f (dite P a b) (dite P c d) = dite P (λ h, f (a h) (c h)) (λ h, f (b h) (d h)) :=
by by_cases h : P; simp [h]

/-- A two-argument function applied to two `ite`s is a `ite` of that two-argument function
applied to each of the branches. -/
lemma apply_ite2 (f : α → β → γ) (P : Prop) [decidable P] (a b : α) (c d : β) :
  f (ite P a b) (ite P c d) = ite P (f a c) (f b d) :=
apply_dite2 f P (λ _, a) (λ _, b) (λ _, c) (λ _, d)

/-- A 'dite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `dite` that applies
either branch to `a`. -/
lemma dite_apply (f : P → Π a, σ a) (g : ¬ P → Π a, σ a) (a : α) :
  (dite P f g) a = dite P (λ h, f h a) (λ h, g h a) :=
by by_cases h : P; simp [h]

/-- A 'ite' producing a `Pi` type `Π a, σ a`, applied to a value `a : α` is a `ite` that applies
either branch to `a`. -/
lemma ite_apply (f g : Π a, σ a) (a : α) : (ite P f g) a = ite P (f a) (g a) :=
dite_apply P (λ _, f) (λ _, g) a

/-- Negation of the condition `P : Prop` in a `dite` is the same as swapping the branches. -/
@[simp] lemma dite_not (x : ¬ P → α) (y : ¬¬ P → α) :
  dite (¬ P) x y = dite P (λ h, y (not_not_intro h)) x :=
by by_cases h : P; simp [h]

/-- Negation of the condition `P : Prop` in a `ite` is the same as swapping the branches. -/
@[simp] lemma ite_not : ite (¬ P) a b = ite P b a := dite_not P (λ _, a) (λ _, b)

lemma ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b :=
by by_cases hp : P; by_cases hq : Q; simp [hp, hq]

end ite
