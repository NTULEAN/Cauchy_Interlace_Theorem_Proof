/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import logic.function.basic
import tactic.ext
import tactic.lint
import tactic.simps

/-!
# Subtypes

This file provides basic API for subtypes, which are defined in core.

A subtype is a type made from restricting another type, say `α`, to its elements that satisfy some
predicate, say `p : α → Prop`. Specifically, it is the type of pairs `⟨val, property⟩` where
`val : α` and `property : p val`. It is denoted `subtype p` and notation `{val : α // p val}` is
available.

A subtype has a natural coercion to the parent type, by coercing `⟨val, property⟩` to `val`. As
such, subtypes can be thought of as bundled sets, the difference being that elements of a set are
still of type `α` while elements of a subtype aren't.
-/

open function

namespace subtype
variables {α β γ : Sort*} {p q : α → Prop}

/-- See Note [custom simps projection] -/
def simps.coe (x : subtype p) : α := x

initialize_simps_projections subtype (val → coe)

/-- A version of `x.property` or `x.2` where `p` is syntactically applied to the coercion of `x`
  instead of `x.1`. A similar result is `subtype.mem` in `data.set.basic`. -/
lemma prop (x : subtype p) : p x := x.2

@[simp] lemma val_eq_coe {x : subtype p} : x.1 = ↑x := rfl

@[simp] protected theorem «forall» {q : {a // p a} → Prop} :
  (∀ x, q x) ↔ (∀ a b, q ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

/-- An alternative version of `subtype.forall`. This one is useful if Lean cannot figure out `q`
  when using `subtype.forall` from right to left. -/
protected theorem forall' {q : ∀ x, p x → Prop} :
  (∀ x h, q x h) ↔ (∀ x : {a // p a}, q x x.2) :=
(@subtype.forall _ _ (λ x, q x.1 x.2)).symm

@[simp] protected theorem «exists» {q : {a // p a} → Prop} :
  (∃ x, q x) ↔ (∃ a b, q ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

/-- An alternative version of `subtype.exists`. This one is useful if Lean cannot figure out `q`
  when using `subtype.exists` from right to left. -/
protected theorem exists' {q : ∀x, p x → Prop} :
  (∃ x h, q x h) ↔ (∃ x : {a // p a}, q x x.2) :=
(@subtype.exists _ _ (λ x, q x.1 x.2)).symm

@[ext] protected lemma ext : ∀ {a1 a2 : {x // p x}}, (a1 : α) = (a2 : α) → a1 = a2
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

lemma ext_iff {a1 a2 : {x // p x}} : a1 = a2 ↔ (a1 : α) = (a2 : α) :=
⟨congr_arg _, subtype.ext⟩

lemma heq_iff_coe_eq (h : ∀ x, p x ↔ q x) {a1 : {x // p x}} {a2 : {x // q x}} :
  a1 == a2 ↔ (a1 : α) = (a2 : α) :=
eq.rec (λ a2', heq_iff_eq.trans ext_iff) (funext $ λ x, propext (h x)) a2

lemma heq_iff_coe_heq {α β : Sort*} {p : α → Prop} {q : β → Prop} {a : {x // p x}}
  {b : {y // q y}} (h : α = β) (h' : p == q) :
  a == b ↔ (a : α) == (b : β) :=
by { subst h, subst h', rw [heq_iff_eq, heq_iff_eq, ext_iff] }

lemma ext_val {a1 a2 : {x // p x}} : a1.1 = a2.1 → a1 = a2 :=
subtype.ext

lemma ext_iff_val {a1 a2 : {x // p x}} : a1 = a2 ↔ a1.1 = a2.1 :=
ext_iff

@[simp] theorem coe_eta (a : {a // p a}) (h : p a) : mk ↑a h = a := subtype.ext rfl

@[simp] theorem coe_mk (a h) : (@mk α p a h : α) = a := rfl

@[simp, nolint simp_nf] -- built-in reduction doesn't always work
theorem mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' :=
ext_iff

theorem coe_eq_iff {a : {a // p a}} {b : α} : ↑a = b ↔ ∃ h, a = ⟨b, h⟩ :=
⟨λ h, h ▸ ⟨a.2, (coe_eta _ _).symm⟩, λ ⟨hb, ha⟩, ha.symm ▸ rfl⟩

theorem coe_injective : injective (coe : subtype p → α) :=
λ a b, subtype.ext

theorem val_injective : injective (@val _ p) :=
coe_injective

@[simp] lemma _root_.exists_subtype_mk_eq_iff {p : α → Prop} {a : subtype p} {b : α} :
  (∃ h : p b, subtype.mk b h = a) ↔ b = a :=
begin
  refine ⟨λ ⟨h, ha⟩, congr_arg subtype.val ha, λ h, _⟩,
  rw h,
  exact ⟨a.2, subtype.coe_eta _ _⟩,
end

@[simp] lemma _root_.exists_eq_subtype_mk_iff {p : α → Prop} {a : subtype p} {b : α} :
  (∃ h : p b, a = subtype.mk b h) ↔ ↑a = b :=
by simp only [@eq_comm _ a, exists_subtype_mk_eq_iff, @eq_comm _ _ b]

/-- Restrict a (dependent) function to a subtype -/
def restrict {α} {β : α → Type*} (f : Π x, β x) (p : α → Prop) (x : subtype p) : β x.1 :=
f x

lemma restrict_apply {α} {β : α → Type*} (f : Π x, β x) (p : α → Prop) (x : subtype p) :
  restrict f p x = f x.1 :=
by refl

lemma restrict_def {α β} (f : α → β) (p : α → Prop) : restrict f p = f ∘ coe :=
by refl

lemma restrict_injective {α β} {f : α → β} (p : α → Prop) (h : injective f) :
  injective (restrict f p) :=
h.comp coe_injective

lemma surjective_restrict {α} {β : α → Type*} [ne : Π a, nonempty (β a)] (p : α → Prop) :
  surjective (λ f : Π x, β x, restrict f p) :=
begin
  letI := classical.dec_pred p,
  refine λ f, ⟨λ x, if h : p x then f ⟨x, h⟩ else nonempty.some (ne x), funext $ _⟩,
  rintro ⟨x, hx⟩,
  exact dif_pos hx
end

/-- Defining a map into a subtype, this can be seen as an "coinduction principle" of `subtype`-/
@[simps] def coind {α β} (f : α → β) {p : β → Prop} (h : ∀ a, p (f a)) : α → subtype p :=
λ a, ⟨f a, h a⟩

theorem coind_injective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a))
  (hf : injective f) : injective (coind f h) :=
λ x y hxy, hf $ by apply congr_arg subtype.val hxy

theorem coind_surjective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a))
  (hf : surjective f) : surjective (coind f h) :=
λ x, let ⟨a, ha⟩ := hf x in ⟨a, coe_injective ha⟩

theorem coind_bijective {α β} {f : α → β} {p : β → Prop} (h : ∀ a, p (f a))
  (hf : bijective f) : bijective (coind f h) :=
⟨coind_injective h hf.1, coind_surjective h hf.2⟩

/-- Restriction of a function to a function on subtypes. -/
@[simps] def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ a, p a → q (f a)) :
  subtype p → subtype q :=
λ x, ⟨f x, h x x.prop⟩

theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀ a, p a → q (f a)) (g : β → γ) (l : ∀ a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
rfl

theorem map_id {p : α → Prop} {h : ∀ a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

lemma map_injective {p : α → Prop} {q : β → Prop} {f : α → β} (h : ∀ a, p a → q (f a))
  (hf : injective f) : injective (map f h) :=
coind_injective _ $ hf.comp coe_injective

lemma map_involutive {p : α → Prop} {f : α → α} (h : ∀ a, p a → p (f a))
  (hf : involutive f) : involutive (map f h) :=
λ x, subtype.ext (hf x)

instance [has_equiv α] (p : α → Prop) : has_equiv (subtype p) :=
⟨λ s t, (s : α) ≈ (t : α)⟩

theorem equiv_iff [has_equiv α] {p : α → Prop} {s t : subtype p} :
  s ≈ t ↔ (s : α) ≈ (t : α) :=
iff.rfl

variables [setoid α]

protected theorem refl (s : subtype p) : s ≈ s :=
setoid.refl ↑s

protected theorem symm {s t : subtype p} (h : s ≈ t) : t ≈ s :=
setoid.symm h

protected theorem trans {s t u : subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
setoid.trans h₁ h₂

theorem equivalence (p : α → Prop) : equivalence (@has_equiv.equiv (subtype p) _) :=
mk_equivalence _ subtype.refl (@subtype.symm _ p _) (@subtype.trans _ p _)

instance (p : α → Prop) : setoid (subtype p) :=
setoid.mk (≈) (equivalence p)

end subtype

namespace subtype
/-! Some facts about sets, which require that `α` is a type. -/
variables {α β γ : Type*} {p : α → Prop}

@[simp] lemma coe_prop {S : set α} (a : {a // a ∈ S}) : ↑a ∈ S := a.prop

lemma val_prop {S : set α} (a : {a // a ∈ S}) : a.val ∈ S := a.property

end subtype
