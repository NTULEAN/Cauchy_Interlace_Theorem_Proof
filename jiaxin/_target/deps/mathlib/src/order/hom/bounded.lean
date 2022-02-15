/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.hom.basic
import order.bounded_order

/-!
# Bounded order homomorphisms

This file defines (bounded) order homomorphisms.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `top_hom`: Maps which preserve `⊤`.
* `bot_hom`: Maps which preserve `⊥`.
* `bounded_order_hom`: Bounded order homomorphisms. Monotone maps which preserve `⊤` and `⊥`.

## Typeclasses

* `top_hom_class`
* `bot_hom_class`
* `bounded_order_hom_class`
-/

open function order_dual

variables {F α β γ δ : Type*}

/-- The type of `⊤`-preserving functions from `α` to `β`. -/
structure top_hom (α β : Type*) [has_top α] [has_top β] :=
(to_fun   : α → β)
(map_top' : to_fun ⊤ = ⊤)

/-- The type of `⊥`-preserving functions from `α` to `β`. -/
structure bot_hom (α β : Type*) [has_bot α] [has_bot β] :=
(to_fun   : α → β)
(map_bot' : to_fun ⊥ = ⊥)

/-- The type of bounded order homomorphisms from `α` to `β`. -/
structure bounded_order_hom (α β : Type*) [preorder α] [preorder β] [bounded_order α]
  [bounded_order β]
  extends order_hom α β :=
(map_top' : to_fun ⊤ = ⊤)
(map_bot' : to_fun ⊥ = ⊥)

/-- `top_hom_class F α β` states that `F` is a type of `⊤`-preserving morphisms.

You should extend this class when you extend `top_hom`. -/
class top_hom_class (F : Type*) (α β : out_param $ Type*) [has_top α] [has_top β]
  extends fun_like F α (λ _, β) :=
(map_top (f : F) : f ⊤ = ⊤)

/-- `bot_hom_class F α β` states that `F` is a type of `⊥`-preserving morphisms.

You should extend this class when you extend `bot_hom`. -/
class bot_hom_class (F : Type*) (α β : out_param $ Type*) [has_bot α] [has_bot β]
  extends fun_like F α (λ _, β) :=
(map_bot (f : F) : f ⊥ = ⊥)

/-- `bounded_order_hom_class F α β` states that `F` is a type of bounded order morphisms.

You should extend this class when you extend `bounded_order_hom`. -/
class bounded_order_hom_class (F : Type*) (α β : out_param $ Type*) [preorder α] [preorder β]
  [bounded_order α] [bounded_order β]
  extends rel_hom_class F ((≤) : α → α → Prop) ((≤) : β → β → Prop) :=
(map_top (f : F) : f ⊤ = ⊤)
(map_bot (f : F) : f ⊥ = ⊥)

export top_hom_class (map_top) bot_hom_class (map_bot)

attribute [simp] map_top map_bot

@[priority 100] -- See note [lower instance priority]
instance bounded_order_hom_class.to_top_hom_class [preorder α] [preorder β]
  [bounded_order α] [bounded_order β] [bounded_order_hom_class F α β] :
  top_hom_class F α β :=
{ .. ‹bounded_order_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance bounded_order_hom_class.to_bot_hom_class [preorder α] [preorder β]
  [bounded_order α] [bounded_order β] [bounded_order_hom_class F α β] :
  bot_hom_class F α β :=
{ .. ‹bounded_order_hom_class F α β› }

@[priority 100] -- See note [lower instance priority]
instance order_iso.top_hom_class [partial_order α] [partial_order β] [order_top α] [order_top β] :
  top_hom_class (α ≃o β) α β :=
{ map_top := λ f, f.map_top, ..rel_iso.rel_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso.bot_hom_class [partial_order α] [partial_order β] [order_bot α] [order_bot β] :
  bot_hom_class (α ≃o β) α β :=
{ map_bot := λ f, f.map_bot, ..rel_iso.rel_hom_class }

@[priority 100] -- See note [lower instance priority]
instance order_iso.bounded_order_hom_class [partial_order α] [partial_order β]
  [bounded_order α] [bounded_order β] :
  bounded_order_hom_class (α ≃o β) α β :=
{ ..order_iso.top_hom_class, ..order_iso.bot_hom_class }

instance [has_top α] [has_top β] [top_hom_class F α β] : has_coe_t F (top_hom α β) :=
⟨λ f, ⟨f, map_top f⟩⟩

instance [has_bot α] [has_bot β] [bot_hom_class F α β] : has_coe_t F (bot_hom α β) :=
⟨λ f, ⟨f, map_bot f⟩⟩

instance [preorder α] [preorder β] [bounded_order α] [bounded_order β]
  [bounded_order_hom_class F α β] : has_coe_t F (bounded_order_hom α β) :=
⟨λ f, { to_fun := f, map_top' := map_top f, map_bot' := map_bot f, ..(f : α →o β) }⟩

/-! ### Top homomorphisms -/

namespace top_hom
variables [has_top α]

section has_top
variables [has_top β] [has_top γ] [has_top δ]

instance : top_hom_class (top_hom α β) α β :=
{ coe := top_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_top := top_hom.map_top' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (top_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : top_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : top_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `top_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : top_hom α β) (f' : α → β) (h : f' = f) : top_hom α β :=
{ to_fun := f',
  map_top' := h.symm ▸ f.map_top' }

instance : inhabited (top_hom α β) := ⟨⟨λ _, ⊤, rfl⟩⟩

variables (α)

/-- `id` as a `top_hom`. -/
protected def id : top_hom α α := ⟨id, rfl⟩

@[simp] lemma coe_id : ⇑(top_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : top_hom.id α a = a := rfl

/-- Composition of `top_hom`s as a `top_hom`. -/
def comp (f : top_hom β γ) (g : top_hom α β) : top_hom α γ :=
{ to_fun := f ∘ g,
  map_top' := by rw [comp_apply, map_top, map_top] }

@[simp] lemma coe_comp (f : top_hom β γ) (g : top_hom α β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : top_hom β γ) (g : top_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : top_hom γ δ) (g : top_hom β γ) (h : top_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : top_hom α β) : f.comp (top_hom.id α) = f := top_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : top_hom α β) : (top_hom.id β).comp f = f := top_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : top_hom β γ} {f : top_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, top_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : top_hom β γ} {f₁ f₂ : top_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, top_hom.ext $ λ a, hg $
  by rw [←top_hom.comp_apply, h, top_hom.comp_apply], congr_arg _⟩

end has_top

instance [preorder β] [has_top β] : preorder (top_hom α β) :=
preorder.lift (coe_fn : top_hom α β → α → β)

instance [partial_order β] [has_top β] : partial_order (top_hom α β) :=
partial_order.lift _ fun_like.coe_injective

section order_top
variables [preorder β] [order_top β]

instance : order_top (top_hom α β) := ⟨⟨⊤, rfl⟩, λ _, le_top⟩

@[simp] lemma coe_top : ⇑(⊤ : top_hom α β) = ⊤ := rfl
@[simp] lemma top_apply (a : α) : (⊤ : top_hom α β) a = ⊤ := rfl

end order_top

section semilattice_inf
variables [semilattice_inf β] [order_top β] (f g : top_hom α β)

instance : has_inf (top_hom α β) :=
⟨λ f g, ⟨f ⊓ g, by rw [pi.inf_apply, map_top, map_top, inf_top_eq]⟩⟩

instance : semilattice_inf (top_hom α β) := fun_like.coe_injective.semilattice_inf _ $ λ _ _, rfl

@[simp] lemma coe_inf : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

end semilattice_inf

section semilattice_sup
variables [semilattice_sup β] [order_top β] (f g : top_hom α β)

instance : has_sup (top_hom α β) :=
⟨λ f g, ⟨f ⊔ g, by rw [pi.sup_apply, map_top, map_top, sup_top_eq]⟩⟩

instance : semilattice_sup (top_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma coe_sup : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

end semilattice_sup

instance [lattice β] [order_top β] : lattice (top_hom α β) :=
fun_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance [distrib_lattice β] [order_top β] : distrib_lattice (top_hom α β) :=
fun_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

end top_hom

/-! ### Bot homomorphisms -/

namespace bot_hom
variables [has_bot α]

section has_bot
variables [has_bot β] [has_bot γ] [has_bot δ]

instance : bot_hom_class (bot_hom α β) α β :=
{ coe := bot_hom.to_fun,
  coe_injective' := λ f g h, by cases f; cases g; congr',
  map_bot := bot_hom.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (bot_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : bot_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bot_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bot_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : bot_hom α β) (f' : α → β) (h : f' = f) : bot_hom α β :=
{ to_fun := f',
  map_bot' := h.symm ▸ f.map_bot' }

instance : inhabited (bot_hom α β) := ⟨⟨λ _, ⊥, rfl⟩⟩

variables (α)

/-- `id` as a `bot_hom`. -/
protected def id : bot_hom α α := ⟨id, rfl⟩

@[simp] lemma coe_id : ⇑(bot_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bot_hom.id α a = a := rfl

/-- Composition of `bot_hom`s as a `bot_hom`. -/
def comp (f : bot_hom β γ) (g : bot_hom α β) : bot_hom α γ :=
{ to_fun := f ∘ g,
  map_bot' := by rw [comp_apply, map_bot, map_bot] }

@[simp] lemma coe_comp (f : bot_hom β γ) (g : bot_hom α β) : (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : bot_hom β γ) (g : bot_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma comp_assoc (f : bot_hom γ δ) (g : bot_hom β γ) (h : bot_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : bot_hom α β) : f.comp (bot_hom.id α) = f := bot_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : bot_hom α β) : (bot_hom.id β).comp f = f := bot_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : bot_hom β γ} {f : bot_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, bot_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : bot_hom β γ} {f₁ f₂ : bot_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, bot_hom.ext $ λ a, hg $
  by rw [←bot_hom.comp_apply, h, bot_hom.comp_apply], congr_arg _⟩

end has_bot

instance [preorder β] [has_bot β] : preorder (bot_hom α β) :=
preorder.lift (coe_fn : bot_hom α β → α → β)

instance [partial_order β] [has_bot β] : partial_order (bot_hom α β) :=
partial_order.lift _ fun_like.coe_injective

section order_bot
variables [preorder β] [order_bot β]

instance : order_bot (bot_hom α β) := ⟨⟨⊥, rfl⟩, λ _, bot_le⟩

@[simp] lemma coe_bot : ⇑(⊥ : bot_hom α β) = ⊥ := rfl
@[simp] lemma bot_apply (a : α) : (⊥ : bot_hom α β) a = ⊥ := rfl

end order_bot

section semilattice_inf
variables [semilattice_inf β] [order_bot β] (f g : bot_hom α β)

instance : has_inf (bot_hom α β) :=
⟨λ f g, ⟨f ⊓ g, by rw [pi.inf_apply, map_bot, map_bot, inf_bot_eq]⟩⟩

instance : semilattice_inf (bot_hom α β) := fun_like.coe_injective.semilattice_inf _ $ λ _ _, rfl

@[simp] lemma coe_inf : ⇑(f ⊓ g) = f ⊓ g := rfl
@[simp] lemma inf_apply (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

end semilattice_inf

section semilattice_sup
variables [semilattice_sup β] [order_bot β] (f g : bot_hom α β)

instance : has_sup (bot_hom α β) :=
⟨λ f g, ⟨f ⊔ g, by rw [pi.sup_apply, map_bot, map_bot, sup_bot_eq]⟩⟩

instance : semilattice_sup (bot_hom α β) := fun_like.coe_injective.semilattice_sup _ $ λ _ _, rfl

@[simp] lemma coe_sup : ⇑(f ⊔ g) = f ⊔ g := rfl
@[simp] lemma sup_apply (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl

end semilattice_sup

instance [lattice β] [order_bot β] : lattice (bot_hom α β) :=
fun_like.coe_injective.lattice _ (λ _ _, rfl) (λ _ _, rfl)

instance [distrib_lattice β] [order_bot β] : distrib_lattice (bot_hom α β) :=
fun_like.coe_injective.distrib_lattice _ (λ _ _, rfl) (λ _ _, rfl)

end bot_hom

/-! ### Bounded order homomorphisms -/

namespace bounded_order_hom
variables [preorder α] [preorder β] [preorder γ] [preorder δ] [bounded_order α] [bounded_order β]
  [bounded_order γ] [bounded_order δ]

/-- Reinterpret a `bounded_order_hom` as a `top_hom`. -/
def to_top_hom (f : bounded_order_hom α β) : top_hom α β := { ..f }

/-- Reinterpret a `bounded_order_hom` as a `bot_hom`. -/
def to_bot_hom (f : bounded_order_hom α β) : bot_hom α β := { ..f }

instance : bounded_order_hom_class (bounded_order_hom α β) α β :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr',
  map_rel := λ f, f.monotone',
  map_top := λ f, f.map_top',
  map_bot := λ f, f.map_bot' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (bounded_order_hom α β) (λ _, α → β) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe {f : bounded_order_hom α β} : f.to_fun = (f : α → β) := rfl

@[ext] lemma ext {f g : bounded_order_hom α β} (h : ∀ a, f a = g a) : f = g := fun_like.ext f g h

/-- Copy of a `bounded_order_hom` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : bounded_order_hom α β) (f' : α → β) (h : f' = f) : bounded_order_hom α β :=
{ .. f.to_order_hom.copy f' h, .. f.to_top_hom.copy f' h, .. f.to_bot_hom.copy f' h }

variables (α)

/-- `id` as a `bounded_order_hom`. -/
protected def id : bounded_order_hom α α := { ..order_hom.id, ..top_hom.id α, ..bot_hom.id α }

instance : inhabited (bounded_order_hom α α) := ⟨bounded_order_hom.id α⟩

@[simp] lemma coe_id : ⇑(bounded_order_hom.id α) = id := rfl

variables {α}

@[simp] lemma id_apply (a : α) : bounded_order_hom.id α a = a := rfl

/-- Composition of `bounded_order_hom`s as a `bounded_order_hom`. -/
def comp (f : bounded_order_hom β γ) (g : bounded_order_hom α β) : bounded_order_hom α γ :=
{ ..f.to_order_hom.comp g.to_order_hom,
  ..f.to_top_hom.comp g.to_top_hom, ..f.to_bot_hom.comp g.to_bot_hom }

@[simp] lemma coe_comp (f : bounded_order_hom β γ) (g : bounded_order_hom α β) :
  (f.comp g : α → γ) = f ∘ g := rfl
@[simp] lemma comp_apply (f : bounded_order_hom β γ) (g : bounded_order_hom α β) (a : α) :
  (f.comp g) a = f (g a) := rfl
@[simp] lemma coe_comp_order_hom (f : bounded_order_hom β γ) (g : bounded_order_hom α β) :
  (f.comp g : order_hom α γ) = (f : order_hom β γ).comp g := rfl
@[simp] lemma coe_comp_top_hom (f : bounded_order_hom β γ) (g : bounded_order_hom α β) :
  (f.comp g : top_hom α γ) = (f : top_hom β γ).comp g := rfl
@[simp] lemma coe_comp_bot_hom (f : bounded_order_hom β γ) (g : bounded_order_hom α β) :
  (f.comp g : bot_hom α γ) = (f : bot_hom β γ).comp g := rfl
@[simp] lemma comp_assoc (f : bounded_order_hom γ δ) (g : bounded_order_hom β γ)
  (h : bounded_order_hom α β) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
@[simp] lemma comp_id (f : bounded_order_hom α β) : f.comp (bounded_order_hom.id α) = f :=
bounded_order_hom.ext $ λ a, rfl
@[simp] lemma id_comp (f : bounded_order_hom α β) : (bounded_order_hom.id β).comp f = f :=
bounded_order_hom.ext $ λ a, rfl

lemma cancel_right {g₁ g₂ : bounded_order_hom β γ} {f : bounded_order_hom α β} (hf : surjective f) :
  g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨λ h, bounded_order_hom.ext $ hf.forall.2 $ fun_like.ext_iff.1 h, congr_arg _⟩

lemma cancel_left {g : bounded_order_hom β γ} {f₁ f₂ : bounded_order_hom α β} (hg : injective g) :
  g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨λ h, bounded_order_hom.ext $ λ a, hg $
  by rw [←bounded_order_hom.comp_apply, h, bounded_order_hom.comp_apply], congr_arg _⟩

/-- Reinterpret a bounded order homomorphism as a bounded order homomorphism between the dual
orders. -/
@[simps] protected def dual :
   bounded_order_hom α β ≃ bounded_order_hom (order_dual α) (order_dual β) :=
{ to_fun := λ f, { to_order_hom := f.to_order_hom.dual,
                   map_top' := congr_arg to_dual (map_bot f),
                   map_bot' := congr_arg to_dual (map_top f) },
  inv_fun := λ f, { to_order_hom := order_hom.dual.symm f.to_order_hom,
                    map_top' := map_bot f,
                    map_bot' := map_top f },
  left_inv := λ f, ext $ λ a, rfl,
  right_inv := λ f, ext $ λ a, rfl }

end bounded_order_hom
