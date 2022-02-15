/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.fun_like.equiv
import data.option.basic
import data.prod
import data.quot
import data.sigma.basic
import data.sum.basic
import data.subtype
import logic.function.conjugate
import logic.unique
import tactic.norm_cast
import tactic.simps

/-!
# Equivalence between types

In this file we define two types:

* `equiv α β` a.k.a. `α ≃ β`: a bijective map `α → β` bundled with its inverse map; we use this (and
  not equality!) to express that various `Type`s or `Sort`s are equivalent.

* `equiv.perm α`: the group of permutations `α ≃ α`. More lemmas about `equiv.perm` can be found in
  `group_theory/perm`.

Then we define

* canonical isomorphisms between various types: e.g.,

  - `equiv.refl α` is the identity map interpreted as `α ≃ α`;

  - `equiv.sum_equiv_sigma_bool` is the canonical equivalence between the sum of two types `α ⊕ β`
    and the sigma-type `Σ b : bool, cond b α β`;

  - `equiv.prod_sum_distrib : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ)` shows that type product and type sum
    satisfy the distributive law up to a canonical equivalence;

* operations on equivalences: e.g.,

  - `equiv.symm e : β ≃ α` is the inverse of `e : α ≃ β`;

  - `equiv.trans e₁ e₂ : α ≃ γ` is the composition of `e₁ : α ≃ β` and `e₂ : β ≃ γ` (note the order
    of the arguments!);

  - `equiv.prod_congr ea eb : α₁ × β₁ ≃ α₂ × β₂`: combine two equivalences `ea : α₁ ≃ α₂` and
    `eb : β₁ ≃ β₂` using `prod.map`.

* definitions that transfer some instances along an equivalence. By convention, we transfer
  instances from right to left.

  - `equiv.inhabited` takes `e : α ≃ β` and `[inhabited β]` and returns `inhabited α`;
  - `equiv.unique` takes `e : α ≃ β` and `[unique β]` and returns `unique α`;
  - `equiv.decidable_eq` takes `e : α ≃ β` and `[decidable_eq β]` and returns `decidable_eq α`.

  More definitions of this kind can be found in other files. E.g., `data/equiv/transfer_instance`
  does it for many algebraic type classes like `group`, `module`, etc.

## Tags

equivalence, congruence, bijective map
-/

open function

universes u v w z
variables {α : Sort u} {β : Sort v} {γ : Sort w}

/-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
@[nolint has_inhabited_instance]
structure equiv (α : Sort*) (β : Sort*) :=
(to_fun    : α → β)
(inv_fun   : β → α)
(left_inv  : left_inverse inv_fun to_fun)
(right_inv : right_inverse inv_fun to_fun)

infix ` ≃ `:25 := equiv

/-- Convert an involutive function `f` to an equivalence with `to_fun = inv_fun = f`. -/
def function.involutive.to_equiv (f : α → α) (h : involutive f) : α ≃ α :=
⟨f, f, h.left_inverse, h.right_inverse⟩

namespace equiv

/-- `perm α` is the type of bijections from `α` to itself. -/
@[reducible] def perm (α : Sort*) := equiv α α

instance : equiv_like (α ≃ β) α β :=
{ coe := to_fun, inv := inv_fun, left_inv := left_inv, right_inv := right_inv,
  coe_injective' := λ e₁ e₂ h₁ h₂, by { cases e₁, cases e₂, congr' } }

instance : has_coe_to_fun (α ≃ β) (λ _, α → β) := ⟨to_fun⟩

@[simp] theorem coe_fn_mk (f : α → β) (g l r) : (equiv.mk f g l r : α → β) = f :=
rfl

/-- The map `coe_fn : (r ≃ s) → (r → s)` is injective. -/
theorem coe_fn_injective : @function.injective (α ≃ β) (α → β) coe_fn := fun_like.coe_injective
protected lemma coe_inj {e₁ e₂ : α ≃ β} : (e₁ : α → β) = e₂ ↔ e₁ = e₂ := fun_like.coe_fn_eq
@[ext] lemma ext {f g : equiv α β} (H : ∀ x, f x = g x) : f = g := fun_like.ext f g H
protected lemma congr_arg {f : equiv α β} {x x' : α} : x = x' → f x = f x' := fun_like.congr_arg f
protected lemma congr_fun {f g : equiv α β} (h : f = g) (x : α) : f x = g x :=
fun_like.congr_fun h x
lemma ext_iff {f g : equiv α β} : f = g ↔ ∀ x, f x = g x := fun_like.ext_iff

@[ext] lemma perm.ext {σ τ : equiv.perm α} (H : ∀ x, σ x = τ x) : σ = τ :=
equiv.ext H

protected lemma perm.congr_arg {f : equiv.perm α} {x x' : α} : x = x' → f x = f x' :=
equiv.congr_arg

protected lemma perm.congr_fun {f g : equiv.perm α} (h : f = g) (x : α) : f x = g x :=
equiv.congr_fun h x

lemma perm.ext_iff {σ τ : equiv.perm α} : σ = τ ↔ ∀ x, σ x = τ x :=
ext_iff

/-- Any type is equivalent to itself. -/
@[refl] protected def refl (α : Sort*) : α ≃ α := ⟨id, id, λ x, rfl, λ x, rfl⟩

instance inhabited' : inhabited (α ≃ α) := ⟨equiv.refl α⟩

/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm] protected def symm (e : α ≃ β) : β ≃ α := ⟨e.inv_fun, e.to_fun, e.right_inv, e.left_inv⟩

/-- See Note [custom simps projection] -/
def simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections equiv (to_fun → apply, inv_fun → symm_apply)

-- Generate the `simps` projections for previously defined equivs.
attribute [simps] function.involutive.to_equiv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[trans] protected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm,
  e₂.left_inv.comp e₁.left_inv, e₂.right_inv.comp e₁.right_inv⟩

@[simp]
lemma to_fun_as_coe (e : α ≃ β) : e.to_fun = e := rfl

@[simp]
lemma inv_fun_as_coe (e : α ≃ β) : e.inv_fun = e.symm := rfl

protected theorem injective (e : α ≃ β) : injective e := equiv_like.injective e
protected theorem surjective (e : α ≃ β) : surjective e := equiv_like.surjective e
protected theorem bijective (e : α ≃ β) : bijective e := equiv_like.bijective e

protected theorem subsingleton (e : α ≃ β) [subsingleton β] : subsingleton α :=
e.injective.subsingleton

protected theorem subsingleton.symm (e : α ≃ β) [subsingleton α] : subsingleton β :=
e.symm.injective.subsingleton

lemma subsingleton_congr (e : α ≃ β) : subsingleton α ↔ subsingleton β :=
⟨λ h, by exactI e.symm.subsingleton, λ h, by exactI e.subsingleton⟩

instance equiv_subsingleton_cod [subsingleton β] :
  subsingleton (α ≃ β) :=
⟨λ f g, equiv.ext $ λ x, subsingleton.elim _ _⟩

instance equiv_subsingleton_dom [subsingleton α] :
  subsingleton (α ≃ β) :=
⟨λ f g, equiv.ext $ λ x, @subsingleton.elim _ (equiv.subsingleton.symm f) _ _⟩

instance perm_unique [subsingleton α] : unique (perm α) :=
unique_of_subsingleton (equiv.refl α)

lemma perm.subsingleton_eq_refl [subsingleton α] (e : perm α) :
  e = equiv.refl α := subsingleton.elim _ _

/-- Transfer `decidable_eq` across an equivalence. -/
protected def decidable_eq (e : α ≃ β) [decidable_eq β] : decidable_eq α :=
e.injective.decidable_eq

lemma nonempty_congr (e : α ≃ β) : nonempty α ↔ nonempty β :=
nonempty.congr e e.symm

protected lemma nonempty (e : α ≃ β) [nonempty β] : nonempty α :=
e.nonempty_congr.mpr ‹_›

/-- If `α ≃ β` and `β` is inhabited, then so is `α`. -/
protected def inhabited [inhabited β] (e : α ≃ β) : inhabited α :=
⟨e.symm default⟩

/-- If `α ≃ β` and `β` is a singleton type, then so is `α`. -/
protected def unique [unique β] (e : α ≃ β) : unique α :=
e.symm.surjective.unique

/-- Equivalence between equal types. -/
protected def cast {α β : Sort*} (h : α = β) : α ≃ β :=
⟨cast h, cast h.symm, λ x, by { cases h, refl }, λ x, by { cases h, refl }⟩

@[simp] theorem coe_fn_symm_mk (f : α → β) (g l r) : ((equiv.mk f g l r).symm : β → α) = g :=
rfl

@[simp] theorem coe_refl : ⇑(equiv.refl α) = id := rfl

@[simp] theorem perm.coe_subsingleton {α : Type*} [subsingleton α] (e : perm α) : ⇑(e) = id :=
by rw [perm.subsingleton_eq_refl e, coe_refl]

theorem refl_apply (x : α) : equiv.refl α x = x := rfl

@[simp] theorem coe_trans (f : α ≃ β) (g : β ≃ γ) : ⇑(f.trans g) = g ∘ f := rfl

theorem trans_apply (f : α ≃ β) (g : β ≃ γ) (a : α) : (f.trans g) a = g (f a) := rfl

@[simp] theorem apply_symm_apply  (e : α ≃ β) (x : β) : e (e.symm x) = x :=
e.right_inv x

@[simp] theorem symm_apply_apply (e : α ≃ β) (x : α) : e.symm (e x) = x :=
e.left_inv x

@[simp] theorem symm_comp_self (e : α ≃ β) : e.symm ∘ e = id := funext e.symm_apply_apply

@[simp] theorem self_comp_symm (e : α ≃ β) : e ∘ e.symm = id := funext e.apply_symm_apply

@[simp] lemma symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ) :
  (f.trans g).symm a = f.symm (g.symm a) := rfl

-- The `simp` attribute is needed to make this a `dsimp` lemma.
-- `simp` will always rewrite with `equiv.symm_symm` before this has a chance to fire.
@[simp, nolint simp_nf] theorem symm_symm_apply (f : α ≃ β) (b : α) : f.symm.symm b = f b := rfl

theorem apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y ↔ x = y := equiv_like.apply_eq_iff_eq f

theorem apply_eq_iff_eq_symm_apply {α β : Sort*} (f : α ≃ β) {x : α} {y : β} :
  f x = y ↔ x = f.symm y :=
begin
  conv_lhs { rw ←apply_symm_apply f y, },
  rw apply_eq_iff_eq,
end

@[simp] theorem cast_apply {α β} (h : α = β) (x : α) : equiv.cast h x = cast h x := rfl

@[simp] theorem cast_symm {α β} (h : α = β) : (equiv.cast h).symm = equiv.cast h.symm := rfl

@[simp] theorem cast_refl {α} (h : α = α := rfl) : equiv.cast h = equiv.refl α := rfl

@[simp] theorem cast_trans {α β γ} (h : α = β) (h2 : β = γ) :
  (equiv.cast h).trans (equiv.cast h2) = equiv.cast (h.trans h2) :=
ext $ λ x, by { substs h h2, refl }

lemma cast_eq_iff_heq {α β} (h : α = β) {a : α} {b : β} : equiv.cast h a = b ↔ a == b :=
by { subst h, simp }

lemma symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = y ↔ x = e y :=
⟨λ H, by simp [H.symm], λ H, by simp [H]⟩

lemma eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm x ↔ e y = x :=
(eq_comm.trans e.symm_apply_eq).trans eq_comm

@[simp] theorem symm_symm (e : α ≃ β) : e.symm.symm = e := by { cases e, refl }

@[simp] theorem trans_refl (e : α ≃ β) : e.trans (equiv.refl β) = e := by { cases e, refl }

@[simp] theorem refl_symm : (equiv.refl α).symm = equiv.refl α := rfl

@[simp] theorem refl_trans (e : α ≃ β) : (equiv.refl α).trans e = e := by { cases e, refl }

@[simp] theorem symm_trans_self (e : α ≃ β) : e.symm.trans e = equiv.refl β := ext (by simp)

@[simp] theorem self_trans_symm (e : α ≃ β) : e.trans e.symm = equiv.refl α := ext (by simp)

lemma trans_assoc {δ} (ab : α ≃ β) (bc : β ≃ γ) (cd : γ ≃ δ) :
  (ab.trans bc).trans cd = ab.trans (bc.trans cd) :=
equiv.ext $ assume a, rfl

theorem left_inverse_symm (f : equiv α β) : left_inverse f.symm f := f.left_inv

theorem right_inverse_symm (f : equiv α β) : function.right_inverse f.symm f := f.right_inv

lemma injective_comp (e : α ≃ β) (f : β → γ) : injective (f ∘ e) ↔ injective f :=
equiv_like.injective_comp e f

lemma comp_injective (f : α → β) (e : β ≃ γ) : injective (e ∘ f) ↔ injective f :=
equiv_like.comp_injective f e

lemma surjective_comp (e : α ≃ β) (f : β → γ) : surjective (f ∘ e) ↔ surjective f :=
equiv_like.surjective_comp e f

lemma comp_surjective (f : α → β) (e : β ≃ γ) : surjective (e ∘ f) ↔ surjective f :=
equiv_like.comp_surjective f e

lemma bijective_comp (e : α ≃ β) (f : β → γ) : bijective (f ∘ e) ↔ bijective f :=
equiv_like.bijective_comp e f

lemma comp_bijective (f : α → β) (e : β ≃ γ) : bijective (e ∘ f) ↔ bijective f :=
equiv_like.comp_bijective f e

/-- If `α` is equivalent to `β` and `γ` is equivalent to `δ`, then the type of equivalences `α ≃ γ`
is equivalent to the type of equivalences `β ≃ δ`. -/
def equiv_congr {δ} (ab : α ≃ β) (cd : γ ≃ δ) : (α ≃ γ) ≃ (β ≃ δ) :=
⟨ λac, (ab.symm.trans ac).trans cd, λbd, ab.trans $ bd.trans $ cd.symm,
  assume ac, by { ext x, simp }, assume ac, by { ext x, simp } ⟩

@[simp] lemma equiv_congr_refl {α β} :
  (equiv.refl α).equiv_congr (equiv.refl β) = equiv.refl (α ≃ β) := by { ext, refl }

@[simp] lemma equiv_congr_symm {δ} (ab : α ≃ β) (cd : γ ≃ δ) :
  (ab.equiv_congr cd).symm = ab.symm.equiv_congr cd.symm := by { ext, refl }

@[simp] lemma equiv_congr_trans {δ ε ζ} (ab : α ≃ β) (de : δ ≃ ε) (bc : β ≃ γ) (ef : ε ≃ ζ) :
  (ab.equiv_congr de).trans (bc.equiv_congr ef) = (ab.trans bc).equiv_congr (de.trans ef) :=
by { ext, refl }

@[simp] lemma equiv_congr_refl_left {α β γ} (bg : β ≃ γ) (e : α ≃ β) :
  (equiv.refl α).equiv_congr bg e = e.trans bg := rfl

@[simp] lemma equiv_congr_refl_right {α β} (ab e : α ≃ β) :
  ab.equiv_congr (equiv.refl β) e = ab.symm.trans e := rfl

@[simp] lemma equiv_congr_apply_apply {δ} (ab : α ≃ β) (cd : γ ≃ δ) (e : α ≃ γ) (x) :
  ab.equiv_congr cd e x = cd (e (ab.symm x)) := rfl

section perm_congr

variables {α' β' : Type*} (e : α' ≃ β')

/-- If `α` is equivalent to `β`, then `perm α` is equivalent to `perm β`. -/
def perm_congr : perm α' ≃ perm β' :=
equiv_congr e e

lemma perm_congr_def (p : equiv.perm α') :
  e.perm_congr p = (e.symm.trans p).trans e := rfl

@[simp] lemma perm_congr_refl :
  e.perm_congr (equiv.refl _) = equiv.refl _ :=
by simp [perm_congr_def]

@[simp] lemma perm_congr_symm :
  e.perm_congr.symm = e.symm.perm_congr := rfl

@[simp] lemma perm_congr_apply (p : equiv.perm α') (x) :
  e.perm_congr p x = e (p (e.symm x)) := rfl

lemma perm_congr_symm_apply (p : equiv.perm β') (x) :
  e.perm_congr.symm p x = e.symm (p (e x)) := rfl

lemma perm_congr_trans (p p' : equiv.perm α') :
  (e.perm_congr p).trans (e.perm_congr p') = e.perm_congr (p.trans p') :=
by { ext, simp }

end perm_congr

/-- If `α` is an empty type, then it is equivalent to the `empty` type. -/
def equiv_empty (α : Sort u) [is_empty α] : α ≃ empty :=
⟨is_empty_elim, λ e, e.rec _, is_empty_elim, λ e, e.rec _⟩

/-- `α` is equivalent to an empty type iff `α` is empty. -/
def equiv_empty_equiv (α : Sort u) : (α ≃ empty) ≃ is_empty α :=
⟨λ e, function.is_empty e, @equiv_empty α, λ e, ext $ λ x, (e x).elim, λ p, rfl⟩

/-- `false` is equivalent to `empty`. -/
def false_equiv_empty : false ≃ empty :=
equiv_empty _

/-- If `α` is an empty type, then it is equivalent to the `pempty` type in any universe. -/
def {u' v'} equiv_pempty (α : Sort v') [is_empty α] : α ≃ pempty.{u'} :=
⟨is_empty_elim, λ e, e.rec _, is_empty_elim, λ e, e.rec _⟩

/-- `false` is equivalent to `pempty`. -/
def false_equiv_pempty : false ≃ pempty :=
equiv_pempty _

/-- `empty` is equivalent to `pempty`. -/
def empty_equiv_pempty : empty ≃ pempty :=
equiv_pempty _

/-- `pempty` types from any two universes are equivalent. -/
def pempty_equiv_pempty : pempty.{v} ≃ pempty.{w} :=
equiv_pempty _

/-- The `Sort` of proofs of a true proposition is equivalent to `punit`. -/
def prop_equiv_punit {p : Prop} (h : p) : p ≃ punit :=
⟨λ x, (), λ x, h, λ _, rfl, λ ⟨⟩, rfl⟩

/-- The `Sort` of proofs of a false proposition is equivalent to `pempty`. -/
def prop_equiv_pempty {p : Prop} (h : ¬p) : p ≃ pempty :=
⟨λ x, absurd x h, λ x, by cases x, λ x, absurd x h, λ x, by cases x⟩

/-- `true` is equivalent to `punit`. -/
def true_equiv_punit : true ≃ punit := prop_equiv_punit trivial

/-- `ulift α` is equivalent to `α`. -/
@[simps apply symm_apply {fully_applied := ff}]
protected def ulift {α : Type v} : ulift.{u} α ≃ α :=
⟨ulift.down, ulift.up, ulift.up_down, λ a, rfl⟩

/-- `plift α` is equivalent to `α`. -/
@[simps apply symm_apply {fully_applied := ff}]
protected def plift : plift α ≃ α :=
⟨plift.down, plift.up, plift.up_down, plift.down_up⟩

/-- `pprod α β` is equivalent to `α × β` -/
@[simps apply symm_apply]
def pprod_equiv_prod {α β : Type*} : pprod α β ≃ α × β :=
{ to_fun := λ x, (x.1, x.2),
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

/-- equivalence of propositions is the same as iff -/
def of_iff {P Q : Prop} (h : P ↔ Q) : P ≃ Q :=
{ to_fun := h.mp,
  inv_fun := h.mpr,
  left_inv := λ x, rfl,
  right_inv := λ y, rfl }

/-- If `α₁` is equivalent to `α₂` and `β₁` is equivalent to `β₂`, then the type of maps `α₁ → β₁`
is equivalent to the type of maps `α₂ → β₂`. -/
@[congr, simps apply] def arrow_congr {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (α₁ → β₁) ≃ (α₂ → β₂) :=
{ to_fun := λ f, e₂ ∘ f ∘ e₁.symm,
  inv_fun := λ f, e₂.symm ∘ f ∘ e₁,
  left_inv := λ f, funext $ λ x, by simp,
  right_inv := λ f, funext $ λ x, by simp }

lemma arrow_congr_comp {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*}
  (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ → β₁) (g : β₁ → γ₁) :
  arrow_congr ea ec (g ∘ f) = (arrow_congr eb ec g) ∘ (arrow_congr ea eb f) :=
by { ext, simp only [comp, arrow_congr_apply, eb.symm_apply_apply] }

@[simp] lemma arrow_congr_refl {α β : Sort*} :
  arrow_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α → β) := rfl

@[simp] lemma arrow_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*}
  (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  arrow_congr (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr e₁ e₁').trans (arrow_congr e₂ e₂') :=
rfl

@[simp] lemma arrow_congr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (arrow_congr e₁ e₂).symm = arrow_congr e₁.symm e₂.symm :=
rfl

/--
A version of `equiv.arrow_congr` in `Type`, rather than `Sort`.

The `equiv_rw` tactic is not able to use the default `Sort` level `equiv.arrow_congr`,
because Lean's universe rules will not unify `?l_1` with `imax (1 ?m_1)`.
-/
@[congr, simps apply]
def arrow_congr' {α₁ β₁ α₂ β₂ : Type*} (hα : α₁ ≃ α₂) (hβ : β₁ ≃ β₂) : (α₁ → β₁) ≃ (α₂ → β₂) :=
equiv.arrow_congr hα hβ

@[simp] lemma arrow_congr'_refl {α β : Type*} :
  arrow_congr' (equiv.refl α) (equiv.refl β) = equiv.refl (α → β) := rfl

@[simp] lemma arrow_congr'_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Type*}
  (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  arrow_congr' (e₁.trans e₂) (e₁'.trans e₂') = (arrow_congr' e₁ e₁').trans (arrow_congr' e₂ e₂') :=
rfl

@[simp] lemma arrow_congr'_symm {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (arrow_congr' e₁ e₂).symm = arrow_congr' e₁.symm e₂.symm :=
rfl

/-- Conjugate a map `f : α → α` by an equivalence `α ≃ β`. -/
@[simps apply]
def conj (e : α ≃ β) : (α → α) ≃ (β → β) := arrow_congr e e

@[simp] lemma conj_refl : conj (equiv.refl α) = equiv.refl (α → α) := rfl

@[simp] lemma conj_symm (e : α ≃ β) : e.conj.symm = e.symm.conj := rfl

@[simp] lemma conj_trans (e₁ : α ≃ β) (e₂ : β ≃ γ) :
  (e₁.trans e₂).conj = e₁.conj.trans e₂.conj :=
rfl

-- This should not be a simp lemma as long as `(∘)` is reducible:
-- when `(∘)` is reducible, Lean can unify `f₁ ∘ f₂` with any `g` using
-- `f₁ := g` and `f₂ := λ x, x`.  This causes nontermination.
lemma conj_comp (e : α ≃ β) (f₁ f₂ : α → α) :
  e.conj (f₁ ∘ f₂) = (e.conj f₁) ∘ (e.conj f₂) :=
by apply arrow_congr_comp

section binary_op

variables {α₁ β₁ : Type*} (e : α₁ ≃ β₁) (f : α₁ → α₁ → α₁)

lemma semiconj_conj (f : α₁ → α₁) : semiconj e f (e.conj f) := λ x, by simp

lemma semiconj₂_conj : semiconj₂ e f (e.arrow_congr e.conj f) := λ x y, by simp

instance [is_associative α₁ f] :
  is_associative β₁ (e.arrow_congr (e.arrow_congr e) f) :=
(e.semiconj₂_conj f).is_associative_right e.surjective

instance [is_idempotent α₁ f] :
  is_idempotent β₁ (e.arrow_congr (e.arrow_congr e) f) :=
(e.semiconj₂_conj f).is_idempotent_right e.surjective

instance [is_left_cancel α₁ f] :
  is_left_cancel β₁ (e.arrow_congr (e.arrow_congr e) f) :=
⟨e.surjective.forall₃.2 $ λ x y z, by simpa using @is_left_cancel.left_cancel _ f _ x y z⟩

instance [is_right_cancel α₁ f] :
  is_right_cancel β₁ (e.arrow_congr (e.arrow_congr e) f) :=
⟨e.surjective.forall₃.2 $ λ x y z, by simpa using @is_right_cancel.right_cancel _ f _ x y z⟩

end binary_op

/-- `punit` sorts in any two universes are equivalent. -/
def punit_equiv_punit : punit.{v} ≃ punit.{w} :=
⟨λ _, punit.star, λ _, punit.star, λ u, by { cases u, refl }, λ u, by { cases u, reflexivity }⟩

section
/-- The sort of maps to `punit.{v}` is equivalent to `punit.{w}`. -/
def arrow_punit_equiv_punit (α : Sort*) : (α → punit.{v}) ≃ punit.{w} :=
⟨λ f, punit.star, λ u f, punit.star,
  λ f, by { funext x, cases f x, refl }, λ u, by { cases u, reflexivity }⟩


/-- If `α` has a unique term, then the type of function `α → β` is equivalent to `β`. -/
@[simps { fully_applied := ff }] def fun_unique (α β) [unique α] : (α → β) ≃ β :=
{ to_fun := eval default,
  inv_fun := const α,
  left_inv := λ f, funext $ λ a, congr_arg f $ subsingleton.elim _ _,
  right_inv := λ b, rfl }

/-- The sort of maps from `punit` is equivalent to the codomain. -/
def punit_arrow_equiv (α : Sort*) : (punit.{u} → α) ≃ α :=
fun_unique _ _

/-- The sort of maps from `true` is equivalent to the codomain. -/
def true_arrow_equiv (α : Sort*) : (true → α) ≃ α :=
fun_unique _ _

/-- The sort of maps from a type that `is_empty` is equivalent to `punit`. -/
def arrow_punit_of_is_empty (α β : Sort*) [is_empty α] : (α → β) ≃ punit.{u} :=
⟨λ f, punit.star, λ u, is_empty_elim, λ f, funext is_empty_elim, λ u, by { cases u, refl }⟩

/-- The sort of maps from `empty` is equivalent to `punit`. -/
def empty_arrow_equiv_punit (α : Sort*) : (empty → α) ≃ punit.{u} :=
arrow_punit_of_is_empty _ _

/-- The sort of maps from `pempty` is equivalent to `punit`. -/
def pempty_arrow_equiv_punit (α : Sort*) : (pempty → α) ≃ punit.{u} :=
arrow_punit_of_is_empty _ _

/-- The sort of maps from `false` is equivalent to `punit`. -/
def false_arrow_equiv_punit (α : Sort*) : (false → α) ≃ punit.{u} :=
arrow_punit_of_is_empty _ _

end

/-- Product of two equivalences. If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then `α₁ × β₁ ≃ α₂ × β₂`. -/
@[congr, simps apply]
def prod_congr {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
⟨prod.map e₁ e₂, prod.map e₁.symm e₂.symm, λ ⟨a, b⟩, by simp, λ ⟨a, b⟩, by simp⟩

@[simp] theorem prod_congr_symm {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (prod_congr e₁ e₂).symm = prod_congr e₁.symm e₂.symm :=
rfl

/-- Type product is commutative up to an equivalence: `α × β ≃ β × α`. -/
@[simps apply] def prod_comm (α β : Type*) : α × β ≃ β × α :=
⟨prod.swap, prod.swap, λ⟨a, b⟩, rfl, λ⟨a, b⟩, rfl⟩

@[simp] lemma prod_comm_symm (α β) : (prod_comm α β).symm = prod_comm β α := rfl

/-- Type product is associative up to an equivalence. -/
@[simps] def prod_assoc (α β γ : Sort*) : (α × β) × γ ≃ α × (β × γ) :=
⟨λ p, (p.1.1, p.1.2, p.2), λp, ((p.1, p.2.1), p.2.2), λ ⟨⟨a, b⟩, c⟩, rfl, λ ⟨a, ⟨b, c⟩⟩, rfl⟩

/-- Functions on `α × β` are equivalent to functions `α → β → γ`. -/
@[simps {fully_applied := ff}] def curry (α β γ : Type*) :
  (α × β → γ) ≃ (α → β → γ) :=
{ to_fun := curry,
  inv_fun := uncurry,
  left_inv := uncurry_curry,
  right_inv := curry_uncurry }

section
/-- `punit` is a right identity for type product up to an equivalence. -/
@[simps] def prod_punit (α : Type*) : α × punit.{u+1} ≃ α :=
⟨λ p, p.1, λ a, (a, punit.star), λ ⟨_, punit.star⟩, rfl, λ a, rfl⟩

/-- `punit` is a left identity for type product up to an equivalence. -/
@[simps] def punit_prod (α : Type*) : punit.{u+1} × α ≃ α :=
calc punit × α ≃ α × punit : prod_comm _ _
           ... ≃ α         : prod_punit _

/-- `empty` type is a right absorbing element for type product up to an equivalence. -/
def prod_empty (α : Type*) : α × empty ≃ empty :=
equiv_empty _

/-- `empty` type is a left absorbing element for type product up to an equivalence. -/
def empty_prod (α : Type*) : empty × α ≃ empty :=
equiv_empty _

/-- `pempty` type is a right absorbing element for type product up to an equivalence. -/
def prod_pempty (α : Type*) : α × pempty ≃ pempty :=
equiv_pempty _

/-- `pempty` type is a left absorbing element for type product up to an equivalence. -/
def pempty_prod (α : Type*) : pempty × α ≃ pempty :=
equiv_pempty _
end

section
open sum
/-- `psum` is equivalent to `sum`. -/
def psum_equiv_sum (α β : Type*) : psum α β ≃ α ⊕ β :=
⟨λ s, psum.cases_on s inl inr,
 λ s, sum.cases_on s psum.inl psum.inr,
 λ s, by cases s; refl,
 λ s, by cases s; refl⟩

/-- If `α ≃ α'` and `β ≃ β'`, then `α ⊕ β ≃ α' ⊕ β'`. -/
@[simps apply]
def sum_congr {α₁ β₁ α₂ β₂ : Type*} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) : α₁ ⊕ β₁ ≃ α₂ ⊕ β₂ :=
⟨sum.map ea eb, sum.map ea.symm eb.symm, λ x, by simp, λ x, by simp⟩

@[simp] lemma sum_congr_trans {α₁ α₂ β₁ β₂ γ₁ γ₂ : Sort*}
  (e : α₁ ≃ β₁) (f : α₂ ≃ β₂) (g : β₁ ≃ γ₁) (h : β₂ ≃ γ₂) :
  (equiv.sum_congr e f).trans (equiv.sum_congr g h) = (equiv.sum_congr (e.trans g) (f.trans h)) :=
by { ext i, cases i; refl }

@[simp] lemma sum_congr_symm {α β γ δ : Sort*} (e : α ≃ β) (f : γ ≃ δ) :
  (equiv.sum_congr e f).symm = (equiv.sum_congr (e.symm) (f.symm)) :=
rfl

@[simp] lemma sum_congr_refl {α β : Sort*} :
  equiv.sum_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ⊕ β) :=
by { ext i, cases i; refl }

namespace perm

/-- Combine a permutation of `α` and of `β` into a permutation of `α ⊕ β`. -/
@[reducible]
def sum_congr {α β : Type*} (ea : equiv.perm α) (eb : equiv.perm β) : equiv.perm (α ⊕ β) :=
equiv.sum_congr ea eb

@[simp] lemma sum_congr_apply {α β : Type*} (ea : equiv.perm α) (eb : equiv.perm β) (x : α ⊕ β) :
  sum_congr ea eb x = sum.map ⇑ea ⇑eb x := equiv.sum_congr_apply ea eb x

@[simp] lemma sum_congr_trans {α β : Sort*}
  (e : equiv.perm α) (f : equiv.perm β) (g : equiv.perm α) (h : equiv.perm β) :
  (sum_congr e f).trans (sum_congr g h) = sum_congr (e.trans g) (f.trans h) :=
equiv.sum_congr_trans e f g h

@[simp] lemma sum_congr_symm {α β : Sort*} (e : equiv.perm α) (f : equiv.perm β) :
  (sum_congr e f).symm = sum_congr (e.symm) (f.symm) :=
equiv.sum_congr_symm e f

@[simp] lemma sum_congr_refl {α β : Sort*} :
  sum_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ⊕ β) :=
equiv.sum_congr_refl

end perm

/-- `bool` is equivalent the sum of two `punit`s. -/
def bool_equiv_punit_sum_punit : bool ≃ punit.{u+1} ⊕ punit.{v+1} :=
⟨λ b, cond b (inr punit.star) (inl punit.star),
 λ s, sum.rec_on s (λ_, ff) (λ_, tt),
 λ b, by cases b; refl,
 λ s, by rcases s with ⟨⟨⟩⟩ | ⟨⟨⟩⟩; refl⟩

/-- `Prop` is noncomputably equivalent to `bool`. -/
noncomputable def Prop_equiv_bool : Prop ≃ bool :=
⟨λ p, @to_bool p (classical.prop_decidable _),
 λ b, b, λ p, by simp, λ b, by simp⟩

/-- Sum of types is commutative up to an equivalence. -/
@[simps apply]
def sum_comm (α β : Type*) : α ⊕ β ≃ β ⊕ α :=
⟨sum.swap, sum.swap, sum.swap_swap, sum.swap_swap⟩

@[simp] lemma sum_comm_symm (α β) : (sum_comm α β).symm = sum_comm β α := rfl

/-- Sum of types is associative up to an equivalence. -/
def sum_assoc (α β γ : Type*) : (α ⊕ β) ⊕ γ ≃ α ⊕ (β ⊕ γ) :=
⟨sum.elim (sum.elim sum.inl (sum.inr ∘ sum.inl)) (sum.inr ∘ sum.inr),
  sum.elim (sum.inl ∘ sum.inl) $ sum.elim (sum.inl ∘ sum.inr) sum.inr,
  by rintros (⟨_ | _⟩ | _); refl,
  by rintros (_ | ⟨_ | _⟩); refl⟩

@[simp] lemma sum_assoc_apply_inl_inl {α β γ} (a) : sum_assoc α β γ (inl (inl a)) = inl a := rfl

@[simp] lemma sum_assoc_apply_inl_inr {α β γ} (b) : sum_assoc α β γ (inl (inr b)) = inr (inl b) :=
rfl

@[simp] lemma sum_assoc_apply_inr {α β γ} (c) : sum_assoc α β γ (inr c) = inr (inr c) := rfl

@[simp] lemma sum_assoc_symm_apply_inl {α β γ} (a) : (sum_assoc α β γ).symm (inl a) = inl (inl a) :=
rfl

@[simp] lemma sum_assoc_symm_apply_inr_inl {α β γ} (b) :
  (sum_assoc α β γ).symm (inr (inl b)) = inl (inr b) := rfl

@[simp] lemma sum_assoc_symm_apply_inr_inr {α β γ} (c) :
  (sum_assoc α β γ).symm (inr (inr c)) = inr c := rfl


/-- Sum with `empty` is equivalent to the original type. -/
@[simps symm_apply] def sum_empty (α β : Type*) [is_empty β] : α ⊕ β ≃ α :=
⟨sum.elim id is_empty_elim,
 inl,
 λ s, by { rcases s with _ | x, refl, exact is_empty_elim x },
 λ a, rfl⟩

@[simp] lemma sum_empty_apply_inl {α β : Type*} [is_empty β] (a : α) :
  sum_empty α β (sum.inl a) = a := rfl

/-- The sum of `empty` with any `Sort*` is equivalent to the right summand. -/
@[simps symm_apply] def empty_sum (α β : Type*) [is_empty α] : α ⊕ β ≃ β :=
(sum_comm _ _).trans $ sum_empty _ _

@[simp] lemma empty_sum_apply_inr {α β : Type*} [is_empty α] (b : β) :
  empty_sum α β (sum.inr b) = b := rfl

/-- `option α` is equivalent to `α ⊕ punit` -/
def option_equiv_sum_punit (α : Type*) : option α ≃ α ⊕ punit.{u+1} :=
⟨λ o, match o with none := inr punit.star | some a := inl a end,
 λ s, match s with inr _ := none | inl a := some a end,
 λ o, by cases o; refl,
 λ s, by rcases s with _ | ⟨⟨⟩⟩; refl⟩

@[simp] lemma option_equiv_sum_punit_none {α} :
  option_equiv_sum_punit α none = sum.inr punit.star := rfl
@[simp] lemma option_equiv_sum_punit_some {α} (a) :
  option_equiv_sum_punit α (some a) = sum.inl a := rfl

@[simp] lemma option_equiv_sum_punit_coe {α} (a : α) :
  option_equiv_sum_punit α a = sum.inl a := rfl

@[simp] lemma option_equiv_sum_punit_symm_inl {α} (a) :
  (option_equiv_sum_punit α).symm (sum.inl a) = a :=
rfl

@[simp] lemma option_equiv_sum_punit_symm_inr {α} (a) :
  (option_equiv_sum_punit α).symm (sum.inr a) = none :=
rfl

/-- The set of `x : option α` such that `is_some x` is equivalent to `α`. -/
@[simps] def option_is_some_equiv (α : Type*) : {x : option α // x.is_some} ≃ α :=
{ to_fun := λ o, option.get o.2,
  inv_fun := λ x, ⟨some x, dec_trivial⟩,
  left_inv := λ o, subtype.eq $ option.some_get _,
  right_inv := λ x, option.get_some _ _ }

/-- The product over `option α` of `β a` is the binary product of the
product over `α` of `β (some α)` and `β none` -/
@[simps] def pi_option_equiv_prod {α : Type*} {β : option α → Type*} :
  (Π a : option α, β a) ≃ (β none × Π a : α, β (some a)) :=
{ to_fun := λ f, (f none, λ a, f (some a)),
  inv_fun := λ x a, option.cases_on a x.fst x.snd,
  left_inv := λ f, funext $ λ a, by cases a; refl,
  right_inv := λ x, by simp }

/-- `α ⊕ β` is equivalent to a `sigma`-type over `bool`. Note that this definition assumes `α` and
`β` to be types from the same universe, so it cannot by used directly to transfer theorems about
sigma types to theorems about sum types. In many cases one can use `ulift` to work around this
difficulty. -/
def sum_equiv_sigma_bool (α β : Type u) : α ⊕ β ≃ (Σ b: bool, cond b α β) :=
⟨λ s, s.elim (λ x, ⟨tt, x⟩) (λ x, ⟨ff, x⟩),
 λ s, match s with ⟨tt, a⟩ := inl a | ⟨ff, b⟩ := inr b end,
 λ s, by cases s; refl,
 λ s, by rcases s with ⟨_|_, _⟩; refl⟩

/-- `sigma_preimage_equiv f` for `f : α → β` is the natural equivalence between
the type of all fibres of `f` and the total space `α`. -/
@[simps]
def sigma_preimage_equiv {α β : Type*} (f : α → β) :
  (Σ y : β, {x // f x = y}) ≃ α :=
⟨λ x, ↑x.2, λ x, ⟨f x, x, rfl⟩, λ ⟨y, x, rfl⟩, rfl, λ x, rfl⟩

end

section sum_compl

/-- For any predicate `p` on `α`,
the sum of the two subtypes `{a // p a}` and its complement `{a // ¬ p a}`
is naturally equivalent to `α`.

See `subtype_or_equiv` for sum types over subtypes `{x // p x}` and `{x // q x}`
that are not necessarily `is_compl p q`.  -/
def sum_compl {α : Type*} (p : α → Prop) [decidable_pred p] :
  {a // p a} ⊕ {a // ¬ p a} ≃ α :=
{ to_fun := sum.elim coe coe,
  inv_fun := λ a, if h : p a then sum.inl ⟨a, h⟩ else sum.inr ⟨a, h⟩,
  left_inv := by { rintros (⟨x,hx⟩|⟨x,hx⟩); dsimp; [rw dif_pos, rw dif_neg], },
  right_inv := λ a, by { dsimp, split_ifs; refl } }

@[simp] lemma sum_compl_apply_inl {α : Type*} (p : α → Prop) [decidable_pred p]
  (x : {a // p a}) :
  sum_compl p (sum.inl x) = x := rfl

@[simp] lemma sum_compl_apply_inr {α : Type*} (p : α → Prop) [decidable_pred p]
  (x : {a // ¬ p a}) :
  sum_compl p (sum.inr x) = x := rfl

@[simp] lemma sum_compl_apply_symm_of_pos {α : Type*} (p : α → Prop) [decidable_pred p]
  (a : α) (h : p a) :
  (sum_compl p).symm a = sum.inl ⟨a, h⟩ := dif_pos h

@[simp] lemma sum_compl_apply_symm_of_neg {α : Type*} (p : α → Prop) [decidable_pred p]
  (a : α) (h : ¬ p a) :
  (sum_compl p).symm a = sum.inr ⟨a, h⟩ := dif_neg h

/-- Combines an `equiv` between two subtypes with an `equiv` between their complements to form a
  permutation. -/
def subtype_congr {α : Type*} {p q : α → Prop} [decidable_pred p] [decidable_pred q]
  (e : {x // p x} ≃ {x // q x}) (f : {x // ¬p x} ≃ {x // ¬q x}) : perm α :=
(sum_compl p).symm.trans ((sum_congr e f).trans
  (sum_compl q))

open equiv

variables {ε : Type*} {p : ε → Prop} [decidable_pred p]
variables (ep ep' : perm {a // p a}) (en en' : perm {a // ¬ p a})

/-- Combining permutations on `ε` that permute only inside or outside the subtype
split induced by `p : ε → Prop` constructs a permutation on `ε`. -/
def perm.subtype_congr : equiv.perm ε :=
perm_congr (sum_compl p) (sum_congr ep en)

lemma perm.subtype_congr.apply (a : ε) :
  ep.subtype_congr en a = if h : p a then ep ⟨a, h⟩ else en ⟨a, h⟩ :=
by { by_cases h : p a; simp [perm.subtype_congr, h] }

@[simp] lemma perm.subtype_congr.left_apply {a : ε} (h : p a) :
  ep.subtype_congr en a = ep ⟨a, h⟩ :=
by simp [perm.subtype_congr.apply, h]

@[simp] lemma perm.subtype_congr.left_apply_subtype (a : {a // p a}) :
  ep.subtype_congr en a = ep a :=
by { convert perm.subtype_congr.left_apply _ _ a.property, simp }

@[simp] lemma perm.subtype_congr.right_apply {a : ε} (h : ¬ p a) :
  ep.subtype_congr en a = en ⟨a, h⟩ :=
by simp [perm.subtype_congr.apply, h]

@[simp] lemma perm.subtype_congr.right_apply_subtype (a : {a // ¬ p a}) :
  ep.subtype_congr en a = en a :=
by { convert perm.subtype_congr.right_apply _ _ a.property, simp }

@[simp] lemma perm.subtype_congr.refl :
  perm.subtype_congr (equiv.refl {a // p a}) (equiv.refl {a // ¬ p a}) = equiv.refl ε :=
by { ext x, by_cases h : p x; simp [h] }

@[simp] lemma perm.subtype_congr.symm :
  (ep.subtype_congr en).symm = perm.subtype_congr ep.symm en.symm :=
begin
  ext x,
  by_cases h : p x,
  { have : p (ep.symm ⟨x, h⟩) := subtype.property _,
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this] },
  { have : ¬ p (en.symm ⟨x, h⟩) := subtype.property (en.symm _),
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this] }
end

@[simp] lemma perm.subtype_congr.trans :
  (ep.subtype_congr en).trans (ep'.subtype_congr en') =
    perm.subtype_congr (ep.trans ep') (en.trans en') :=
begin
  ext x,
  by_cases h : p x,
  { have : p (ep ⟨x, h⟩) := subtype.property _,
    simp [perm.subtype_congr.apply, h, this] },
  { have : ¬ p (en ⟨x, h⟩) := subtype.property (en _),
    simp [perm.subtype_congr.apply, h, symm_apply_eq, this] }
end

end sum_compl

section subtype_preimage

variables (p : α → Prop) [decidable_pred p] (x₀ : {a // p a} → β)

/-- For a fixed function `x₀ : {a // p a} → β` defined on a subtype of `α`,
the subtype of functions `x : α → β` that agree with `x₀` on the subtype `{a // p a}`
is naturally equivalent to the type of functions `{a // ¬ p a} → β`. -/
@[simps]
def subtype_preimage :
  {x : α → β // x ∘ coe = x₀} ≃ ({a // ¬ p a} → β) :=
{ to_fun := λ (x : {x : α → β // x ∘ coe = x₀}) a, (x : α → β) a,
  inv_fun := λ x, ⟨λ a, if h : p a then x₀ ⟨a, h⟩ else x ⟨a, h⟩,
    funext $ λ ⟨a, h⟩, dif_pos h⟩,
  left_inv := λ ⟨x, hx⟩, subtype.val_injective $ funext $ λ a,
    (by { dsimp, split_ifs; [ rw ← hx, skip ]; refl }),
  right_inv := λ x, funext $ λ ⟨a, h⟩,
    show dite (p a) _ _ = _, by { dsimp, rw [dif_neg h] } }

lemma subtype_preimage_symm_apply_coe_pos (x : {a // ¬ p a} → β) (a : α) (h : p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x₀ ⟨a, h⟩ :=
dif_pos h

lemma subtype_preimage_symm_apply_coe_neg (x : {a // ¬ p a} → β) (a : α) (h : ¬ p a) :
  ((subtype_preimage p x₀).symm x : α → β) a = x ⟨a, h⟩ :=
dif_neg h

end subtype_preimage

section

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Π a, β₁ a` and
`Π a, β₂ a`. -/
def Pi_congr_right {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) : (Π a, β₁ a) ≃ (Π a, β₂ a) :=
⟨λ H a, F a (H a), λ H a, (F a).symm (H a),
 λ H, funext $ by simp, λ H, funext $ by simp⟩

/-- Dependent `curry` equivalence: the type of dependent functions on `Σ i, β i` is equivalent
to the type of dependent functions of two arguments (i.e., functions to the space of functions).

This is `sigma.curry` and `sigma.uncurry` together as an equiv. -/
def Pi_curry {α} {β : α → Sort*} (γ : Π a, β a → Sort*) :
  (Π x : Σ i, β i, γ x.1 x.2) ≃ (Π a b, γ a b) :=
{ to_fun := sigma.curry,
  inv_fun := sigma.uncurry,
  left_inv := sigma.uncurry_curry,
  right_inv := sigma.curry_uncurry }

end

section
/-- A `psigma`-type is equivalent to the corresponding `sigma`-type. -/
@[simps apply symm_apply] def psigma_equiv_sigma {α} (β : α → Type*) : (Σ' i, β i) ≃ Σ i, β i :=
⟨λ a, ⟨a.1, a.2⟩, λ a, ⟨a.1, a.2⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ' a, β₁ a` and
`Σ' a, β₂ a`. -/
@[simps apply]
def psigma_congr_right {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) : (Σ' a, β₁ a) ≃ Σ' a, β₂ a :=
⟨λ a, ⟨a.1, F a.1 a.2⟩, λ a, ⟨a.1, (F a.1).symm a.2⟩,
 λ ⟨a, b⟩, congr_arg (psigma.mk a) $ symm_apply_apply (F a) b,
 λ ⟨a, b⟩, congr_arg (psigma.mk a) $ apply_symm_apply (F a) b⟩

@[simp] lemma psigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Sort*}
  (F : Π a, β₁ a ≃ β₂ a) (G : Π a, β₂ a ≃ β₃ a) :
  (psigma_congr_right F).trans (psigma_congr_right G) =
    psigma_congr_right (λ a, (F a).trans (G a)) :=
by { ext1 x, cases x, refl }

@[simp] lemma psigma_congr_right_symm {α} {β₁ β₂ : α → Sort*} (F : Π a, β₁ a ≃ β₂ a) :
  (psigma_congr_right F).symm = psigma_congr_right (λ a, (F a).symm) :=
by { ext1 x, cases x, refl }

@[simp] lemma psigma_congr_right_refl {α} {β : α → Sort*} :
  (psigma_congr_right (λ a, equiv.refl (β a))) = equiv.refl (Σ' a, β a) :=
by { ext1 x, cases x, refl }

/-- A family of equivalences `Π a, β₁ a ≃ β₂ a` generates an equivalence between `Σ a, β₁ a` and
`Σ a, β₂ a`. -/
@[simps apply]
def sigma_congr_right {α} {β₁ β₂ : α → Type*} (F : Π a, β₁ a ≃ β₂ a) : (Σ a, β₁ a) ≃ Σ a, β₂ a :=
⟨λ a, ⟨a.1, F a.1 a.2⟩, λ a, ⟨a.1, (F a.1).symm a.2⟩,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ symm_apply_apply (F a) b,
 λ ⟨a, b⟩, congr_arg (sigma.mk a) $ apply_symm_apply (F a) b⟩

@[simp] lemma sigma_congr_right_trans {α} {β₁ β₂ β₃ : α → Type*}
  (F : Π a, β₁ a ≃ β₂ a) (G : Π a, β₂ a ≃ β₃ a) :
  (sigma_congr_right F).trans (sigma_congr_right G) = sigma_congr_right (λ a, (F a).trans (G a)) :=
by { ext1 x, cases x, refl }

@[simp] lemma sigma_congr_right_symm {α} {β₁ β₂ : α → Type*} (F : Π a, β₁ a ≃ β₂ a) :
  (sigma_congr_right F).symm = sigma_congr_right (λ a, (F a).symm) :=
by { ext1 x, cases x, refl }

@[simp] lemma sigma_congr_right_refl {α} {β : α → Type*} :
  (sigma_congr_right (λ a, equiv.refl (β a))) = equiv.refl (Σ a, β a) :=
by { ext1 x, cases x, refl }

/-- A `psigma` with `Prop` fibers is equivalent to the subtype.  -/
def psigma_equiv_subtype {α : Type v} (P : α → Prop) :
  (Σ' i, P i) ≃ subtype P :=
{ to_fun := λ x, ⟨x.1, x.2⟩,
  inv_fun := λ x, ⟨x.1, x.2⟩,
  left_inv := λ x, by { cases x, refl, },
  right_inv := λ x, by { cases x, refl, }, }

/-- A `sigma` with `plift` fibers is equivalent to the subtype. -/
def sigma_plift_equiv_subtype {α : Type v} (P : α → Prop) :
  (Σ i, plift (P i)) ≃ subtype P :=
((psigma_equiv_sigma _).symm.trans (psigma_congr_right (λ a, equiv.plift))).trans
  (psigma_equiv_subtype P)

/--
A `sigma` with `λ i, ulift (plift (P i))` fibers is equivalent to `{ x // P x }`.
Variant of `sigma_plift_equiv_subtype`.
-/
def sigma_ulift_plift_equiv_subtype {α : Type v} (P : α → Prop) :
  (Σ i, ulift (plift (P i))) ≃ subtype P :=
(sigma_congr_right (λ a, equiv.ulift)).trans (sigma_plift_equiv_subtype P)

namespace perm

/-- A family of permutations `Π a, perm (β a)` generates a permuation `perm (Σ a, β₁ a)`. -/
@[reducible]
def sigma_congr_right {α} {β : α → Sort*} (F : Π a, perm (β a)) : perm (Σ a, β a) :=
equiv.sigma_congr_right F

@[simp] lemma sigma_congr_right_trans {α} {β : α → Sort*}
  (F : Π a, perm (β a)) (G : Π a, perm (β a)) :
  (sigma_congr_right F).trans (sigma_congr_right G) = sigma_congr_right (λ a, (F a).trans (G a)) :=
equiv.sigma_congr_right_trans F G

@[simp] lemma sigma_congr_right_symm {α} {β : α → Sort*} (F : Π a, perm (β a)) :
  (sigma_congr_right F).symm = sigma_congr_right (λ a, (F a).symm) :=
equiv.sigma_congr_right_symm F

@[simp] lemma sigma_congr_right_refl {α} {β : α → Sort*} :
  (sigma_congr_right (λ a, equiv.refl (β a))) = equiv.refl (Σ a, β a) :=
equiv.sigma_congr_right_refl

end perm

/-- An equivalence `f : α₁ ≃ α₂` generates an equivalence between `Σ a, β (f a)` and `Σ a, β a`. -/
@[simps apply]
def sigma_congr_left {α₁ α₂} {β : α₂ → Sort*} (e : α₁ ≃ α₂) : (Σ a:α₁, β (e a)) ≃ (Σ a:α₂, β a) :=
⟨λ a, ⟨e a.1, a.2⟩, λ a, ⟨e.symm a.1, @@eq.rec β a.2 (e.right_inv a.1).symm⟩,
 λ ⟨a, b⟩, match e.symm (e a), e.left_inv a : ∀ a' (h : a' = a),
     @sigma.mk _ (β ∘ e) _ (@@eq.rec β b (congr_arg e h.symm)) = ⟨a, b⟩ with
   | _, rfl := rfl end,
 λ ⟨a, b⟩, match e (e.symm a), _ : ∀ a' (h : a' = a),
     sigma.mk a' (@@eq.rec β b h.symm) = ⟨a, b⟩ with
   | _, rfl := rfl end⟩

/-- Transporting a sigma type through an equivalence of the base -/
def sigma_congr_left' {α₁ α₂} {β : α₁ → Sort*} (f : α₁ ≃ α₂) :
  (Σ a:α₁, β a) ≃ (Σ a:α₂, β (f.symm a)) :=
(sigma_congr_left f.symm).symm

/-- Transporting a sigma type through an equivalence of the base and a family of equivalences
of matching fibers -/
def sigma_congr {α₁ α₂} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*} (f : α₁ ≃ α₂)
  (F : ∀ a, β₁ a ≃ β₂ (f a)) :
  sigma β₁ ≃ sigma β₂ :=
(sigma_congr_right F).trans (sigma_congr_left f)

/-- `sigma` type with a constant fiber is equivalent to the product. -/
@[simps apply symm_apply] def sigma_equiv_prod (α β : Type*) : (Σ_:α, β) ≃ α × β :=
⟨λ a, ⟨a.1, a.2⟩, λ a, ⟨a.1, a.2⟩, λ ⟨a, b⟩, rfl, λ ⟨a, b⟩, rfl⟩

/-- If each fiber of a `sigma` type is equivalent to a fixed type, then the sigma type
is equivalent to the product. -/
def sigma_equiv_prod_of_equiv {α β} {β₁ : α → Sort*} (F : Π a, β₁ a ≃ β) : sigma β₁ ≃ α × β :=
(sigma_congr_right F).trans (sigma_equiv_prod α β)

/-- Dependent product of types is associative up to an equivalence. -/
def sigma_assoc {α : Type*} {β : α → Type*} (γ : Π (a : α), β a → Type*) :
  (Σ (ab : Σ (a : α), β a), γ ab.1 ab.2) ≃ Σ (a : α), (Σ (b : β a), γ a b) :=
{ to_fun := λ x, ⟨x.1.1, ⟨x.1.2, x.2⟩⟩,
  inv_fun := λ x, ⟨⟨x.1, x.2.1⟩, x.2.2⟩,
  left_inv := λ ⟨⟨a, b⟩, c⟩, rfl,
  right_inv := λ ⟨a, ⟨b, c⟩⟩, rfl }

end

section prod_congr

variables {α₁ β₁ β₂ : Type*} (e : α₁ → β₁ ≃ β₂)

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `β₁ × α₁` and `β₂ × α₁`. -/
def prod_congr_left : β₁ × α₁ ≃ β₂ × α₁ :=
{ to_fun := λ ab, ⟨e ab.2 ab.1, ab.2⟩,
  inv_fun := λ ab, ⟨(e ab.2).symm ab.1, ab.2⟩,
  left_inv := by { rintros ⟨a, b⟩, simp },
  right_inv := by { rintros ⟨a, b⟩, simp } }

@[simp] lemma prod_congr_left_apply (b : β₁) (a : α₁) :
prod_congr_left e (b, a) = (e a b, a) := rfl

lemma prod_congr_refl_right (e : β₁ ≃ β₂) :
  prod_congr e (equiv.refl α₁) = prod_congr_left (λ _, e) :=
by { ext ⟨a, b⟩ : 1, simp }

/-- A family of equivalences `Π (a : α₁), β₁ ≃ β₂` generates an equivalence
between `α₁ × β₁` and `α₁ × β₂`. -/
def prod_congr_right : α₁ × β₁ ≃ α₁ × β₂ :=
{ to_fun := λ ab, ⟨ab.1, e ab.1 ab.2⟩,
  inv_fun := λ ab, ⟨ab.1, (e ab.1).symm ab.2⟩,
  left_inv := by { rintros ⟨a, b⟩, simp },
  right_inv := by { rintros ⟨a, b⟩, simp } }

@[simp] lemma prod_congr_right_apply (a : α₁) (b : β₁) :
  prod_congr_right e (a, b) = (a, e a b) := rfl

lemma prod_congr_refl_left (e : β₁ ≃ β₂) :
  prod_congr (equiv.refl α₁) e = prod_congr_right (λ _, e) :=
by { ext ⟨a, b⟩ : 1, simp }

@[simp] lemma prod_congr_left_trans_prod_comm :
  (prod_congr_left e).trans (prod_comm _ _) = (prod_comm _ _).trans (prod_congr_right e) :=
by { ext ⟨a, b⟩ : 1, simp }

@[simp] lemma prod_congr_right_trans_prod_comm :
  (prod_congr_right e).trans (prod_comm _ _) = (prod_comm _ _).trans (prod_congr_left e) :=
by { ext ⟨a, b⟩ : 1, simp }

lemma sigma_congr_right_sigma_equiv_prod :
  (sigma_congr_right e).trans (sigma_equiv_prod α₁ β₂) =
    (sigma_equiv_prod α₁ β₁).trans (prod_congr_right e) :=
by { ext ⟨a, b⟩ : 1, simp }

lemma sigma_equiv_prod_sigma_congr_right :
  (sigma_equiv_prod α₁ β₁).symm.trans (sigma_congr_right e) =
    (prod_congr_right e).trans (sigma_equiv_prod α₁ β₂).symm :=
by { ext ⟨a, b⟩ : 1, simp }

/-- A variation on `equiv.prod_congr` where the equivalence in the second component can depend
  on the first component. A typical example is a shear mapping, explaining the name of this
  declaration. -/
@[simps {fully_applied := ff}]
def prod_shear {α₁ β₁ α₂ β₂ : Type*} (e₁ : α₁ ≃ α₂) (e₂ : α₁ → β₁ ≃ β₂) : α₁ × β₁ ≃ α₂ × β₂ :=
{ to_fun := λ x : α₁ × β₁, (e₁ x.1, e₂ x.1 x.2),
  inv_fun := λ y : α₂ × β₂, (e₁.symm y.1, (e₂ $ e₁.symm y.1).symm y.2),
  left_inv := by { rintro ⟨x₁, y₁⟩, simp only [symm_apply_apply] },
  right_inv := by { rintro ⟨x₁, y₁⟩, simp only [apply_symm_apply] } }

end prod_congr

namespace perm

variables {α₁ β₁ β₂ : Type*} [decidable_eq α₁] (a : α₁) (e : perm β₁)

/-- `prod_extend_right a e` extends `e : perm β` to `perm (α × β)` by sending `(a, b)` to
`(a, e b)` and keeping the other `(a', b)` fixed. -/
def prod_extend_right : perm (α₁ × β₁) :=
{ to_fun := λ ab, if ab.fst = a then (a, e ab.snd) else ab,
  inv_fun := λ ab, if ab.fst = a then (a, e.symm ab.snd) else ab,
  left_inv := by { rintros ⟨k', x⟩, dsimp only, split_ifs with h; simp [h] },
  right_inv := by { rintros ⟨k', x⟩, dsimp only, split_ifs with h; simp [h] } }

@[simp] lemma prod_extend_right_apply_eq (b : β₁) :
  prod_extend_right a e (a, b) = (a, e b) := if_pos rfl

lemma prod_extend_right_apply_ne {a a' : α₁} (h : a' ≠ a) (b : β₁) :
  prod_extend_right a e (a', b) = (a', b) := if_neg h

lemma eq_of_prod_extend_right_ne {e : perm β₁} {a a' : α₁} {b : β₁}
  (h : prod_extend_right a e (a', b) ≠ (a', b)) : a' = a :=
by { contrapose! h, exact prod_extend_right_apply_ne _ h _ }

@[simp] lemma fst_prod_extend_right (ab : α₁ × β₁) :
  (prod_extend_right a e ab).fst = ab.fst :=
begin
  rw [prod_extend_right, coe_fn_mk],
  split_ifs with h,
  { rw h },
  { refl }
end

end perm

section
/-- The type of functions to a product `α × β` is equivalent to the type of pairs of functions
`γ → α` and `γ → β`. -/
def arrow_prod_equiv_prod_arrow (α β γ : Type*) : (γ → α × β) ≃ (γ → α) × (γ → β) :=
⟨λ f, (λ c, (f c).1, λ c, (f c).2),
 λ p c, (p.1 c, p.2 c),
 λ f, funext $ λ c, prod.mk.eta,
 λ p, by { cases p, refl }⟩

open sum
/-- The type of functions on a sum type `α ⊕ β` is equivalent to the type of pairs of functions
on `α` and on `β`. -/
def sum_arrow_equiv_prod_arrow (α β γ : Type*) : ((α ⊕ β) → γ) ≃ (α → γ) × (β → γ) :=
⟨λ f, (f ∘ inl, f ∘ inr),
 λ p, sum.elim p.1 p.2,
 λ f, by { ext ⟨⟩; refl },
 λ p, by { cases p, refl }⟩

@[simp] lemma sum_arrow_equiv_prod_arrow_apply_fst {α β γ} (f : (α ⊕ β) → γ) (a : α) :
  (sum_arrow_equiv_prod_arrow α β γ f).1 a = f (inl a) := rfl
@[simp] lemma sum_arrow_equiv_prod_arrow_apply_snd {α β γ} (f : (α ⊕ β) → γ) (b : β) :
  (sum_arrow_equiv_prod_arrow α β γ f).2 b = f (inr b) := rfl
@[simp] lemma sum_arrow_equiv_prod_arrow_symm_apply_inl {α β γ} (f : α → γ) (g : β → γ) (a : α) :
  ((sum_arrow_equiv_prod_arrow α β γ).symm (f, g)) (inl a) = f a := rfl
@[simp] lemma sum_arrow_equiv_prod_arrow_symm_apply_inr {α β γ} (f : α → γ) (g : β → γ) (b : β) :
  ((sum_arrow_equiv_prod_arrow α β γ).symm (f, g)) (inr b) = g b := rfl

/-- Type product is right distributive with respect to type sum up to an equivalence. -/
def sum_prod_distrib (α β γ : Sort*) : (α ⊕ β) × γ ≃ (α × γ) ⊕ (β × γ) :=
⟨λ p, match p with (inl a, c) := inl (a, c) | (inr b, c) := inr (b, c) end,
 λ s, match s with inl q := (inl q.1, q.2) | inr q := (inr q.1, q.2) end,
 λ p, by rcases p with ⟨_ | _, _⟩; refl,
 λ s, by rcases s with ⟨_, _⟩ | ⟨_, _⟩; refl⟩

@[simp] theorem sum_prod_distrib_apply_left {α β γ} (a : α) (c : γ) :
   sum_prod_distrib α β γ (sum.inl a, c) = sum.inl (a, c) := rfl
@[simp] theorem sum_prod_distrib_apply_right {α β γ} (b : β) (c : γ) :
   sum_prod_distrib α β γ (sum.inr b, c) = sum.inr (b, c) := rfl

/-- Type product is left distributive with respect to type sum up to an equivalence. -/
def prod_sum_distrib (α β γ : Sort*) : α × (β ⊕ γ) ≃ (α × β) ⊕ (α × γ) :=
calc α × (β ⊕ γ) ≃ (β ⊕ γ) × α       : prod_comm _ _
            ...   ≃ (β × α) ⊕ (γ × α) : sum_prod_distrib _ _ _
            ...   ≃ (α × β) ⊕ (α × γ) : sum_congr (prod_comm _ _) (prod_comm _ _)

@[simp] theorem prod_sum_distrib_apply_left {α β γ} (a : α) (b : β) :
   prod_sum_distrib α β γ (a, sum.inl b) = sum.inl (a, b) := rfl
@[simp] theorem prod_sum_distrib_apply_right {α β γ} (a : α) (c : γ) :
   prod_sum_distrib α β γ (a, sum.inr c) = sum.inr (a, c) := rfl

/-- The product of an indexed sum of types (formally, a `sigma`-type `Σ i, α i`) by a type `β` is
equivalent to the sum of products `Σ i, (α i × β)`. -/
def sigma_prod_distrib {ι : Type*} (α : ι → Type*) (β : Type*) :
  ((Σ i, α i) × β) ≃ (Σ i, (α i × β)) :=
⟨λ p, ⟨p.1.1, (p.1.2, p.2)⟩,
 λ p, (⟨p.1, p.2.1⟩, p.2.2),
 λ p, by { rcases p with ⟨⟨_, _⟩, _⟩, refl },
 λ p, by { rcases p with ⟨_, ⟨_, _⟩⟩, refl }⟩

/-- The product `bool × α` is equivalent to `α ⊕ α`. -/
def bool_prod_equiv_sum (α : Type u) : bool × α ≃ α ⊕ α :=
calc bool × α ≃ (unit ⊕ unit) × α       : prod_congr bool_equiv_punit_sum_punit (equiv.refl _)
      ...     ≃ (unit × α) ⊕ (unit × α) : sum_prod_distrib _ _ _
      ...     ≃ α ⊕ α                   : sum_congr (punit_prod _) (punit_prod _)

/-- The function type `bool → α` is equivalent to `α × α`. -/
@[simps] def bool_arrow_equiv_prod (α : Type u) : (bool → α) ≃ α × α :=
{ to_fun := λ f, (f tt, f ff),
  inv_fun := λ p b, cond b p.1 p.2,
  left_inv := λ f, funext $ bool.forall_bool.2 ⟨rfl, rfl⟩,
  right_inv := λ ⟨x, y⟩, rfl }

end

section
open sum nat
/-- The set of natural numbers is equivalent to `ℕ ⊕ punit`. -/
def nat_equiv_nat_sum_punit : ℕ ≃ ℕ ⊕ punit.{u+1} :=
⟨λ n, match n with zero := inr punit.star | succ a := inl a end,
 λ s, match s with inl n := succ n | inr punit.star := zero end,
 λ n, begin cases n, repeat { refl } end,
 λ s, begin cases s with a u, { refl }, {cases u, { refl }} end⟩

/-- `ℕ ⊕ punit` is equivalent to `ℕ`. -/
def nat_sum_punit_equiv_nat : ℕ ⊕ punit.{u+1} ≃ ℕ :=
nat_equiv_nat_sum_punit.symm

/-- The type of integer numbers is equivalent to `ℕ ⊕ ℕ`. -/
def int_equiv_nat_sum_nat : ℤ ≃ ℕ ⊕ ℕ :=
by refine ⟨_, _, _, _⟩; intro z; {cases z; [left, right]; assumption} <|> {cases z; refl}

end

/-- An equivalence between `α` and `β` generates an equivalence between `list α` and `list β`. -/
def list_equiv_of_equiv {α β : Type*} (e : α ≃ β) : list α ≃ list β :=
{ to_fun := list.map e,
  inv_fun := list.map e.symm,
  left_inv := λ l, by rw [list.map_map, e.symm_comp_self, list.map_id],
  right_inv := λ l, by rw [list.map_map, e.self_comp_symm, list.map_id] }

/-- `fin n` is equivalent to `{m // m < n}`. -/
def fin_equiv_subtype (n : ℕ) : fin n ≃ {m // m < n} :=
⟨λ x, ⟨x.1, x.2⟩, λ x, ⟨x.1, x.2⟩, λ ⟨a, b⟩, rfl,λ ⟨a, b⟩, rfl⟩

/-- If `α` is equivalent to `β`, then `unique α` is equivalent to `unique β`. -/
def unique_congr (e : α ≃ β) : unique α ≃ unique β :=
{ to_fun := λ h, @equiv.unique _ _ h e.symm,
  inv_fun := λ h, @equiv.unique _ _ h e,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- If `α` is equivalent to `β`, then `is_empty α` is equivalent to `is_empty β`. -/
lemma is_empty_congr (e : α ≃ β) : is_empty α ↔ is_empty β :=
⟨λ h, @function.is_empty _ _ h e.symm, λ h, @function.is_empty _ _ h e⟩

protected lemma is_empty (e : α ≃ β) [is_empty β] : is_empty α :=
e.is_empty_congr.mpr ‹_›

section
open subtype

/-- If `α` is equivalent to `β` and the predicates `p : α → Prop` and `q : β → Prop` are equivalent
at corresponding points, then `{a // p a}` is equivalent to `{b // q b}`.
For the statement where `α = β`, that is, `e : perm α`, see `perm.subtype_perm`. -/
def subtype_equiv {p : α → Prop} {q : β → Prop}
  (e : α ≃ β) (h : ∀ a, p a ↔ q (e a)) : {a : α // p a} ≃ {b : β // q b} :=
⟨λ x, ⟨e x, (h _).1 x.2⟩,
 λ y, ⟨e.symm y, (h _).2 (by { simp, exact y.2 })⟩,
 λ ⟨x, h⟩, subtype.ext_val $ by simp,
 λ ⟨y, h⟩, subtype.ext_val $ by simp⟩

@[simp] lemma subtype_equiv_refl {p : α → Prop}
  (h : ∀ a, p a ↔ p (equiv.refl _ a) := λ a, iff.rfl) :
  (equiv.refl α).subtype_equiv h = equiv.refl {a : α // p a} :=
by { ext, refl }

@[simp] lemma subtype_equiv_symm {p : α → Prop} {q : β → Prop} (e : α ≃ β)
  (h : ∀ (a : α), p a ↔ q (e a)) :
  (e.subtype_equiv h).symm = e.symm.subtype_equiv (λ a, by
  { convert (h $ e.symm a).symm,
    exact (e.apply_symm_apply a).symm }) :=
rfl

@[simp] lemma subtype_equiv_trans {p : α → Prop} {q : β → Prop} {r : γ → Prop}
  (e : α ≃ β) (f : β ≃ γ)
  (h : ∀ (a : α), p a ↔ q (e a)) (h' : ∀ (b : β), q b ↔ r (f b)):
  (e.subtype_equiv h).trans (f.subtype_equiv h') =
    (e.trans f).subtype_equiv (λ a, (h a).trans (h' $ e a)) :=
rfl

@[simp] lemma subtype_equiv_apply {p : α → Prop} {q : β → Prop} (e : α ≃ β)
  (h : ∀ (a : α), p a ↔ q (e a)) (x : {x // p x}) :
  e.subtype_equiv h x = ⟨e x, (h _).1 x.2⟩ :=
rfl

/-- If two predicates `p` and `q` are pointwise equivalent, then `{x // p x}` is equivalent to
`{x // q x}`. -/
@[simps]
def subtype_equiv_right {p q : α → Prop} (e : ∀x, p x ↔ q x) : {x // p x} ≃ {x // q x} :=
subtype_equiv (equiv.refl _) e

/-- If `α ≃ β`, then for any predicate `p : β → Prop` the subtype `{a // p (e a)}` is equivalent
to the subtype `{b // p b}`. -/
def subtype_equiv_of_subtype {p : β → Prop} (e : α ≃ β) :
  {a : α // p (e a)} ≃ {b : β // p b} :=
subtype_equiv e $ by simp

/-- If `α ≃ β`, then for any predicate `p : α → Prop` the subtype `{a // p a}` is equivalent
to the subtype `{b // p (e.symm b)}`. This version is used by `equiv_rw`. -/
def subtype_equiv_of_subtype' {p : α → Prop} (e : α ≃ β) :
  {a : α // p a} ≃ {b : β // p (e.symm b)} :=
e.symm.subtype_equiv_of_subtype.symm

/-- If two predicates are equal, then the corresponding subtypes are equivalent. -/
def subtype_equiv_prop {α : Type*} {p q : α → Prop} (h : p = q) : subtype p ≃ subtype q :=
subtype_equiv (equiv.refl α) (assume a, h ▸ iff.rfl)

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. This
version allows the “inner” predicate to depend on `h : p a`. -/
def subtype_subtype_equiv_subtype_exists {α : Type u} (p : α → Prop) (q : subtype p → Prop) :
  subtype q ≃ {a : α // ∃h:p a, q ⟨a, h⟩ } :=
⟨λ⟨⟨a, ha⟩, ha'⟩, ⟨a, ha, ha'⟩,
  λ⟨a, ha⟩, ⟨⟨a, ha.cases_on $ assume h _, h⟩, by { cases ha, exact ha_h }⟩,
  assume ⟨⟨a, ha⟩, h⟩, rfl, assume ⟨a, h₁, h₂⟩, rfl⟩

@[simp] lemma subtype_subtype_equiv_subtype_exists_apply {α : Type u} (p : α → Prop)
  (q : subtype p → Prop) (a) : (subtype_subtype_equiv_subtype_exists p q a : α) = a :=
by { cases a, cases a_val, refl }

/-- A subtype of a subtype is equivalent to the subtype of elements satisfying both predicates. -/
def subtype_subtype_equiv_subtype_inter {α : Type u} (p q : α → Prop) :
  {x : subtype p // q x.1} ≃ subtype (λ x, p x ∧ q x) :=
(subtype_subtype_equiv_subtype_exists p _).trans $
subtype_equiv_right $ λ x, exists_prop

@[simp] lemma subtype_subtype_equiv_subtype_inter_apply {α : Type u} (p q : α → Prop) (a) :
  (subtype_subtype_equiv_subtype_inter p q a : α) = a :=
by { cases a, cases a_val, refl }

/-- If the outer subtype has more restrictive predicate than the inner one,
then we can drop the latter. -/
def subtype_subtype_equiv_subtype {α : Type u} {p q : α → Prop} (h : ∀ {x}, q x → p x) :
  {x : subtype p // q x.1} ≃ subtype q :=
(subtype_subtype_equiv_subtype_inter p _).trans $
subtype_equiv_right $
assume x,
⟨and.right, λ h₁, ⟨h h₁, h₁⟩⟩

@[simp] lemma subtype_subtype_equiv_subtype_apply {α : Type u} {p q : α → Prop} (h : ∀ x, q x → p x)
  (a : {x : subtype p // q x.1}) :
  (subtype_subtype_equiv_subtype h a : α) = a :=
by { cases a, cases a_val, refl }

/-- If a proposition holds for all elements, then the subtype is
equivalent to the original type. -/
@[simps apply symm_apply]
def subtype_univ_equiv {α : Type u} {p : α → Prop} (h : ∀ x, p x) :
  subtype p ≃ α :=
⟨λ x, x, λ x, ⟨x, h x⟩, λ x, subtype.eq rfl, λ x, rfl⟩

/-- A subtype of a sigma-type is a sigma-type over a subtype. -/
def subtype_sigma_equiv {α : Type u} (p : α → Type v) (q : α → Prop) :
  { y : sigma p // q y.1 } ≃ Σ(x : subtype q), p x.1 :=
⟨λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
 λ x, ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
 λ ⟨⟨x, h⟩, y⟩, rfl,
 λ ⟨⟨x, y⟩, h⟩, rfl⟩

/-- A sigma type over a subtype is equivalent to the sigma set over the original type,
if the fiber is empty outside of the subset -/
def sigma_subtype_equiv_of_subset {α : Type u} (p : α → Type v) (q : α → Prop)
  (h : ∀ x, p x → q x) :
  (Σ x : subtype q, p x) ≃ Σ x : α, p x :=
(subtype_sigma_equiv p q).symm.trans $ subtype_univ_equiv $ λ x, h x.1 x.2

/-- If a predicate `p : β → Prop` is true on the range of a map `f : α → β`, then
`Σ y : {y // p y}, {x // f x = y}` is equivalent to `α`. -/
def sigma_subtype_preimage_equiv {α : Type u} {β : Type v} (f : α → β) (p : β → Prop)
  (h : ∀ x, p (f x)) :
  (Σ y : subtype p, {x : α // f x = y}) ≃ α :=
calc _ ≃ Σ y : β, {x : α // f x = y} : sigma_subtype_equiv_of_subset _ p (λ y ⟨x, h'⟩, h' ▸ h x)
   ... ≃ α                           : sigma_preimage_equiv f

/-- If for each `x` we have `p x ↔ q (f x)`, then `Σ y : {y // q y}, f ⁻¹' {y}` is equivalent
to `{x // p x}`. -/
def sigma_subtype_preimage_equiv_subtype {α : Type u} {β : Type v} (f : α → β)
  {p : α → Prop} {q : β → Prop} (h : ∀ x, p x ↔ q (f x)) :
  (Σ y : subtype q, {x : α // f x = y}) ≃ subtype p :=
calc (Σ y : subtype q, {x : α // f x = y}) ≃
  Σ y : subtype q, {x : subtype p // subtype.mk (f x) ((h x).1 x.2) = y} :
  begin
    apply sigma_congr_right,
    assume y,
    symmetry,
    refine (subtype_subtype_equiv_subtype_exists _ _).trans (subtype_equiv_right _),
    assume x,
    exact ⟨λ ⟨hp, h'⟩, congr_arg subtype.val h', λ h', ⟨(h x).2 (h'.symm ▸ y.2), subtype.eq h'⟩⟩
  end

   ... ≃ subtype p : sigma_preimage_equiv (λ x : subtype p, (⟨f x, (h x).1 x.property⟩ : subtype q))

/-- A sigma type over an `option` is equivalent to the sigma set over the original type,
if the fiber is empty at none. -/
def sigma_option_equiv_of_some {α : Type u} (p : option α → Type v) (h : p none → false) :
  (Σ x : option α, p x) ≃ (Σ x : α, p (some x)) :=
begin
  have h' : ∀ x, p x → x.is_some,
  { intro x,
    cases x,
    { intro n, exfalso, exact h n },
    { intro s, exact rfl } },
  exact (sigma_subtype_equiv_of_subset _ _ h').symm.trans
    (sigma_congr_left' (option_is_some_equiv α)),
end

/-- The `pi`-type `Π i, π i` is equivalent to the type of sections `f : ι → Σ i, π i` of the
`sigma` type such that for all `i` we have `(f i).fst = i`. -/
def pi_equiv_subtype_sigma (ι : Type*) (π : ι → Type*) :
  (Π i, π i) ≃ {f : ι → Σ i, π i // ∀ i, (f i).1 = i } :=
⟨ λf, ⟨λi, ⟨i, f i⟩, assume i, rfl⟩, λf i, begin rw ← f.2 i, exact (f.1 i).2 end,
  assume f, funext $ assume i, rfl,
  assume ⟨f, hf⟩, subtype.eq $ funext $ assume i, sigma.eq (hf i).symm $
    eq_of_heq $ rec_heq_of_heq _ $ rec_heq_of_heq _ $ heq.refl _⟩

/-- The set of functions `f : Π a, β a` such that for all `a` we have `p a (f a)` is equivalent
to the set of functions `Π a, {b : β a // p a b}`. -/
def subtype_pi_equiv_pi {α : Sort u} {β : α → Sort v} {p : Πa, β a → Prop} :
  {f : Πa, β a // ∀a, p a (f a) } ≃ Πa, { b : β a // p a b } :=
⟨λf a, ⟨f.1 a, f.2 a⟩, λf, ⟨λa, (f a).1, λa, (f a).2⟩,
  by { rintro ⟨f, h⟩, refl },
  by { rintro f, funext a, exact subtype.ext_val rfl }⟩

/-- A subtype of a product defined by componentwise conditions
is equivalent to a product of subtypes. -/
def subtype_prod_equiv_prod {α : Type u} {β : Type v} {p : α → Prop} {q : β → Prop} :
  {c : α × β // p c.1 ∧ q c.2} ≃ ({a // p a} × {b // q b}) :=
⟨λ x, ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
 λ x, ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩,
 λ ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl,
 λ ⟨⟨_, _⟩, ⟨_, _⟩⟩, rfl⟩

/-- A subtype of a `prod` is equivalent to a sigma type whose fibers are subtypes. -/
def subtype_prod_equiv_sigma_subtype {α β : Type*} (p : α → β → Prop) :
  {x : α × β // p x.1 x.2} ≃ Σ a, {b : β // p a b} :=
{ to_fun := λ x, ⟨x.1.1, x.1.2, x.prop⟩,
  inv_fun := λ x, ⟨⟨x.1, x.2⟩, x.2.prop⟩,
  left_inv := λ x, by ext; refl,
  right_inv := λ ⟨a, b, pab⟩, rfl }

/-- The type `Π (i : α), β i` can be split as a product by separating the indices in `α`
depending on whether they satisfy a predicate `p` or not. -/
@[simps] def pi_equiv_pi_subtype_prod
  {α : Type*} (p : α → Prop) (β : α → Type*) [decidable_pred p] :
  (Π (i : α), β i) ≃ (Π (i : {x // p x}), β i) × (Π (i : {x // ¬ p x}), β i) :=
{ to_fun := λ f, (λ x, f x, λ x, f x),
  inv_fun := λ f x, if h : p x then f.1 ⟨x, h⟩ else f.2 ⟨x, h⟩,
  right_inv := begin
    rintros ⟨f, g⟩,
    ext1;
    { ext y,
      rcases y,
      simp only [y_property, dif_pos, dif_neg, not_false_iff, subtype.coe_mk],
      refl },
  end,
  left_inv := λ f, begin
    ext x,
    by_cases h : p x;
    { simp only [h, dif_neg, dif_pos, not_false_iff],
      refl },
  end }

end

section subtype_equiv_codomain
variables {X : Type*} {Y : Type*} [decidable_eq X] {x : X}

/-- The type of all functions `X → Y` with prescribed values for all `x' ≠ x`
is equivalent to the codomain `Y`. -/
def subtype_equiv_codomain (f : {x' // x' ≠ x} → Y) : {g : X → Y // g ∘ coe = f} ≃ Y :=
(subtype_preimage _ f).trans $
@fun_unique {x' // ¬ x' ≠ x} _ $
show unique {x' // ¬ x' ≠ x}, from @equiv.unique _ _
  (show unique {x' // x' = x}, from
    { default := ⟨x, rfl⟩, uniq := λ ⟨x', h⟩, subtype.val_injective h })
  (subtype_equiv_right $ λ a, not_not)

@[simp] lemma coe_subtype_equiv_codomain (f : {x' // x' ≠ x} → Y) :
  (subtype_equiv_codomain f : {g : X → Y // g ∘ coe = f} → Y) = λ g, (g : X → Y) x := rfl

@[simp] lemma subtype_equiv_codomain_apply (f : {x' // x' ≠ x} → Y)
  (g : {g : X → Y // g ∘ coe = f}) :
  subtype_equiv_codomain f g = (g : X → Y) x := rfl

lemma coe_subtype_equiv_codomain_symm (f : {x' // x' ≠ x} → Y) :
  ((subtype_equiv_codomain f).symm : Y → {g : X → Y // g ∘ coe = f}) =
  λ y, ⟨λ x', if h : x' ≠ x then f ⟨x', h⟩ else y,
    by { funext x', dsimp, erw [dif_pos x'.2, subtype.coe_eta] }⟩ := rfl

@[simp] lemma subtype_equiv_codomain_symm_apply (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = if h : x' ≠ x then f ⟨x', h⟩ else y :=
rfl

@[simp] lemma subtype_equiv_codomain_symm_apply_eq (f : {x' // x' ≠ x} → Y) (y : Y) :
  ((subtype_equiv_codomain f).symm y : X → Y) x = y :=
dif_neg (not_not.mpr rfl)

lemma subtype_equiv_codomain_symm_apply_ne (f : {x' // x' ≠ x} → Y) (y : Y) (x' : X) (h : x' ≠ x) :
  ((subtype_equiv_codomain f).symm y : X → Y) x' = f ⟨x', h⟩ :=
dif_pos h

end subtype_equiv_codomain

/-- If `f` is a bijective function, then its domain is equivalent to its codomain. -/
@[simps apply]
noncomputable def of_bijective {α β} (f : α → β) (hf : bijective f) : α ≃ β :=
{ to_fun := f,
  inv_fun := function.surj_inv hf.surjective,
  left_inv := function.left_inverse_surj_inv hf,
  right_inv := function.right_inverse_surj_inv _}

lemma of_bijective_apply_symm_apply {α β} (f : α → β) (hf : bijective f) (x : β) :
  f ((of_bijective f hf).symm x) = x :=
(of_bijective f hf).apply_symm_apply x

@[simp] lemma of_bijective_symm_apply_apply {α β} (f : α → β) (hf : bijective f) (x : α) :
  (of_bijective f hf).symm (f x) = x :=
(of_bijective f hf).symm_apply_apply x

section

variables {α' β' : Type*} (e : perm α') {p : β' → Prop} [decidable_pred p]
  (f : α' ≃ subtype p)

/--
Extend the domain of `e : equiv.perm α` to one that is over `β` via `f : α → subtype p`,
where `p : β → Prop`, permuting only the `b : β` that satisfy `p b`.
This can be used to extend the domain across a function `f : α → β`,
keeping everything outside of `set.range f` fixed. For this use-case `equiv` given by `f` can
be constructed by `equiv.of_left_inverse'` or `equiv.of_left_inverse` when there is a known
inverse, or `equiv.of_injective` in the general case.`.
-/
def perm.extend_domain : perm β' :=
(perm_congr f e).subtype_congr (equiv.refl _)

@[simp] lemma perm.extend_domain_apply_image (a : α') :
  e.extend_domain f (f a) = f (e a) :=
by simp [perm.extend_domain]

lemma perm.extend_domain_apply_subtype {b : β'} (h : p b) :
  e.extend_domain f b = f (e (f.symm ⟨b, h⟩)) :=
by simp [perm.extend_domain, h]

lemma perm.extend_domain_apply_not_subtype {b : β'} (h : ¬ p b) :
  e.extend_domain f b = b :=
by simp [perm.extend_domain, h]

@[simp] lemma perm.extend_domain_refl : perm.extend_domain (equiv.refl _) f = equiv.refl _ :=
by simp [perm.extend_domain]

@[simp] lemma perm.extend_domain_symm :
  (e.extend_domain f).symm = perm.extend_domain e.symm f := rfl

lemma perm.extend_domain_trans (e e' : perm α') :
  (e.extend_domain f).trans (e'.extend_domain f) = perm.extend_domain (e.trans e') f :=
by simp [perm.extend_domain, perm_congr_trans]

end

/-- Subtype of the quotient is equivalent to the quotient of the subtype. Let `α` be a setoid with
equivalence relation `~`. Let `p₂` be a predicate on the quotient type `α/~`, and `p₁` be the lift
of this predicate to `α`: `p₁ a ↔ p₂ ⟦a⟧`. Let `~₂` be the restriction of `~` to `{x // p₁ x}`.
Then `{x // p₂ x}` is equivalent to the quotient of `{x // p₁ x}` by `~₂`. -/
def subtype_quotient_equiv_quotient_subtype (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) :
  {x // p₂ x} ≃ quotient s₂ :=
{ to_fun := λ a, quotient.hrec_on a.1 (λ a h, ⟦⟨a, (hp₂ _).2 h⟩⟧)
    (λ a b hab, hfunext (by rw quotient.sound hab)
    (λ h₁ h₂ _, heq_of_eq (quotient.sound ((h _ _).2 hab)))) a.2,
  inv_fun := λ a, quotient.lift_on a (λ a, (⟨⟦a.1⟧, (hp₂ _).1 a.2⟩ : {x // p₂ x}))
    (λ a b hab, subtype.ext_val (quotient.sound ((h _ _).1 hab))),
  left_inv := λ ⟨a, ha⟩, quotient.induction_on a (λ a ha, rfl) ha,
  right_inv := λ a, quotient.induction_on a (λ ⟨a, ha⟩, rfl) }

@[simp] lemma subtype_quotient_equiv_quotient_subtype_mk (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x hx) :
  subtype_quotient_equiv_quotient_subtype p₁ p₂ hp₂ h ⟨⟦x⟧, hx⟩ = ⟦⟨x, (hp₂ _).2 hx⟩⟧ := rfl

@[simp] lemma subtype_quotient_equiv_quotient_subtype_symm_mk (p₁ : α → Prop) [s₁ : setoid α]
  [s₂ : setoid (subtype p₁)] (p₂ : quotient s₁ → Prop) (hp₂ : ∀ a, p₁ a ↔ p₂ ⟦a⟧)
  (h : ∀ x y : subtype p₁, @setoid.r _ s₂ x y ↔ (x : α) ≈ y) (x) :
  (subtype_quotient_equiv_quotient_subtype p₁ p₂ hp₂ h).symm ⟦x⟧ = ⟨⟦x⟧, (hp₂ _).1 x.prop⟩ := rfl

section swap
variable [decidable_eq α]

/-- A helper function for `equiv.swap`. -/
def swap_core (a b r : α) : α :=
if r = a then b
else if r = b then a
else r

theorem swap_core_self (r a : α) : swap_core a a r = r :=
by { unfold swap_core, split_ifs; cc }

theorem swap_core_swap_core (r a b : α) : swap_core a b (swap_core a b r) = r :=
by { unfold swap_core, split_ifs; cc }

theorem swap_core_comm (r a b : α) : swap_core a b r = swap_core b a r :=
by { unfold swap_core, split_ifs; cc }

/-- `swap a b` is the permutation that swaps `a` and `b` and
  leaves other values as is. -/
def swap (a b : α) : perm α :=
⟨swap_core a b, swap_core a b, λr, swap_core_swap_core r a b, λr, swap_core_swap_core r a b⟩

@[simp] theorem swap_self (a : α) : swap a a = equiv.refl _ :=
ext $ λ r, swap_core_self r a

theorem swap_comm (a b : α) : swap a b = swap b a :=
ext $ λ r, swap_core_comm r _ _

theorem swap_apply_def (a b x : α) : swap a b x = if x = a then b else if x = b then a else x :=
rfl

@[simp] theorem swap_apply_left (a b : α) : swap a b a = b :=
if_pos rfl

@[simp] theorem swap_apply_right (a b : α) : swap a b b = a :=
by { by_cases h : b = a; simp [swap_apply_def, h], }

theorem swap_apply_of_ne_of_ne {a b x : α} : x ≠ a → x ≠ b → swap a b x = x :=
by simp [swap_apply_def] {contextual := tt}

@[simp] theorem swap_swap (a b : α) : (swap a b).trans (swap a b) = equiv.refl _ :=
ext $ λ x, swap_core_swap_core _ _ _

@[simp] lemma symm_swap (a b : α) : (swap a b).symm = swap a b := rfl

@[simp] lemma swap_eq_refl_iff {x y : α} : swap x y = equiv.refl _ ↔ x = y :=
begin
  refine ⟨λ h, (equiv.refl _).injective _, λ h, h ▸ (swap_self _)⟩,
  rw [←h, swap_apply_left, h, refl_apply]
end

theorem swap_comp_apply {a b x : α} (π : perm α) :
  π.trans (swap a b) x = if π x = a then b else if π x = b then a else π x :=
by { cases π, refl }

lemma swap_eq_update (i j : α) :
  (equiv.swap i j : α → α) = update (update id j i) i j :=
funext $ λ x, by rw [update_apply _ i j, update_apply _ j i, equiv.swap_apply_def, id.def]

lemma comp_swap_eq_update (i j : α) (f : α → β) :
  f ∘ equiv.swap i j = update (update f j (f i)) i (f j) :=
by rw [swap_eq_update, comp_update, comp_update, comp.right_id]

@[simp] lemma symm_trans_swap_trans [decidable_eq β] (a b : α) (e : α ≃ β) :
  (e.symm.trans (swap a b)).trans e = swap (e a) (e b) :=
equiv.ext (λ x, begin
  have : ∀ a, e.symm x = a ↔ x = e a :=
    λ a, by { rw @eq_comm _ (e.symm x), split; intros; simp * at * },
  simp [swap_apply_def, this],
  split_ifs; simp
end)

@[simp] lemma trans_swap_trans_symm [decidable_eq β] (a b : β)
  (e : α ≃ β) : (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
symm_trans_swap_trans a b e.symm

@[simp] lemma swap_apply_self (i j a : α) :
  swap i j (swap i j a) = a :=
by rw [← equiv.trans_apply, equiv.swap_swap, equiv.refl_apply]

/-- A function is invariant to a swap if it is equal at both elements -/
lemma apply_swap_eq_self {v : α → β} {i j : α} (hv : v i = v j) (k : α) : v (swap i j k) = v k :=
begin
  by_cases hi : k = i, { rw [hi, swap_apply_left, hv] },
  by_cases hj : k = j, { rw [hj, swap_apply_right, hv] },
  rw swap_apply_of_ne_of_ne hi hj,
end

lemma swap_apply_eq_iff {x y z w : α} :
  swap x y z = w ↔ z = swap x y w :=
by rw [apply_eq_iff_eq_symm_apply, symm_swap]

lemma swap_apply_ne_self_iff {a b x : α} : swap a b x ≠ x ↔ a ≠ b ∧ (x = a ∨ x = b) :=
begin
  by_cases hab : a = b,
  { simp [hab] },
  by_cases hax : x = a,
  { simp [hax, eq_comm] },
  by_cases hbx : x = b,
  { simp [hbx] },
  simp [hab, hax, hbx, swap_apply_of_ne_of_ne]
end

namespace perm

@[simp] lemma sum_congr_swap_refl {α β : Sort*} [decidable_eq α] [decidable_eq β] (i j : α) :
  equiv.perm.sum_congr (equiv.swap i j) (equiv.refl β) = equiv.swap (sum.inl i) (sum.inl j) :=
begin
  ext x,
  cases x,
  { simp [sum.map, swap_apply_def],
    split_ifs; refl},
  { simp [sum.map, swap_apply_of_ne_of_ne] },
end

@[simp] lemma sum_congr_refl_swap {α β : Sort*} [decidable_eq α] [decidable_eq β] (i j : β) :
  equiv.perm.sum_congr (equiv.refl α) (equiv.swap i j) = equiv.swap (sum.inr i) (sum.inr j) :=
begin
  ext x,
  cases x,
  { simp [sum.map, swap_apply_of_ne_of_ne] },
  { simp [sum.map, swap_apply_def],
    split_ifs; refl},
end

end perm

/-- Augment an equivalence with a prescribed mapping `f a = b` -/
def set_value (f : α ≃ β) (a : α) (b : β) : α ≃ β :=
(swap a (f.symm b)).trans f

@[simp] theorem set_value_eq (f : α ≃ β) (a : α) (b : β) : set_value f a b a = b :=
by { dsimp [set_value], simp [swap_apply_left] }

end swap

end equiv

lemma plift.eq_up_iff_down_eq {x : plift α} {y : α} : x = plift.up y ↔ x.down = y :=
equiv.plift.eq_symm_apply

lemma function.injective.map_swap {α β : Type*} [decidable_eq α] [decidable_eq β]
  {f : α → β} (hf : function.injective f) (x y z : α) :
  f (equiv.swap x y z) = equiv.swap (f x) (f y) (f z) :=
begin
  conv_rhs { rw equiv.swap_apply_def },
  split_ifs with h₁ h₂,
  { rw [hf h₁, equiv.swap_apply_left] },
  { rw [hf h₂, equiv.swap_apply_right] },
  { rw [equiv.swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)] }
end

namespace equiv

protected lemma exists_unique_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
  (h : ∀{x}, p x ↔ q (f x)) : (∃! x, p x) ↔ ∃! y, q y :=
begin
  split,
  { rintro ⟨a, ha₁, ha₂⟩,
    exact ⟨f a, h.1 ha₁, λ b hb, f.symm_apply_eq.1 (ha₂ (f.symm b) (h.2 (by simpa using hb)))⟩ },
  { rintro ⟨b, hb₁, hb₂⟩,
    exact ⟨f.symm b, h.2 (by simpa using hb₁), λ y hy, (eq_symm_apply f).2 (hb₂ _ (h.1 hy))⟩ }
end

protected lemma exists_unique_congr_left' {p : α → Prop} (f : α ≃ β) :
  (∃! x, p x) ↔ (∃! y, p (f.symm y)) :=
equiv.exists_unique_congr f (λx, by simp)

protected lemma exists_unique_congr_left {p : β → Prop} (f : α ≃ β) :
  (∃! x, p (f x)) ↔ (∃! y, p y) :=
(equiv.exists_unique_congr_left' f.symm).symm

protected lemma forall_congr {p : α → Prop} {q : β → Prop} (f : α ≃ β)
  (h : ∀{x}, p x ↔ q (f x)) : (∀x, p x) ↔ (∀y, q y) :=
begin
  split; intros h₂ x,
  { rw [←f.right_inv x], apply h.mp, apply h₂ },
  apply h.mpr, apply h₂
end
protected lemma forall_congr' {p : α → Prop} {q : β → Prop} (f : α ≃ β)
  (h : ∀{x}, p (f.symm x) ↔ q x) : (∀x, p x) ↔ (∀y, q y) :=
(equiv.forall_congr f.symm (λ x, h.symm)).symm

-- We next build some higher arity versions of `equiv.forall_congr`.
-- Although they appear to just be repeated applications of `equiv.forall_congr`,
-- unification of metavariables works better with these versions.
-- In particular, they are necessary in `equiv_rw`.
-- (Stopping at ternary functions seems reasonable: at least in 1-categorical mathematics,
-- it's rare to have axioms involving more than 3 elements at once.)
universes ua1 ua2 ub1 ub2 ug1 ug2
variables {α₁ : Sort ua1} {α₂ : Sort ua2}
          {β₁ : Sort ub1} {β₂ : Sort ub2}
          {γ₁ : Sort ug1} {γ₂ : Sort ug2}

protected lemma forall₂_congr {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂)
  (eβ : β₁ ≃ β₂) (h : ∀{x y}, p x y ↔ q (eα x) (eβ y)) :
  (∀x y, p x y) ↔ (∀x y, q x y) :=
begin
  apply equiv.forall_congr,
  intros,
  apply equiv.forall_congr,
  intros,
  apply h,
end
protected lemma forall₂_congr' {p : α₁ → β₁ → Prop} {q : α₂ → β₂ → Prop} (eα : α₁ ≃ α₂)
  (eβ : β₁ ≃ β₂) (h : ∀{x y}, p (eα.symm x) (eβ.symm y) ↔ q x y) :
  (∀x y, p x y) ↔ (∀x y, q x y) :=
(equiv.forall₂_congr eα.symm eβ.symm (λ x y, h.symm)).symm

protected lemma forall₃_congr {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
  (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
  (h : ∀{x y z}, p x y z ↔ q (eα x) (eβ y) (eγ z)) : (∀x y z, p x y z) ↔ (∀x y z, q x y z) :=
begin
  apply equiv.forall₂_congr,
  intros,
  apply equiv.forall_congr,
  intros,
  apply h,
end
protected lemma forall₃_congr' {p : α₁ → β₁ → γ₁ → Prop} {q : α₂ → β₂ → γ₂ → Prop}
  (eα : α₁ ≃ α₂) (eβ : β₁ ≃ β₂) (eγ : γ₁ ≃ γ₂)
  (h : ∀{x y z}, p (eα.symm x) (eβ.symm y) (eγ.symm z) ↔ q x y z) :
    (∀x y z, p x y z) ↔ (∀x y z, q x y z) :=
(equiv.forall₃_congr eα.symm eβ.symm eγ.symm (λ x y z, h.symm)).symm

protected lemma forall_congr_left' {p : α → Prop} (f : α ≃ β) :
  (∀x, p x) ↔ (∀y, p (f.symm y)) :=
equiv.forall_congr f (λx, by simp)

protected lemma forall_congr_left {p : β → Prop} (f : α ≃ β) :
  (∀x, p (f x)) ↔ (∀y, p y) :=
(equiv.forall_congr_left' f.symm).symm

protected lemma exists_congr_left {α β} (f : α ≃ β) {p : α → Prop} :
  (∃ a, p a) ↔ (∃ b, p (f.symm b)) :=
⟨λ ⟨a, h⟩, ⟨f a, by simpa using h⟩, λ ⟨b, h⟩, ⟨_, h⟩⟩

section
variables (P : α → Sort w) (e : α ≃ β)

/--
Transport dependent functions through an equivalence of the base space.
-/
@[simps] def Pi_congr_left' : (Π a, P a) ≃ (Π b, P (e.symm b)) :=
{ to_fun := λ f x, f (e.symm x),
  inv_fun := λ f x, begin rw [← e.symm_apply_apply x], exact f (e x)  end,
  left_inv := λ f, funext $ λ x, eq_of_heq ((eq_rec_heq _ _).trans
    (by { dsimp, rw e.symm_apply_apply })),
  right_inv := λ f, funext $ λ x, eq_of_heq ((eq_rec_heq _ _).trans
    (by { rw e.apply_symm_apply })) }

end

section
variables (P : β → Sort w) (e : α ≃ β)

/--
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".
-/
def Pi_congr_left : (Π a, P (e a)) ≃ (Π b, P b) :=
(Pi_congr_left' P e.symm).symm
end

section
variables
  {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : Π a : α, (W a ≃ Z (h₁ a)))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibers.
-/
def Pi_congr : (Π a, W a) ≃ (Π b, Z b) :=
(equiv.Pi_congr_right h₂).trans (equiv.Pi_congr_left _ h₁)

@[simp] lemma coe_Pi_congr_symm :
  ((h₁.Pi_congr h₂).symm : (Π b, Z b) → (Π a, W a)) = λ f a, (h₂ a).symm (f (h₁ a)) :=
rfl

lemma Pi_congr_symm_apply (f : Π b, Z b) :
  (h₁.Pi_congr h₂).symm f = λ a, (h₂ a).symm (f (h₁ a)) :=
rfl

@[simp] lemma Pi_congr_apply_apply (f : Π a, W a) (a : α) :
  h₁.Pi_congr h₂ f (h₁ a) = h₂ a (f a) :=
begin
  change cast _ ((h₂ (h₁.symm (h₁ a))) (f (h₁.symm (h₁ a)))) = (h₂ a) (f a),
  generalize_proofs hZa,
  revert hZa,
  rw h₁.symm_apply_apply a,
  simp,
end

end

section
variables
  {W : α → Sort w} {Z : β → Sort z} (h₁ : α ≃ β) (h₂ : Π b : β, (W (h₁.symm b) ≃ Z b))

/--
Transport dependent functions through
an equivalence of the base spaces and a family
of equivalences of the matching fibres.
-/
def Pi_congr' : (Π a, W a) ≃ (Π b, Z b) :=
(Pi_congr h₁.symm (λ b, (h₂ b).symm)).symm

@[simp] lemma coe_Pi_congr' :
  (h₁.Pi_congr' h₂ : (Π a, W a) → (Π b, Z b)) = λ f b, h₂ b $ f $ h₁.symm b :=
rfl

lemma Pi_congr'_apply (f : Π a, W a) :
  h₁.Pi_congr' h₂ f = λ b, h₂ b $ f $ h₁.symm b :=
rfl

@[simp] lemma Pi_congr'_symm_apply_symm_apply (f : Π b, Z b) (b : β) :
  (h₁.Pi_congr' h₂).symm f (h₁.symm b) = (h₂ b).symm (f b) :=
begin
  change cast _ ((h₂ (h₁ (h₁.symm b))).symm (f (h₁ (h₁.symm b)))) = (h₂ b).symm (f b),
  generalize_proofs hWb,
  revert hWb,
  generalize hb : h₁ (h₁.symm b) = b',
  rw h₁.apply_symm_apply b at hb,
  subst hb,
  simp,
end

end

end equiv

lemma function.injective.swap_apply [decidable_eq α] [decidable_eq β] {f : α → β}
  (hf : function.injective f) (x y z : α) :
  equiv.swap (f x) (f y) (f z) = f (equiv.swap x y z) :=
begin
  by_cases hx : z = x, by simp [hx],
  by_cases hy : z = y, by simp [hy],
  rw [equiv.swap_apply_of_ne_of_ne hx hy, equiv.swap_apply_of_ne_of_ne (hf.ne hx) (hf.ne hy)]
end

lemma function.injective.swap_comp [decidable_eq α] [decidable_eq β] {f : α → β}
  (hf : function.injective f) (x y : α) :
  equiv.swap (f x) (f y) ∘ f = f ∘ equiv.swap x y :=
funext $ λ z, hf.swap_apply _ _ _

/-- If both `α` and `β` are singletons, then `α ≃ β`. -/
def equiv_of_unique_of_unique [unique α] [unique β] : α ≃ β :=
{ to_fun := λ _, default,
  inv_fun := λ _, default,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- If `α` is a singleton, then it is equivalent to any `punit`. -/
def equiv_punit_of_unique [unique α] : α ≃ punit.{v} :=
equiv_of_unique_of_unique

/-- If `α` is a subsingleton, then it is equivalent to `α × α`. -/
def subsingleton_prod_self_equiv {α : Type*} [subsingleton α] : α × α ≃ α :=
{ to_fun := λ p, p.1,
  inv_fun := λ a, (a, a),
  left_inv := λ p, subsingleton.elim _ _,
  right_inv := λ p, subsingleton.elim _ _, }

/-- To give an equivalence between two subsingleton types, it is sufficient to give any two
    functions between them. -/
def equiv_of_subsingleton_of_subsingleton [subsingleton α] [subsingleton β]
  (f : α → β) (g : β → α) : α ≃ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _ }

/-- A nonempty subsingleton type is (noncomputably) equivalent to `punit`. -/
noncomputable
def equiv.punit_of_nonempty_of_subsingleton {α : Sort*} [h : nonempty α] [subsingleton α] :
  α ≃ punit.{v} :=
equiv_of_subsingleton_of_subsingleton
 (λ _, punit.star) (λ _, h.some)

/-- `unique (unique α)` is equivalent to `unique α`. -/
def unique_unique_equiv : unique (unique α) ≃ unique α :=
equiv_of_subsingleton_of_subsingleton (λ h, h.default)
  (λ h, { default := h, uniq := λ _, subsingleton.elim _ _ })

namespace quot

/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
  (eq : ∀a₁ a₂, ra a₁ a₂ ↔ rb (e a₁) (e a₂)) :
  quot ra ≃ quot rb :=
{ to_fun := quot.map e (assume a₁ a₂, (eq a₁ a₂).1),
  inv_fun := quot.map e.symm
    (assume b₁ b₂ h,
     (eq (e.symm b₁) (e.symm b₂)).2
       ((e.apply_symm_apply b₁).symm ▸ (e.apply_symm_apply b₂).symm ▸ h)),
  left_inv := by { rintros ⟨a⟩, dunfold quot.map, simp only [equiv.symm_apply_apply] },
  right_inv := by { rintros ⟨a⟩, dunfold quot.map, simp only [equiv.apply_symm_apply] } }

@[simp]
lemma congr_mk {ra : α → α → Prop} {rb : β → β → Prop} (e : α ≃ β)
  (eq : ∀ (a₁ a₂ : α), ra a₁ a₂ ↔ rb (e a₁) (e a₂)) (a : α) :
  quot.congr e eq (quot.mk ra a) = quot.mk rb (e a) := rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : α → α → Prop} (eq : ∀a₁ a₂, r a₁ a₂ ↔ r' a₁ a₂) :
  quot r ≃ quot r' :=
quot.congr (equiv.refl α) eq

/-- An equivalence `e : α ≃ β` generates an equivalence between the quotient space of `α`
by a relation `ra` and the quotient space of `β` by the image of this relation under `e`. -/
protected def congr_left {r : α → α → Prop} (e : α ≃ β) :
  quot r ≃ quot (λ b b', r (e.symm b) (e.symm b')) :=
@quot.congr α β r (λ b b', r (e.symm b) (e.symm b')) e (λ a₁ a₂, by simp only [e.symm_apply_apply])

end quot

namespace quotient
/-- An equivalence `e : α ≃ β` generates an equivalence between quotient spaces,
if `ra a₁ a₂ ↔ rb (e a₁) (e a₂). -/
protected def congr {ra : setoid α} {rb : setoid β} (e : α ≃ β)
  (eq : ∀a₁ a₂, @setoid.r α ra a₁ a₂ ↔ @setoid.r β rb (e a₁) (e a₂)) :
  quotient ra ≃ quotient rb :=
quot.congr e eq

@[simp]
lemma congr_mk {ra : setoid α} {rb : setoid β} (e : α ≃ β)
  (eq : ∀ (a₁ a₂ : α), setoid.r a₁ a₂ ↔ setoid.r (e a₁) (e a₂)) (a : α):
  quotient.congr e eq (quotient.mk a) = quotient.mk (e a) :=
rfl

/-- Quotients are congruent on equivalences under equality of their relation.
An alternative is just to use rewriting with `eq`, but then computational proofs get stuck. -/
protected def congr_right {r r' : setoid α}
  (eq : ∀a₁ a₂, @setoid.r α r a₁ a₂ ↔ @setoid.r α r' a₁ a₂) : quotient r ≃ quotient r' :=
quot.congr_right eq
end quotient

namespace function

lemma update_comp_equiv {α β α' : Sort*} [decidable_eq α'] [decidable_eq α] (f : α → β) (g : α' ≃ α)
  (a : α) (v : β) :
  update f a v ∘ g = update (f ∘ g) (g.symm a) v :=
by rw [← update_comp_eq_of_injective _ g.injective, g.apply_symm_apply]

lemma update_apply_equiv_apply {α β α' : Sort*} [decidable_eq α'] [decidable_eq α]
  (f : α → β) (g : α' ≃ α) (a : α) (v : β) (a' : α') :
  update f a v (g a') = update (f ∘ g) (g.symm a) v a' :=
congr_fun (update_comp_equiv f g a v) a'

lemma Pi_congr_left'_update [decidable_eq α] [decidable_eq β]
  (P : α → Sort*) (e : α ≃ β) (f : Π a, P a) (b : β) (x : P (e.symm b)) :
  e.Pi_congr_left' P (update f (e.symm b) x) = update (e.Pi_congr_left' P f) b x :=
begin
  ext b',
  rcases eq_or_ne b' b with rfl | h,
  { simp, },
  { simp [h], },
end

lemma Pi_congr_left'_symm_update [decidable_eq α] [decidable_eq β]
  (P : α → Sort*) (e : α ≃ β) (f : Π b, P (e.symm b)) (b : β) (x : P (e.symm b)) :
  (e.Pi_congr_left' P).symm (update f b x) = update ((e.Pi_congr_left' P).symm f) (e.symm b) x :=
by simp [(e.Pi_congr_left' P).symm_apply_eq, Pi_congr_left'_update]

end function
