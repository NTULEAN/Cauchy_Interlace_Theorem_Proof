/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import data.equiv.basic
import data.fun_like.embedding
import data.pprod
import data.set.basic
import data.sigma.basic

/-!
# Injective functions
-/

universes u v w x

namespace function

/-- `α ↪ β` is a bundled injective function. -/
@[nolint has_inhabited_instance] -- depending on cardinalities, an injective function may not exist
structure embedding (α : Sort*) (β : Sort*) :=
(to_fun : α → β)
(inj'   : injective to_fun)

infixr ` ↪ `:25 := embedding

instance {α : Sort u} {β : Sort v} : has_coe_to_fun (α ↪ β) (λ _, α → β) := ⟨embedding.to_fun⟩

initialize_simps_projections embedding (to_fun → apply)

instance {α : Sort u} {β : Sort v} : embedding_like (α ↪ β) α β :=
{ coe := embedding.to_fun,
  injective' := embedding.inj',
  coe_injective' := λ f g h, by { cases f, cases g, congr' } }

end function

section equiv

variables {α : Sort u} {β : Sort v} (f : α ≃ β)

/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `equiv.coe_embedding`.
The explicit `equiv.to_embedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f.to_embedding = s.map f := by simp
-- Error, `f` has type `fin 3 ≃ fin 3` but is expected to have type `fin 3 ↪ ?m_1 : Type ?`
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f = s.map f.to_embedding := by simp
```
-/
@[simps] protected def equiv.to_embedding : α ↪ β := ⟨f, f.injective⟩

instance equiv.coe_embedding : has_coe (α ≃ β) (α ↪ β) := ⟨equiv.to_embedding⟩

@[reducible]
instance equiv.perm.coe_embedding : has_coe (equiv.perm α) (α ↪ α) := equiv.coe_embedding

@[simp] lemma equiv.coe_eq_to_embedding  : ↑f = f.to_embedding := rfl

/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps]
def equiv.as_embedding {p : β → Prop} (e : α ≃ subtype p) : α ↪ β :=
⟨coe ∘ e, subtype.coe_injective.comp e.injective⟩

@[simp]
lemma equiv.as_embedding_range {α β : Sort*} {p : β → Prop} (e : α ≃ subtype p) :
  set.range e.as_embedding = set_of p :=
set.ext $ λ x, ⟨λ ⟨y, h⟩, h ▸ subtype.coe_prop (e y), λ hs, ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

end equiv

namespace function
namespace embedding

lemma coe_injective {α β} : @function.injective (α ↪ β) (α → β) coe_fn := fun_like.coe_injective

@[ext] lemma ext {α β} {f g : embedding α β} (h : ∀ x, f x = g x) : f = g := fun_like.ext f g h

lemma ext_iff {α β} {f g : embedding α β} : (∀ x, f x = g x) ↔ f = g := fun_like.ext_iff.symm

@[simp] theorem to_fun_eq_coe {α β} (f : α ↪ β) : to_fun f = f := rfl

@[simp] theorem coe_fn_mk {α β} (f : α → β) (i) :
  (@mk _ _ f i : α → β) = f := rfl

@[simp] lemma mk_coe {α β : Type*} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f :=
by { ext, simp }

protected theorem injective {α β} (f : α ↪ β) : injective f := embedding_like.injective f

lemma apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
embedding_like.apply_eq_iff_eq f

/-- The identity map as a `function.embedding`. -/
@[refl, simps {simp_rhs := tt}]
protected def refl (α : Sort*) : α ↪ α :=
⟨id, injective_id⟩

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps {simp_rhs := tt}]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
⟨g ∘ f, g.injective.comp f.injective⟩

@[simp]
lemma equiv_to_embedding_trans_symm_to_embedding {α β : Sort*} (e : α ≃ β) :
  e.to_embedding.trans e.symm.to_embedding = embedding.refl _ :=
by { ext, simp, }

@[simp]
lemma equiv_symm_to_embedding_trans_to_embedding {α β : Sort*} (e : α ≃ β) :
  e.symm.to_embedding.trans e.to_embedding = embedding.refl _ :=
by { ext, simp, }

/-- Transfer an embedding along a pair of equivalences. -/
@[simps { fully_applied := ff }]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}
  (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ) : (β ↪ δ) :=
(equiv.to_embedding e₁.symm).trans (f.trans e₂.to_embedding)

/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected noncomputable def of_surjective {α β} (f : β → α) (hf : surjective f) :
  α ↪ β :=
⟨surj_inv hf, injective_surj_inv _⟩

/-- Convert a surjective `embedding` to an `equiv` -/
protected noncomputable def equiv_of_surjective {α β} (f : α ↪ β) (hf : surjective f) :
  α ≃ β :=
equiv.of_bijective f ⟨f.injective, hf⟩

/-- There is always an embedding from an empty type. --/
protected def of_is_empty {α β} [is_empty α] : α ↪ β :=
⟨is_empty_elim, is_empty_elim⟩

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def set_value {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', decidable (a' = a)]
  [∀ a', decidable (f a' = b)] : α ↪ β :=
⟨λ a', if a' = a then b else if f a' = b then f a else f a',
  begin
    intros x y h,
    dsimp at h,
    split_ifs at h; try { substI b }; try { simp only [f.injective.eq_iff] at * }; cc
  end⟩

theorem set_value_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', decidable (a' = a)]
  [∀ a', decidable (f a' = b)] : set_value f a b a = b :=
by simp [set_value]

/-- Embedding into `option α` using `some`. -/
@[simps { fully_applied := ff }] protected def some {α} : α ↪ option α :=
⟨some, option.some_injective α⟩

/-- Embedding into `option α` using `coe`. Usually the correct synctatical form for `simp`. -/
@[simps { fully_applied := ff }]
def coe_option {α} : α ↪ option α := ⟨coe, option.some_injective α⟩

/-- Embedding into `with_top α`. -/
@[simps]
def coe_with_top {α} : α ↪ with_top α := { to_fun := coe, ..embedding.some}

/-- Given an embedding `f : α ↪ β` and a point outside of `set.range f`, construct an embedding
`option α ↪ β`. -/
@[simps] def option_elim {α β} (f : α ↪ β) (x : β) (h : x ∉ set.range f) :
  option α ↪ β :=
⟨λ o, o.elim x f, option.injective_iff.2 ⟨f.2, h⟩⟩

/-- Embedding of a `subtype`. -/
def subtype {α} (p : α → Prop) : subtype p ↪ α :=
⟨coe, λ _ _, subtype.ext_val⟩

@[simp] lemma coe_subtype {α} (p : α → Prop) : ⇑(subtype p) = coe := rfl

/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def punit {β : Sort*} (b : β) : punit ↪ β :=
⟨λ _, b, by { rintros ⟨⟩ ⟨⟩ _, refl, }⟩

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
def sectl (α : Sort*) {β : Sort*} (b : β) : α ↪ α × β :=
⟨λ a, (a, b), λ a a' h, congr_arg prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
def sectr {α : Sort*} (a : α) (β : Sort*): β ↪ α × β :=
⟨λ b, (a, b), λ b b' h, congr_arg prod.snd h⟩

/-- Restrict the codomain of an embedding. -/
def cod_restrict {α β} (p : set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
⟨λ a, ⟨f a, H a⟩, λ a b h, f.injective (@congr_arg _ _ _ _ subtype.val h)⟩

@[simp] theorem cod_restrict_apply {α β} (p) (f : α ↪ β) (H a) :
  cod_restrict p f H a = ⟨f a, H a⟩ := rfl

/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prod_map {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
⟨prod.map e₁ e₂, e₁.injective.prod_map e₂.injective⟩

@[simp] lemma coe_prod_map {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
  ⇑(e₁.prod_map e₂) = prod.map e₁ e₂ :=
rfl

/-- If `e₁` and `e₂` are embeddings, then so is `λ ⟨a, b⟩, ⟨e₁ a, e₂ b⟩ : pprod α γ → pprod β δ`. -/
def pprod_map {α β γ δ : Sort*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : pprod α γ ↪ pprod β δ :=
⟨λ x, ⟨e₁ x.1, e₂ x.2⟩, e₁.injective.pprod_map e₂.injective⟩

section sum
open sum

/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sum_map {α β γ δ : Type*} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α ⊕ γ ↪ β ⊕ δ :=
⟨sum.map e₁ e₂,
    assume s₁ s₂ h, match s₁, s₂, h with
    | inl a₁, inl a₂, h := congr_arg inl $ e₁.injective $ inl.inj h
    | inr b₁, inr b₂, h := congr_arg inr $ e₂.injective $ inr.inj h
    end⟩

@[simp] theorem coe_sum_map {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) :
  ⇑(sum_map e₁ e₂) = sum.map e₁ e₂ :=
rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps] def inl {α β : Type*} : α ↪ α ⊕ β :=
⟨sum.inl, λ a b, sum.inl.inj⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps] def inr {α β : Type*} : β ↪ α ⊕ β :=
⟨sum.inr, λ a b, sum.inr.inj⟩

end sum

section sigma

variables {α α' : Type*} {β : α → Type*} {β' : α' → Type*}

/-- `sigma.mk` as an `function.embedding`. -/
@[simps apply] def sigma_mk (a : α) : β a ↪ Σ x, β x :=
⟨sigma.mk a, sigma_mk_injective⟩

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simps apply] def sigma_map (f : α ↪ α') (g : Π a, β a ↪ β' (f a)) :
  (Σ a, β a) ↪ Σ a', β' a' :=
⟨sigma.map f (λ a, g a), f.injective.sigma_map (λ a, (g a).injective)⟩

end sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `λ a, e a (f a)`. -/
@[simps] def Pi_congr_right {α : Sort*} {β γ : α → Sort*} (e : ∀ a, β a ↪ γ a) :
  (Π a, β a) ↪ (Π a, γ a) :=
⟨λf a, e a (f a), λ f₁ f₂ h, funext $ λ a, (e a).injective (congr_fun h a)⟩

/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrow_congr_right {α : Sort u} {β : Sort v} {γ : Sort w}
  (e : α ↪ β) : (γ → α) ↪ (γ → β) :=
Pi_congr_right (λ _, e)

@[simp] lemma arrow_congr_right_apply {α : Sort u} {β : Sort v} {γ : Sort w}
  (e : α ↪ β) (f : γ ↪ α) : arrow_congr_right e f = e ∘ f := rfl

/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrow_congr_left {α : Sort u} {β : Sort v} {γ : Sort w} [inhabited γ]
  (e : α ↪ β) : (α → γ) ↪ (β → γ) :=
⟨λ f, extend e f (λ _, default), λ f₁ f₂ h, funext $ λ x,
  by simpa only [extend_apply e.injective] using congr_fun h (e x)⟩

/-- Restrict both domain and codomain of an embedding. -/
protected def subtype_map {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β)
  (h : ∀{{x}}, p x → q (f x)) : {x : α // p x} ↪ {y : β // q y} :=
⟨subtype.map f h, subtype.map_injective h f.2⟩

open set

/-- `set.image` as an embedding `set α ↪ set β`. -/
@[simps apply] protected def image {α β} (f : α ↪ β) : set α ↪ set β :=
⟨image f, f.2.image_injective⟩

lemma swap_apply {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α ↪ β) (x y z : α) :
  equiv.swap (f x) (f y) (f z) = f (equiv.swap x y z) :=
f.injective.swap_apply x y z

lemma swap_comp {α β : Type*} [decidable_eq α] [decidable_eq β] (f : α ↪ β) (x y : α) :
  equiv.swap (f x) (f y) ∘ f = f ∘ equiv.swap x y :=
f.injective.swap_comp x y

end embedding
end function

namespace equiv

open function.embedding

/-- The type of embeddings `α ↪ β` is equivalent to
    the subtype of all injective functions `α → β`. -/
def subtype_injective_equiv_embedding (α β : Sort*) :
  {f : α → β // function.injective f} ≃ (α ↪ β) :=
{ to_fun := λ f, ⟨f.val, f.property⟩,
  inv_fun := λ f, ⟨f, f.injective⟩,
  left_inv := λ f, by simp,
  right_inv := λ f, by {ext, refl} }

/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[congr, simps apply] def embedding_congr {α β γ δ : Sort*}
  (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) :=
{ to_fun := λ f, f.congr h h',
  inv_fun := λ f, f.congr h.symm h'.symm,
  left_inv := λ x, by {ext, simp},
  right_inv := λ x, by {ext, simp} }

@[simp] lemma embedding_congr_refl {α β : Sort*} :
  embedding_congr (equiv.refl α) (equiv.refl β) = equiv.refl (α ↪ β) :=
by {ext, refl}

@[simp] lemma embedding_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort*}
  (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃) (e₂' : β₂ ≃ β₃) :
  embedding_congr (e₁.trans e₂) (e₁'.trans e₂') =
  (embedding_congr e₁ e₁').trans (embedding_congr e₂ e₂') :=
rfl

@[simp] lemma embedding_congr_symm {α₁ β₁ α₂ β₂ : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
  (embedding_congr e₁ e₂).symm = embedding_congr e₁.symm e₂.symm :=
rfl

lemma embedding_congr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort*}
  (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂) (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
  equiv.embedding_congr ea ec (f.trans g) =
  (equiv.embedding_congr ea eb f).trans (equiv.embedding_congr eb ec g) :=
by {ext, simp}

@[simp]
lemma refl_to_embedding {α : Type*} : (equiv.refl α).to_embedding = function.embedding.refl α := rfl

@[simp]
lemma trans_to_embedding {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
  (e.trans f).to_embedding = e.to_embedding.trans f.to_embedding := rfl

end equiv

namespace set

/-- The injection map is an embedding between subsets. -/
@[simps apply] def embedding_of_subset {α} (s t : set α) (h : s ⊆ t) : s ↪ t :=
⟨λ x, ⟨x.1, h x.2⟩, λ ⟨x, hx⟩ ⟨y, hy⟩ h, by { congr, injection h }⟩

end set

section subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtype_or_left_embedding (p q : α → Prop) [decidable_pred p] :
  {x // p x ∨ q x} ↪ {x // p x} ⊕ {x // q x} :=
⟨λ x, if h : p x then sum.inl ⟨x, h⟩ else sum.inr ⟨x, x.prop.resolve_left h⟩,
  begin
    intros x y,
    dsimp only,
    split_ifs;
    simp [subtype.ext_iff]
  end⟩

lemma subtype_or_left_embedding_apply_left {p q : α → Prop} [decidable_pred p]
  (x : {x // p x ∨ q x}) (hx : p x) : subtype_or_left_embedding p q x = sum.inl ⟨x, hx⟩ :=
dif_pos hx

lemma subtype_or_left_embedding_apply_right {p q : α → Prop} [decidable_pred p]
  (x : {x // p x ∨ q x}) (hx : ¬ p x) :
  subtype_or_left_embedding p q x = sum.inr ⟨x, x.prop.resolve_left hx⟩ :=
dif_neg hx

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps] def subtype.imp_embedding (p q : α → Prop) (h : p ≤ q) :
  {x // p x} ↪ {x // q x} :=
⟨λ x, ⟨x, h x x.prop⟩, λ x y, by simp [subtype.ext_iff]⟩

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`disjoint p q`.

See also `equiv.sum_compl`, for when `is_compl p q`.  -/
@[simps apply] def subtype_or_equiv (p q : α → Prop) [decidable_pred p] (h : disjoint p q) :
  {x // p x ∨ q x} ≃ {x // p x} ⊕ {x // q x} :=
{ to_fun := subtype_or_left_embedding p q,
  inv_fun := sum.elim
    (subtype.imp_embedding _ _ (λ x hx, (or.inl hx : p x ∨ q x)))
    (subtype.imp_embedding _ _ (λ x hx, (or.inr hx : p x ∨ q x))),
  left_inv := λ x, begin
    by_cases hx : p x,
    { rw subtype_or_left_embedding_apply_left _ hx,
      simp [subtype.ext_iff] },
    { rw subtype_or_left_embedding_apply_right _ hx,
      simp [subtype.ext_iff] },
  end,
  right_inv := λ x, begin
    cases x,
    { simp only [sum.elim_inl],
      rw subtype_or_left_embedding_apply_left,
      { simp },
      { simpa using x.prop } },
    { simp only [sum.elim_inr],
      rw subtype_or_left_embedding_apply_right,
      { simp },
      { suffices : ¬ p x,
        { simpa },
        intro hp,
        simpa using h x ⟨hp, x.prop⟩ } }
  end }

@[simp] lemma subtype_or_equiv_symm_inl (p q : α → Prop) [decidable_pred p] (h : disjoint p q)
  (x : {x // p x}) : (subtype_or_equiv p q h).symm (sum.inl x) = ⟨x, or.inl x.prop⟩ :=
rfl

@[simp] lemma subtype_or_equiv_symm_inr (p q : α → Prop) [decidable_pred p] (h : disjoint p q)
  (x : {x // q x}) : (subtype_or_equiv p q h).symm (sum.inr x) = ⟨x, or.inr x.prop⟩ :=
rfl

end subtype
