/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import tactic.split_ifs
import tactic.simpa
import tactic.congr
import algebra.group.to_additive
import data.prod
/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `pi.lean` files elsewhere.
-/

open function

universes u v₁ v₂ v₃
variable {I : Type u}     -- The indexing type
variables {α β γ : Type*}
-- The families of types already equipped with instances
variables {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}
variables (x y : Π i, f i) (i : I)

namespace pi

/-! `1`, `0`, `+`, `*`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive] instance has_one [∀ i, has_one $ f i] :
  has_one (Π i : I, f i) :=
⟨λ _, 1⟩
@[simp, to_additive] lemma one_apply [∀ i, has_one $ f i] : (1 : Π i, f i) i = 1 := rfl

@[to_additive] lemma one_def [Π i, has_one $ f i] : (1 : Π i, f i) = λ i, 1 := rfl

@[simp, to_additive] lemma const_one [has_one β] : const α (1 : β) = 1 := rfl

@[simp, to_additive] lemma one_comp [has_one γ] (x : α → β) : (1 : β → γ) ∘ x = 1 := rfl

@[simp, to_additive] lemma comp_one [has_one β] (x : β → γ) : x ∘ 1 = const α (x 1) := rfl

@[to_additive]
instance has_mul [∀ i, has_mul $ f i] :
  has_mul (Π i : I, f i) :=
⟨λ f g i, f i * g i⟩
@[simp, to_additive] lemma mul_apply [∀ i, has_mul $ f i] : (x * y) i = x i * y i := rfl

@[to_additive] lemma mul_def [Π i, has_mul $ f i] : x * y = λ i, x i * y i := rfl

@[simp, to_additive] lemma const_mul [has_mul β] (a b : β) :
  const α a * const α b = const α (a * b) := rfl

@[to_additive] lemma mul_comp [has_mul γ] (x y : β → γ) (z : α → β) :
  (x * y) ∘ z = x ∘ z * y ∘ z := rfl

@[simp] lemma bit0_apply [Π i, has_add $ f i] : (bit0 x) i = bit0 (x i) := rfl

@[simp] lemma bit1_apply [Π i, has_add $ f i] [Π i, has_one $ f i] : (bit1 x) i = bit1 (x i) := rfl

@[to_additive] instance has_inv [∀ i, has_inv $ f i] :
  has_inv (Π i : I, f i) :=
  ⟨λ f i, (f i)⁻¹⟩
@[simp, to_additive] lemma inv_apply [∀ i, has_inv $ f i] : x⁻¹ i = (x i)⁻¹ := rfl
@[to_additive] lemma inv_def [Π i, has_inv $ f i] : x⁻¹ = λ i, (x i)⁻¹ := rfl

@[to_additive] lemma const_inv [has_inv β] (a : β) : (const α a)⁻¹ = const α a⁻¹ := rfl

@[to_additive] lemma inv_comp [has_inv γ] (x : β → γ) (y : α → β) : x⁻¹ ∘ y = (x ∘ y)⁻¹ := rfl

@[to_additive] instance has_div [Π i, has_div $ f i] :
  has_div (Π i : I, f i) :=
⟨λ f g i, f i / g i⟩
@[simp, to_additive] lemma div_apply [Π i, has_div $ f i] : (x / y) i = x i / y i := rfl
@[to_additive] lemma div_def [Π i, has_div $ f i] : x / y = λ i, x i / y i := rfl

@[to_additive] lemma div_comp [has_div γ] (x y : β → γ) (z : α → β) :
  (x / y) ∘ z = x ∘ z / y ∘ z := rfl

@[simp, to_additive] lemma const_div [has_div β] (a b : β) :
  const α a / const α b = const α (a / b) := rfl

section

variables [decidable_eq I]
variables [Π i, has_one (f i)] [Π i, has_one (g i)] [Π i, has_one (h i)]

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive pi.single "The function supported at `i`, with value `x` there, and `0` elsewhere." ]
def mul_single (i : I) (x : f i) : Π i, f i :=
function.update 1 i x

@[simp, to_additive]
lemma mul_single_eq_same (i : I) (x : f i) : mul_single i x i = x :=
function.update_same i x _

@[simp, to_additive]
lemma mul_single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : mul_single i x i' = 1 :=
function.update_noteq h x _

/-- Abbreviation for `mul_single_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[simp, to_additive "Abbreviation for `single_eq_of_ne h.symm`, for ease of
use by `simp`."]
lemma mul_single_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : mul_single i x i' = 1 :=
mul_single_eq_of_ne h.symm x

@[simp, to_additive]
lemma mul_single_one (i : I) : mul_single i (1 : f i) = 1 :=
function.update_eq_self _ _

/-- On non-dependent functions, `pi.mul_single` can be expressed as an `ite` -/
@[to_additive "On non-dependent functions, `pi.single` can be expressed as an `ite`"]
lemma mul_single_apply {β : Sort*} [has_one β] (i : I) (x : β) (i' : I) :
  mul_single i x i' = if i' = i then x else 1 :=
function.update_apply 1 i x i'

/-- On non-dependent functions, `pi.mul_single` is symmetric in the two indices. -/
@[to_additive "On non-dependent functions, `pi.single` is symmetric in the two
indices."]
lemma mul_single_comm {β : Sort*} [has_one β] (i : I) (x : β) (i' : I) :
  mul_single i x i' = mul_single i' x i :=
by simp [mul_single_apply, eq_comm]

@[to_additive]
lemma apply_mul_single (f' : Π i, f i → g i) (hf' : ∀ i, f' i 1 = 1) (i : I) (x : f i) (j : I):
  f' j (mul_single i x j) = mul_single i (f' i x) j :=
by simpa only [pi.one_apply, hf', mul_single] using function.apply_update f' 1 i x j

@[to_additive apply_single₂]
lemma apply_mul_single₂ (f' : Π i, f i → g i → h i) (hf' : ∀ i, f' i 1 1 = 1)
  (i : I) (x : f i) (y : g i) (j : I):
  f' j (mul_single i x j) (mul_single i y j) = mul_single i (f' i x y) j :=
begin
  by_cases h : j = i,
  { subst h, simp only [mul_single_eq_same] },
  { simp only [mul_single_eq_of_ne h, hf'] },
end

@[to_additive]
lemma mul_single_op {g : I → Type*} [Π i, has_one (g i)] (op : Π i, f i → g i) (h : ∀ i, op i 1 = 1)
  (i : I) (x : f i) :
  mul_single i (op i x) = λ j, op j (mul_single i x j) :=
eq.symm $ funext $ apply_mul_single op h i x

@[to_additive]
lemma mul_single_op₂ {g₁ g₂ : I → Type*} [Π i, has_one (g₁ i)] [Π i, has_one (g₂ i)]
  (op : Π i, g₁ i → g₂ i → f i) (h : ∀ i, op i 1 1 = 1) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
  mul_single i (op i x₁ x₂) = λ j, op j (mul_single i x₁ j) (mul_single i x₂ j) :=
eq.symm $ funext $ apply_mul_single₂ op h i x₁ x₂

variables (f)

@[to_additive]
lemma mul_single_injective (i : I) : function.injective (mul_single i : f i → Π i, f i) :=
function.update_injective _ i

@[simp, to_additive]
lemma mul_single_inj (i : I) {x y : f i} : mul_single i x = mul_single i y ↔ x = y :=
(pi.mul_single_injective _ _).eq_iff

end

/-- The mapping into a product type built from maps into each component. -/
@[simp] protected def prod (f' : Π i, f i) (g' : Π i, g i) (i : I) : f i × g i := (f' i, g' i)

@[simp] lemma prod_fst_snd : pi.prod (prod.fst : α × β → α) (prod.snd : α × β → β) = id :=
funext $ λ _, prod.mk.eta

@[simp] lemma prod_snd_fst : pi.prod (prod.snd : α × β → β) (prod.fst : α × β → α) = prod.swap :=
rfl

end pi

namespace function

section extend
@[to_additive]
lemma extend_one [has_one γ] (f : α → β) :
  function.extend f (1 : α → γ) (1 : β → γ) = 1 :=
funext $ λ _, by apply if_t_t _ _

@[to_additive]
lemma extend_mul [has_mul γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
  function.extend f (g₁ * g₂) (e₁ * e₂) = function.extend f g₁ e₁ * function.extend f g₂ e₂ :=
funext $ λ _, by convert (apply_dite2 (*) _ _ _ _ _).symm

@[to_additive]
lemma extend_inv [has_inv γ] (f : α → β) (g : α → γ) (e : β → γ) :
  function.extend f (g⁻¹) (e⁻¹) = (function.extend f g e)⁻¹ :=
funext $ λ _, by convert (apply_dite has_inv.inv _ _ _).symm

@[to_additive]
lemma extend_div [has_div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
  function.extend f (g₁ / g₂) (e₁ / e₂) = function.extend f g₁ e₁ / function.extend f g₂ e₂ :=
funext $ λ _, by convert (apply_dite2 (/) _ _ _ _ _).symm

end extend

lemma surjective_pi_map {F : Π i, f i → g i} (hF : ∀ i, surjective (F i)) :
  surjective (λ x : Π i, f i, λ i, F i (x i)) :=
λ y, ⟨λ i, (hF i (y i)).some, funext $ λ i, (hF i (y i)).some_spec⟩

lemma injective_pi_map {F : Π i, f i → g i} (hF : ∀ i, injective (F i)) :
  injective (λ x : Π i, f i, λ i, F i (x i)) :=
λ x y h, funext $ λ i, hF i $ (congr_fun h i : _)

lemma bijective_pi_map {F : Π i, f i → g i} (hF : ∀ i, bijective (F i)) :
  bijective (λ x : Π i, f i, λ i, F i (x i)) :=
⟨injective_pi_map (λ i, (hF i).injective), surjective_pi_map (λ i, (hF i).surjective)⟩

end function

@[to_additive subsingleton.pi_single_eq]
lemma subsingleton.pi_mul_single_eq {α : Type*} [decidable_eq I] [subsingleton I] [has_one α]
  (i : I) (x : α) :
  pi.mul_single i x = λ _, x :=
funext $ λ j, by rw [subsingleton.elim j i, pi.mul_single_eq_same]
