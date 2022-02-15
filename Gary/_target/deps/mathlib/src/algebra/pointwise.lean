/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.big_operators.basic
import algebra.module.basic
import data.finset.preimage
import data.set.finite
import group_theory.submonoid.basic

/-!
# Pointwise addition, multiplication, scalar multiplication and vector subtraction of sets.

This file defines pointwise algebraic operations on sets.
* For a type `α` with multiplication, multiplication is defined on `set α` by taking
  `s * t` to be the set of all `x * y` where `x ∈ s` and `y ∈ t`. Similarly for addition.
* For `α` a semigroup, `set α` is a semigroup.
* If `α` is a (commutative) monoid, we define an alias `set_semiring α` for `set α`, which then
  becomes a (commutative) semiring with union as addition and pointwise multiplication as
  multiplication.
* For a type `β` with scalar multiplication by another type `α`, this
  file defines a scalar multiplication of `set β` by `set α` and a separate scalar
  multiplication of `set β` by `α`.
* We also define pointwise multiplication on `finset`.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes
* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication,
pointwise subtraction
-/

open function

variables {α β γ : Type*}

namespace set

/-! ### Properties about 1 -/

section one
variables [has_one α] {s : set α} {a : α}

/-- The set `(1 : set α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive
/-"The set `(0 : set α)` is defined as `{0}` in locale `pointwise`. "-/]
protected def has_one : has_one (set α) := ⟨{1}⟩

localized "attribute [instance] set.has_one set.has_zero" in pointwise

@[to_additive]
lemma singleton_one : ({1} : set α) = 1 := rfl

@[simp, to_additive]
lemma mem_one : a ∈ (1 : set α) ↔ a = 1 := iff.rfl

@[to_additive]
lemma one_mem_one : (1 : α) ∈ (1 : set α) := eq.refl _

@[simp, to_additive]
lemma one_subset : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

@[to_additive]
lemma one_nonempty : (1 : set α).nonempty := ⟨1, rfl⟩

@[simp, to_additive]
lemma image_one {f : α → β} : f '' 1 = {f 1} := image_singleton

end one

open_locale pointwise

/-! ### Properties about multiplication -/

section mul
variables {s s₁ s₂ t t₁ t₂ u : set α} {a b : α}

/-- The set `(s * t : set α)` is defined as `{x * y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[to_additive
/-" The set `(s + t : set α)` is defined as `{x + y | x ∈ s, y ∈ t}` in locale `pointwise`."-/]
protected def has_mul [has_mul α] : has_mul (set α) := ⟨image2 has_mul.mul⟩

localized "attribute [instance] set.has_mul set.has_add" in pointwise

section has_mul
variables {ι : Sort*} {κ : ι → Sort*} [has_mul α]

@[simp, to_additive]
lemma image2_mul : image2 has_mul.mul s t = s * t := rfl

@[to_additive]
lemma mem_mul : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a := iff.rfl

@[to_additive]
lemma mul_mem_mul (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t := mem_image2_of_mem ha hb

@[to_additive]
lemma mul_subset_mul (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ * s₂ ⊆ t₁ * t₂ := image2_subset h₁ h₂

@[to_additive add_image_prod]
lemma image_mul_prod : (λ x : α × α, x.fst * x.snd) '' (s ×ˢ t) = s * t := image_prod _

@[simp, to_additive] lemma empty_mul : ∅ * s = ∅ := image2_empty_left
@[simp, to_additive] lemma mul_empty : s * ∅ = ∅ := image2_empty_right

@[simp, to_additive] lemma mul_singleton : s * {b} = (* b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_mul : {a} * t = ((*) a) '' t := image2_singleton_left

@[simp, to_additive]
lemma singleton_mul_singleton : ({a} : set α) * {b} = {a * b} := image2_singleton

@[to_additive] lemma mul_subset_mul_left (h : t₁ ⊆ t₂) : s * t₁ ⊆ s * t₂ := image2_subset_left h
@[to_additive] lemma mul_subset_mul_right (h : s₁ ⊆ s₂) : s₁ * t ⊆ s₂ * t := image2_subset_right h

@[to_additive] lemma union_mul : (s₁ ∪ s₂) * t = s₁ * t ∪ s₂ * t := image2_union_left
@[to_additive] lemma mul_union : s * (t₁ ∪ t₂) = s * t₁ ∪ s * t₂ := image2_union_right

@[to_additive]
lemma inter_mul_subset : (s₁ ∩ s₂) * t ⊆ s₁ * t ∩ (s₂ * t) := image2_inter_subset_left

@[to_additive]
lemma mul_inter_subset : s * (t₁ ∩ t₂) ⊆ s * t₁ ∩ (s * t₂) := image2_inter_subset_right

@[to_additive]
lemma Union_mul_left_image : (⋃ a ∈ s, (λ x, a * x) '' t) = s * t := Union_image_left _

@[to_additive]
lemma Union_mul_right_image : (⋃ a ∈ t, (λ x, x * a) '' s) = s * t := Union_image_right _

@[to_additive]
lemma Union_mul (s : ι → set α) (t : set α) : (⋃ i, s i) * t = ⋃ i, s i * t :=
image2_Union_left _ _ _

@[to_additive]
lemma mul_Union (s : set α) (t : ι → set α) : s * (⋃ i, t i) = ⋃ i, s * t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_mul (s : Π i, κ i → set α) (t : set α) : (⋃ i j, s i j) * t = ⋃ i j, s i j * t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma mul_Union₂ (s : set α) (t : Π i, κ i → set α) : s * (⋃ i j, t i j) = ⋃ i j, s * t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_mul_subset (s : ι → set α) (t : set α) : (⋂ i, s i) * t ⊆ ⋂ i, s i * t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma mul_Inter_subset (s : set α) (t : ι → set α) : s * (⋂ i, t i) ⊆ ⋂ i, s * t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_mul_subset (s : Π i, κ i → set α) (t : set α) :
  (⋂ i j, s i j) * t ⊆ ⋂ i j, s i j * t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma mul_Inter₂_subset (s : set α) (t : Π i, κ i → set α) :
  s * (⋂ i j, t i j) ⊆ ⋂ i j, s * t i j :=
image2_Inter₂_subset_right _ _ _

/-- Under `[has_mul M]`, the `singleton` map from `M` to `set M` as a `mul_hom`, that is, a map
which preserves multiplication. -/
@[to_additive "Under `[has_add A]`, the `singleton` map from `A` to `set A` as an `add_hom`,
that is, a map which preserves addition.", simps]
def singleton_mul_hom : mul_hom α (set α) :=
{ to_fun := singleton,
  map_mul' := λ a b, singleton_mul_singleton.symm }

end has_mul

@[simp, to_additive]
lemma image_mul_left [group α] : ((*) a) '' t = ((*) a⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[simp, to_additive]
lemma image_mul_right [group α] : (* b) '' t = (* b⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[to_additive]
lemma image_mul_left' [group α] : (λ b, a⁻¹ * b) '' t = (λ b, a * b) ⁻¹' t := by simp

@[to_additive]
lemma image_mul_right' [group α] : (* b⁻¹) '' t = (* b) ⁻¹' t := by simp

@[simp, to_additive]
lemma preimage_mul_left_singleton [group α] : ((*) a) ⁻¹' {b} = {a⁻¹ * b} :=
by rw [← image_mul_left', image_singleton]

@[simp, to_additive]
lemma preimage_mul_right_singleton [group α] : (* a) ⁻¹' {b} = {b * a⁻¹} :=
by rw [← image_mul_right', image_singleton]

@[simp, to_additive]
lemma preimage_mul_left_one [group α] : ((*) a) ⁻¹' 1 = {a⁻¹} :=
by rw [← image_mul_left', image_one, mul_one]

@[simp, to_additive]
lemma preimage_mul_right_one [group α] : (* b) ⁻¹' 1 = {b⁻¹} :=
by rw [← image_mul_right', image_one, one_mul]

@[to_additive]
lemma preimage_mul_left_one' [group α] : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp

@[to_additive]
lemma preimage_mul_right_one' [group α] : (* b⁻¹) ⁻¹' 1 = {b} := by simp

@[to_additive]
protected lemma mul_comm [comm_semigroup α] : s * t = t * s :=
by simp only [← image2_mul, image2_swap _ s, mul_comm]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_zero_class` under pointwise operations if `α` is."-/]
protected def mul_one_class [mul_one_class α] : mul_one_class (set α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..set.has_one, ..set.has_mul }

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_semigroup` under pointwise operations if `α` is. "-/]
protected def semigroup [semigroup α] : semigroup (set α) :=
{ mul_assoc := λ _ _ _, image2_assoc mul_assoc,
  ..set.has_mul }

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_monoid` under pointwise operations if `α` is. "-/]
protected def monoid [monoid α] : monoid (set α) :=
{ ..set.semigroup,
  ..set.mul_one_class }

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_comm_monoid` under pointwise operations if `α` is. "-/]
protected def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
{ mul_comm := λ _ _, set.mul_comm, ..set.monoid }

localized "attribute [instance] set.mul_one_class set.add_zero_class set.semigroup set.add_semigroup
  set.monoid set.add_monoid set.comm_monoid set.add_comm_monoid" in pointwise

@[to_additive nsmul_mem_nsmul]
lemma pow_mem_pow [monoid α] (ha : a ∈ s) (n : ℕ) :
  a ^ n ∈ s ^ n :=
begin
  induction n with n ih,
  { rw pow_zero,
    exact set.mem_singleton 1 },
  { rw pow_succ,
    exact set.mul_mem_mul ha ih },
end

@[to_additive empty_nsmul]
lemma empty_pow [monoid α] (n : ℕ) (hn : n ≠ 0) : (∅ : set α) ^ n = ∅ :=
by rw [← tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

instance decidable_mem_mul [monoid α] [fintype α] [decidable_eq α]
  [decidable_pred (∈ s)] [decidable_pred (∈ t)] :
  decidable_pred (∈ s * t) :=
λ _, decidable_of_iff _ mem_mul.symm

instance decidable_mem_pow [monoid α] [fintype α] [decidable_eq α]
  [decidable_pred (∈ s)] (n : ℕ) :
  decidable_pred (∈ (s ^ n)) :=
begin
  induction n with n ih,
  { simp_rw [pow_zero, mem_one], apply_instance },
  { letI := ih, rw pow_succ, apply_instance }
end

@[to_additive]
lemma subset_mul_left [mul_one_class α] (s : set α) {t : set α} (ht : (1 : α) ∈ t) : s ⊆ s * t :=
λ x hx, ⟨x, 1, hx, ht, mul_one _⟩

@[to_additive]
lemma subset_mul_right [mul_one_class α] {s : set α} (t : set α) (hs : (1 : α) ∈ s) : t ⊆ s * t :=
λ x hx, ⟨1, x, hs, hx, one_mul _⟩

lemma pow_subset_pow [monoid α] (hst : s ⊆ t) (n : ℕ) :
  s ^ n ⊆ t ^ n :=
begin
  induction n with n ih,
  { rw pow_zero,
    exact subset.rfl },
  { rw [pow_succ, pow_succ],
    exact mul_subset_mul hst ih },
end

@[simp, to_additive]
lemma univ_mul_univ [monoid α] : (univ : set α) * univ = univ :=
begin
  have : ∀x, ∃a b : α, a * b = x := λx, ⟨x, ⟨1, mul_one x⟩⟩,
  simpa only [mem_mul, eq_univ_iff_forall, mem_univ, true_and]
end

@[simp, to_additive]
lemma mul_univ [group α] (hs : s.nonempty) : s * (univ : set α) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ * b, ha, trivial, mul_inv_cancel_left _ _⟩

@[simp, to_additive]
lemma univ_mul [group α] (ht : t.nonempty) : (univ : set α) * t = univ :=
let ⟨a, ha⟩ := ht in eq_univ_of_forall $ λ b, ⟨b * a⁻¹, a, trivial, ha, inv_mul_cancel_right _ _⟩

/-- `singleton` is a monoid hom. -/
@[to_additive singleton_add_hom "singleton is an add monoid hom"]
def singleton_hom [monoid α] : α →* set α :=
{ to_fun := singleton, map_one' := rfl, map_mul' := λ a b, singleton_mul_singleton.symm }

@[to_additive]
lemma nonempty.mul [has_mul α] : s.nonempty → t.nonempty → (s * t).nonempty := nonempty.image2

@[to_additive]
lemma finite.mul [has_mul α] (hs : finite s) (ht : finite t) : finite (s * t) :=
hs.image2 _ ht

/-- multiplication preserves finiteness -/
@[to_additive "addition preserves finiteness"]
def fintype_mul [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s * t : set α) :=
set.fintype_image2 _ s t

@[to_additive]
lemma bdd_above_mul [ordered_comm_monoid α] {A B : set α} :
  bdd_above A → bdd_above B → bdd_above (A * B) :=
begin
  rintros ⟨bA, hbA⟩ ⟨bB, hbB⟩,
  use bA * bB,
  rintros x ⟨xa, xb, hxa, hxb, rfl⟩,
  exact mul_le_mul' (hbA hxa) (hbB hxb),
end

end mul

open_locale pointwise

section big_operators
open_locale big_operators

variables {ι : Type*} [comm_monoid α]

/-- The n-ary version of `set.mem_mul`. -/
@[to_additive /-" The n-ary version of `set.mem_add`. "-/]
lemma mem_finset_prod (t : finset ι) (f : ι → set α) (a : α) :
  a ∈ ∏ i in t, f i ↔ ∃ (g : ι → α) (hg : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i in t, g i = a :=
begin
  classical,
  induction t using finset.induction_on with i is hi ih generalizing a,
  { simp_rw [finset.prod_empty, set.mem_one],
    exact ⟨λ h, ⟨λ i, a, λ i, false.elim, h.symm⟩, λ ⟨f, _, hf⟩, hf.symm⟩ },
  rw [finset.prod_insert hi, set.mem_mul],
  simp_rw [finset.prod_insert hi],
  simp_rw ih,
  split,
  { rintros ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩,
    refine ⟨function.update g i x, λ j hj, _, _⟩,
    obtain rfl | hj := finset.mem_insert.mp hj,
    { rw function.update_same, exact hx },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi), exact hg hj, },
    rw [finset.prod_update_of_not_mem hi, function.update_same], },
  { rintros ⟨g, hg, rfl⟩,
    exact ⟨g i, is.prod g, hg (is.mem_insert_self _),
      ⟨g, λ i hi, hg (finset.mem_insert_of_mem hi), rfl⟩, rfl⟩ },
end

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive /-" A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "-/]
lemma mem_fintype_prod [fintype ι] (f : ι → set α) (a : α) :
  a ∈ ∏ i, f i ↔ ∃ (g : ι → α) (hg : ∀ i, g i ∈ f i), ∏ i, g i = a :=
by { rw mem_finset_prod, simp }

/-- The n-ary version of `set.mul_mem_mul`. -/
@[to_additive /-" The n-ary version of `set.add_mem_add`. "-/]
lemma finset_prod_mem_finset_prod (t : finset ι) (f : ι → set α)
  (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
  ∏ i in t, g i ∈ ∏ i in t, f i :=
by { rw mem_finset_prod, exact ⟨g, hg, rfl⟩ }

/-- The n-ary version of `set.mul_subset_mul`. -/
@[to_additive /-" The n-ary version of `set.add_subset_add`. "-/]
lemma finset_prod_subset_finset_prod (t : finset ι) (f₁ f₂ : ι → set α)
  (hf : ∀ {i}, i ∈ t → f₁ i ⊆ f₂ i) :
  ∏ i in t, f₁ i ⊆ ∏ i in t, f₂ i :=
begin
  intro a,
  rw [mem_finset_prod, mem_finset_prod],
  rintro ⟨g, hg, rfl⟩,
  exact ⟨g, λ i hi, hf hi $ hg hi, rfl⟩
end

@[to_additive]
lemma finset_prod_singleton {M ι : Type*} [comm_monoid M] (s : finset ι) (I : ι → M) :
  ∏ (i : ι) in s, ({I i} : set M) = {∏ (i : ι) in s, I i} :=
begin
  letI := classical.dec_eq ι,
  refine finset.induction_on s _ _,
  { simpa },
  { intros _ _ H ih,
    rw [finset.prod_insert H, finset.prod_insert H, ih],
    simp }
end

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/

end big_operators

/-! ### Properties about inversion -/

section inv
variables {s t : set α} {a : α}

/-- The set `(s⁻¹ : set α)` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`.
It is equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
/-" The set `(-s : set α)` is defined as `{x | -x ∈ s}` in locale `pointwise`.
It is equal to `{-x | x ∈ s}`, see `set.image_neg`. "-/]
protected def has_inv [has_inv α] : has_inv (set α) :=
⟨preimage has_inv.inv⟩

localized "attribute [instance] set.has_inv set.has_neg" in pointwise

@[simp, to_additive]
lemma inv_empty [has_inv α] : (∅ : set α)⁻¹ = ∅ := rfl

@[simp, to_additive]
lemma inv_univ [has_inv α] : (univ : set α)⁻¹ = univ := rfl

@[simp, to_additive]
lemma nonempty_inv [group α] {s : set α} : s⁻¹.nonempty ↔ s.nonempty :=
inv_involutive.surjective.nonempty_preimage

@[to_additive] lemma nonempty.inv [group α] {s : set α} (h : s.nonempty) : s⁻¹.nonempty :=
nonempty_inv.2 h

@[simp, to_additive]
lemma mem_inv [has_inv α] : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := iff.rfl

@[to_additive]
lemma inv_mem_inv [group α] : a⁻¹ ∈ s⁻¹ ↔ a ∈ s :=
by simp only [mem_inv, inv_inv]

@[simp, to_additive]
lemma inv_preimage [has_inv α] : has_inv.inv ⁻¹' s = s⁻¹ := rfl

@[simp, to_additive]
lemma image_inv [group α] : has_inv.inv '' s = s⁻¹ :=
by { simp only [← inv_preimage], rw [image_eq_preimage_of_inverse]; intro; simp only [inv_inv] }

@[simp, to_additive]
lemma inter_inv [has_inv α] : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := preimage_inter

@[simp, to_additive]
lemma union_inv [has_inv α] : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := preimage_union

@[simp, to_additive]
lemma Inter_inv {ι : Sort*} [has_inv α] (s : ι → set α) : (⋂ i, s i)⁻¹ = ⋂ i, (s i)⁻¹ :=
preimage_Inter

@[simp, to_additive]
lemma Union_inv {ι : Sort*} [has_inv α] (s : ι → set α) : (⋃ i, s i)⁻¹ = ⋃ i, (s i)⁻¹ :=
preimage_Union

@[simp, to_additive]
lemma compl_inv [has_inv α] : (sᶜ)⁻¹ = (s⁻¹)ᶜ := preimage_compl

@[simp, to_additive]
protected lemma inv_inv [group α] : s⁻¹⁻¹ = s :=
by { simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id'] }

@[simp, to_additive]
protected lemma univ_inv [group α] : (univ : set α)⁻¹ = univ := preimage_univ

@[simp, to_additive]
lemma inv_subset_inv [group α] {s t : set α} : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
(equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive] lemma inv_subset [group α] {s t : set α} : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ :=
by { rw [← inv_subset_inv, set.inv_inv] }

@[to_additive] lemma finite.inv [group α] {s : set α} (hs : finite s) : finite s⁻¹ :=
hs.preimage $ inv_injective.inj_on _

@[to_additive] lemma inv_singleton {β : Type*} [group β] (x : β) : ({x} : set β)⁻¹ = {x⁻¹} :=
by { ext1 y, rw [mem_inv, mem_singleton_iff, mem_singleton_iff, inv_eq_iff_inv_eq, eq_comm], }

@[to_additive] protected lemma mul_inv_rev [group α] (s t : set α) : (s * t)⁻¹ = t⁻¹ * s⁻¹ :=
by simp_rw [←image_inv, ←image2_mul, image_image2, image2_image_left, image2_image_right,
              mul_inv_rev, image2_swap _ s t]

end inv

/-! ### Properties about scalar multiplication -/

section smul

/-- The scaling of a set `(x • s : set β)` by a scalar `x ∶ α` is defined as `{x • y | y ∈ s}`
in locale `pointwise`. -/
@[to_additive has_vadd_set "The translation of a set `(x +ᵥ s : set β)` by a scalar `x ∶ α` is
defined as `{x +ᵥ y | y ∈ s}` in locale `pointwise`."]
protected def has_scalar_set [has_scalar α β] : has_scalar α (set β) :=
⟨λ a, image (has_scalar.smul a)⟩

/-- The pointwise scalar multiplication `(s • t : set β)` by a set of scalars `s ∶ set α`
is defined as `{x • y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[to_additive has_vadd "The pointwise translation `(s +ᵥ t : set β)` by a set of constants
`s ∶ set α` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def has_scalar [has_scalar α β] : has_scalar (set α) (set β) :=
⟨image2 has_scalar.smul⟩

localized "attribute [instance] set.has_scalar_set set.has_scalar" in pointwise
localized "attribute [instance] set.has_vadd_set set.has_vadd" in pointwise

section has_scalar
variables {ι : Sort*} {κ : ι → Sort*} [has_scalar α β] {s s₁ s₂ : set α} {t t₁ t₂ u : set β} {a : α}
  {b : β}

@[simp, to_additive]
lemma image2_smul : image2 has_scalar.smul s t = s • t := rfl

@[to_additive add_image_prod]
lemma image_smul_prod : (λ x : α × β, x.fst • x.snd) '' (s ×ˢ t) = s • t := image_prod _

@[to_additive]
lemma mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b := iff.rfl

@[to_additive]
lemma smul_mem_smul (ha : a ∈ s) (hb : b ∈ t) : a • b ∈ s • t := mem_image2_of_mem ha hb

@[to_additive]
lemma smul_subset_smul (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ • t₁ ⊆ s₂ • t₂ := image2_subset hs ht

@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a • b ∈ u := image2_subset_iff

@[simp, to_additive] lemma empty_smul : (∅ : set α) • t = ∅ := image2_empty_left
@[simp, to_additive] lemma smul_empty : s • (∅ : set β) = ∅ := image2_empty_right

@[simp, to_additive] lemma smul_singleton : s • {b} = (• b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_smul : ({a} : set α) • t = a • t := image2_singleton_left

@[simp, to_additive]
lemma singleton_smul_singleton : ({a} : set α) • ({b} : set β) = {a • b} := image2_singleton

@[to_additive] lemma smul_subset_smul_left (h : t₁ ⊆ t₂) : s • t₁ ⊆ s • t₂ := image2_subset_left h
@[to_additive] lemma smul_subset_smul_right (h : s₁ ⊆ s₂) : s₁ • t ⊆ s₂ • t := image2_subset_right h

@[to_additive] lemma union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image2_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image2_union_right

@[to_additive]
lemma inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left

@[to_additive]
lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ := image2_inter_subset_right

@[to_additive]
lemma Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t := Union_image_left _

@[to_additive]
lemma Union_smul_right_image : (⋃ a ∈ t, (λ x, x • a) '' s) = s • t := Union_image_right _

@[to_additive]
lemma Union_smul (s : ι → set α) (t : set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
image2_Union_left _ _ _

@[to_additive]
lemma smul_Union (s : set α) (t : ι → set β) : s • (⋃ i, t i) = ⋃ i, s • t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_smul (s : Π i, κ i → set α) (t : set β) : (⋃ i j, s i j) • t = ⋃ i j, s i j • t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma smul_Union₂ (s : set α) (t : Π i, κ i → set β) : s • (⋃ i j, t i j) = ⋃ i j, s • t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_smul_subset (s : ι → set α) (t : set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma smul_Inter_subset (s : set α) (t : ι → set β) : s • (⋂ i, t i) ⊆ ⋂ i, s • t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_smul_subset (s : Π i, κ i → set α) (t : set β) :
  (⋂ i j, s i j) • t ⊆ ⋂ i j, s i j • t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma smul_Inter₂_subset (s : set α) (t : Π i, κ i → set β) :
  s • (⋂ i j, t i j) ⊆ ⋂ i j, s • t i j :=
image2_Inter₂_subset_right _ _ _

end has_scalar

section has_scalar_set
variables {ι : Sort*} {κ : ι → Sort*} [has_scalar α β] {s t t₁ t₂ : set β} {a : α} {b : β} {x y : β}

@[simp, to_additive] lemma image_smul : (λ x, a • x) '' t = a • t := rfl

@[to_additive] lemma mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := iff.rfl

@[to_additive] lemma smul_mem_smul_set (hy : y ∈ t) : a • y ∈ a • t := ⟨y, hy, rfl⟩

@[to_additive]
lemma mem_smul_of_mem {s : set α} (ha : a ∈ s) (hb : b ∈ t) : a • b ∈ s • t :=
mem_image2_of_mem ha hb

@[simp, to_additive] lemma smul_set_empty : a • (∅ : set β) = ∅ := image_empty _

@[simp, to_additive] lemma smul_set_singleton : a • ({b} : set β) = {a • b} := image_singleton

@[to_additive] lemma smul_set_mono (h : s ⊆ t) : a • s ⊆ a • t := image_subset _ h

@[to_additive] lemma smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ := image_union _ _ _

@[to_additive]
lemma smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ (a • t₂) := image_inter_subset _ _ _

@[to_additive]
lemma smul_set_Union (a : α) (s : ι → set β) : a • (⋃ i, s i) = ⋃ i, a • s i := image_Union

@[to_additive]
lemma smul_set_Union₂ (a : α) (s : Π i, κ i → set β) : a • (⋃ i j, s i j) = ⋃ i j, a • s i j :=
image_Union₂ _ _

@[to_additive]
lemma smul_set_Inter_subset (a : α) (t : ι → set β) : a • (⋂ i, t i) ⊆ ⋂ i, a • t i :=
image_Inter_subset _ _

@[to_additive]
lemma smul_set_Inter₂_subset (a : α) (t : Π i, κ i → set β) :
  a • (⋂ i j, t i j) ⊆ ⋂ i j, a • t i j :=
image_Inter₂_subset _ _

@[to_additive] lemma finite.smul_set (hs : finite s) : finite (a • s) := hs.image _

end has_scalar_set

variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

@[to_additive]
lemma smul_set_inter [group α] [mul_action α β] {s t : set β} :
  a • (s ∩ t) = a • s ∩ a • t :=
(image_inter $ mul_action.injective a).symm

lemma smul_set_inter₀ [group_with_zero α] [mul_action α β] {s t : set β} (ha : a ≠ 0) :
  a • (s ∩ t) = a • s ∩ a • t :=
show units.mk0 a ha • _ = _, from smul_set_inter

@[simp, to_additive]
lemma smul_set_univ [group α] [mul_action α β] {a : α} : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[simp, to_additive]
lemma smul_univ [group α] [mul_action α β] {s : set α} (hs : s.nonempty) :
  s • (univ : set β) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩

@[to_additive]
theorem range_smul_range {ι κ : Type*} [has_scalar α β] (b : ι → α) (c : κ → β) :
  range b • range c = range (λ p : ι × κ, b p.1 • c p.2) :=
ext $ λ x, ⟨λ hx, let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := set.mem_smul.1 hx in
  ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
λ ⟨⟨i, j⟩, h⟩, set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[to_additive]
instance smul_comm_class_set [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class α (set β) (set γ) :=
{ smul_comm := λ a T T',
    by simp only [←image2_smul, ←image_smul, image2_image_right, image_image2, smul_comm] }

@[to_additive]
instance smul_comm_class_set' [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) β (set γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) (set β) (set γ) :=
{ smul_comm := λ T T' T'', begin
    simp only [←image2_smul, image2_swap _ T],
    exact image2_assoc (λ b c a, smul_comm a b c),
  end }

instance is_scalar_tower [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower α β (set γ) :=
{ smul_assoc := λ a b T, by simp only [←image_smul, image_image, smul_assoc] }

instance is_scalar_tower' [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower α (set β) (set γ) :=
{ smul_assoc := λ a T T',
    by simp only [←image_smul, ←image2_smul, image_image2, image2_image_left, smul_assoc] }

instance is_scalar_tower'' [has_scalar α β] [has_scalar α γ] [has_scalar β γ]
  [is_scalar_tower α β γ] :
  is_scalar_tower (set α) (set β) (set γ) :=
{ smul_assoc := λ T T' T'', image2_assoc smul_assoc }

instance is_central_scalar [has_scalar α β] [has_scalar αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (set β) :=
⟨λ a S, congr_arg (λ f, f '' S) $ by exact funext (λ _, op_smul_eq_smul _ _)⟩

end smul

section vsub
variables {ι : Sort*} {κ : ι → Sort*} [has_vsub α β] {s s₁ s₂ t t₁ t₂ : set β} {a : α}
  {b c : β}
include α

instance has_vsub : has_vsub (set α) (set β) := ⟨image2 (-ᵥ)⟩

@[simp] lemma image2_vsub : (image2 has_vsub.vsub s t : set α) = s -ᵥ t := rfl

lemma image_vsub_prod : (λ x : β × β, x.fst -ᵥ x.snd) '' (s ×ˢ t) = s -ᵥ t := image_prod _

lemma mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a := iff.rfl

lemma vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t := mem_image2_of_mem hb hc

lemma vsub_subset_vsub (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ := image2_subset hs ht

lemma vsub_subset_iff {u : set α} : s -ᵥ t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x -ᵥ y ∈ u := image2_subset_iff

@[simp] lemma empty_vsub (t : set β) : ∅ -ᵥ t = ∅ := image2_empty_left
@[simp] lemma vsub_empty (s : set β) : s -ᵥ ∅ = ∅ := image2_empty_right

@[simp] lemma vsub_singleton (s : set β) (b : β) : s -ᵥ {b} = (-ᵥ b) '' s := image2_singleton_right
@[simp] lemma singleton_vsub (t : set β) (b : β) : {b} -ᵥ t = ((-ᵥ) b) '' t := image2_singleton_left

@[simp] lemma singleton_vsub_singleton : ({b} : set β) -ᵥ {c} = {b -ᵥ c} := image2_singleton

lemma vsub_subset_vsub_left (h : t₁ ⊆ t₂) : s -ᵥ t₁ ⊆ s -ᵥ t₂ := image2_subset_left h
lemma vsub_subset_vsub_right (h : s₁ ⊆ s₂) : s₁ -ᵥ t ⊆ s₂ -ᵥ t := image2_subset_right h

lemma union_vsub : (s₁ ∪ s₂) -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) := image2_union_left
lemma vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) := image2_union_right

lemma inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image2_inter_subset_left
lemma vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) := image2_inter_subset_right

lemma Union_vsub_left_image : (⋃ a ∈ s, ((-ᵥ) a) '' t) = s -ᵥ t := Union_image_left _
lemma Union_vsub_right_image : (⋃ a ∈ t, (-ᵥ a) '' s) = s -ᵥ t := Union_image_right _

lemma Union_vsub (s : ι → set β) (t : set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
image2_Union_left _ _ _

lemma vsub_Union (s : set β) (t : ι → set β) : s -ᵥ (⋃ i, t i) = ⋃ i, s -ᵥ t i :=
image2_Union_right _ _ _

lemma Union₂_vsub (s : Π i, κ i → set β) (t : set β) : (⋃ i j, s i j) -ᵥ t = ⋃ i j, s i j -ᵥ t :=
image2_Union₂_left _ _ _

lemma vsub_Union₂ (s : set β) (t : Π i, κ i → set β) : s -ᵥ (⋃ i j, t i j) = ⋃ i j, s -ᵥ t i j :=
image2_Union₂_right _ _ _

lemma Inter_vsub_subset (s : ι → set β) (t : set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
image2_Inter_subset_left _ _ _

lemma vsub_Inter_subset (s : set β) (t : ι → set β) : s -ᵥ (⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
image2_Inter_subset_right _ _ _

lemma Inter₂_vsub_subset (s : Π i, κ i → set β) (t : set β) :
  (⋂ i j, s i j) -ᵥ t ⊆ ⋂ i j, s i j -ᵥ t :=
image2_Inter₂_subset_left _ _ _

lemma vsub_Inter₂_subset (s : set β) (t : Π i, κ i → set β) :
  s -ᵥ (⋂ i j, t i j) ⊆ ⋂ i j, s -ᵥ t i j :=
image2_Inter₂_subset_right _ _ _

lemma finite.vsub (hs : finite s) (ht : finite t) : finite (s -ᵥ t) := hs.image2 _ ht

lemma vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t := vsub_subset_vsub h h

end vsub

open_locale pointwise

section ring
variables [ring α] [add_comm_group β] [module α β] {s : set α} {t : set β} {a : α}

@[simp] lemma neg_smul_set : -a • t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, neg_smul]

@[simp] lemma smul_set_neg : a • -t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, smul_neg]

@[simp] protected lemma neg_smul : -s • t = -(s • t) :=
by simp_rw [←image2_smul, ←image_neg, image2_image_left, image_image2, neg_smul]

@[simp] protected lemma smul_neg : s • -t = -(s • t) :=
by simp_rw [←image2_smul, ←image_neg, image2_image_right, image_image2, smul_neg]

end ring

section monoid

/-! ### `set α` as a `(∪,*)`-semiring -/

/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
@[derive [inhabited, partial_order, order_bot]] def set_semiring (α : Type*) : Type* := set α

/-- The identitiy function `set α → set_semiring α`. -/
protected def up (s : set α) : set_semiring α := s
/-- The identitiy function `set_semiring α → set α`. -/
protected def set_semiring.down (s : set_semiring α) : set α := s
@[simp] protected lemma down_up {s : set α} : s.up.down = s := rfl
@[simp] protected lemma up_down {s : set_semiring α} : s.down.up = s := rfl

/- This lemma is not tagged `simp`, since otherwise the linter complains. -/
lemma up_le_up {s t : set α} : s.up ≤ t.up ↔ s ⊆ t := iff.rfl
/- This lemma is not tagged `simp`, since otherwise the linter complains. -/
lemma up_lt_up {s t : set α} : s.up < t.up ↔ s ⊂ t := iff.rfl

@[simp] lemma down_subset_down {s t : set_semiring α} : s.down ⊆ t.down ↔ s ≤ t := iff.rfl
@[simp] lemma down_ssubset_down {s t : set_semiring α} : s.down ⊂ t.down ↔ s < t := iff.rfl

instance set_semiring.add_comm_monoid : add_comm_monoid (set_semiring α) :=
{ add := λ s t, (s ∪ t : set α),
  zero := (∅ : set α),
  add_assoc := union_assoc,
  zero_add := empty_union,
  add_zero := union_empty,
  add_comm := union_comm, }

instance set_semiring.non_unital_non_assoc_semiring [has_mul α] :
  non_unital_non_assoc_semiring (set_semiring α) :=
{ zero_mul := λ s, empty_mul,
  mul_zero := λ s, mul_empty,
  left_distrib := λ _ _ _, mul_union,
  right_distrib := λ _ _ _, union_mul,
  ..set.has_mul, ..set_semiring.add_comm_monoid }

instance set_semiring.non_assoc_semiring [mul_one_class α] : non_assoc_semiring (set_semiring α) :=
{ ..set_semiring.non_unital_non_assoc_semiring, ..set.mul_one_class }

instance set_semiring.non_unital_semiring [semigroup α] : non_unital_semiring (set_semiring α) :=
{ ..set_semiring.non_unital_non_assoc_semiring, ..set.semigroup }

instance set_semiring.semiring [monoid α] : semiring (set_semiring α) :=
{ ..set_semiring.non_assoc_semiring, ..set_semiring.non_unital_semiring }

instance set_semiring.comm_semiring [comm_monoid α] : comm_semiring (set_semiring α) :=
{ ..set.comm_monoid, ..set_semiring.semiring }

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
@[to_additive "An additive action of an additive monoid on a type β gives also an additive action
on the subsets of β."]
protected def mul_action_set [monoid α] [mul_action α β] : mul_action α (set β) :=
{ mul_smul := by { intros, simp only [← image_smul, image_image, ← mul_smul] },
  one_smul := by { intros, simp only [← image_smul, image_eta, one_smul, image_id'] },
  ..set.has_scalar_set }

localized "attribute [instance] set.mul_action_set set.add_action_set" in pointwise

section mul_hom

variables [has_mul α] [has_mul β] (m : mul_hom α β) {s t : set α}

@[to_additive]
lemma image_mul : m '' (s * t) = m '' s * m '' t :=
by { simp only [← image2_mul, image_image2, image2_image_left, image2_image_right, m.map_mul] }

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintros _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (m.map_mul _ _).symm ⟩ }

instance set_semiring.no_zero_divisors : no_zero_divisors (set_semiring α) :=
⟨λ a b ab, a.eq_empty_or_nonempty.imp_right $ λ ha, b.eq_empty_or_nonempty.resolve_right $
  λ hb, nonempty.ne_empty ⟨_, mul_mem_mul ha.some_mem hb.some_mem⟩ ab⟩

/- Since addition on `set_semiring` is commutative (it is set union), there is no need
to also have the instance `covariant_class (set_semiring α) (set_semiring α) (swap (+)) (≤)`. -/
instance set_semiring.covariant_class_add :
  covariant_class (set_semiring α) (set_semiring α) (+) (≤) :=
{ elim := λ a b c, union_subset_union_right _ }

instance set_semiring.covariant_class_mul_left :
  covariant_class (set_semiring α) (set_semiring α) (*) (≤) :=
{ elim := λ a b c, mul_subset_mul_left }

instance set_semiring.covariant_class_mul_right :
  covariant_class (set_semiring α) (set_semiring α) (swap (*)) (≤) :=
{ elim := λ a b c, mul_subset_mul_right }

end mul_hom

/-- The image of a set under a multiplicative homomorphism is a ring homomorphism
with respect to the pointwise operations on sets. -/
def image_hom [monoid α] [monoid β] (f : α →* β) : set_semiring α →+* set_semiring β :=
{ to_fun := image f,
  map_zero' := image_empty _,
  map_one' := by simp only [← singleton_one, image_singleton, f.map_one],
  map_add' := image_union _,
  map_mul' := λ _ _, image_mul f.to_mul_hom }

end monoid

section comm_monoid

variable [comm_monoid α]

instance : canonically_ordered_comm_semiring (set_semiring α) :=
{ add_le_add_left := λ a b, add_le_add_left,
  le_iff_exists_add := λ a b, ⟨λ ab, ⟨b, (union_eq_right_iff_subset.2 ab).symm⟩,
    by { rintro ⟨c, rfl⟩, exact subset_union_left _ _ }⟩,
  ..(infer_instance : comm_semiring (set_semiring α)),
  ..(infer_instance : partial_order (set_semiring α)),
  ..(infer_instance : order_bot (set_semiring α)),
  ..(infer_instance : no_zero_divisors (set_semiring α)) }

end comm_monoid

end set

open set
open_locale pointwise

section

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β]

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_set {s : set β} (h : s.nonempty) : (0 : α) • s = (0 : set β) :=
by simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

lemma zero_smul_subset (s : set β) : (0 : α) • s ⊆ 0 := image_subset_iff.2 $ λ x _, zero_smul α x

lemma subsingleton_zero_smul_set (s : set β) : ((0 : α) • s).subsingleton :=
subsingleton_singleton.mono (zero_smul_subset s)

lemma zero_mem_smul_set {t : set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
⟨0, h, smul_zero' _ _⟩

variables [no_zero_smul_divisors α β] {s : set α} {t : set β} {a : α}

lemma zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.nonempty ∨ (0 : β) ∈ t ∧ s.nonempty :=
begin
  split,
  { rintro ⟨a, b, ha, hb, h⟩,
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h,
    { exact or.inl ⟨ha, b, hb⟩ },
    { exact or.inr ⟨hb, a, ha⟩ } },
  { rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩),
    { exact ⟨0, b, hs, hb, zero_smul _ _⟩ },
    { exact ⟨a, 0, ha, ht, smul_zero' _ _⟩ } }
end

lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
begin
  refine ⟨_, zero_mem_smul_set⟩,
  rintro ⟨b, hb, h⟩,
  rwa (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha at hb,
end

end smul_with_zero

lemma smul_add_set [monoid α] [add_monoid β] [distrib_mul_action α β] (c : α) (s t : set β) :
  c • (s + t) = c • s + c • t :=
image_add (distrib_mul_action.to_add_monoid_hom β c).to_add_hom

section group
variables [group α] [mul_action α β] {A B : set β} {a : α} {x : β}

@[simp, to_additive]
lemma smul_mem_smul_set_iff : a • x ∈ a • A ↔ x ∈ A :=
⟨λ h, begin
  rw [←inv_smul_smul a x, ←inv_smul_smul a A],
  exact smul_mem_smul_set h,
end, smul_mem_smul_set⟩

@[to_additive]
lemma mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show x ∈ mul_action.to_perm a '' A ↔ _, from mem_image_equiv

@[to_additive]
lemma mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
by simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive]
lemma preimage_smul (a : α) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
((mul_action.to_perm a).symm.image_eq_preimage _).symm

@[to_additive]
lemma preimage_smul_inv (a : α) (t : set β) : (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul (to_units a)⁻¹ t

@[simp, to_additive]
lemma set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
image_subset_image_iff $ mul_action.injective _

@[to_additive]
lemma set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
(image_subset_iff).trans $ iff_of_eq $ congr_arg _ $
  preimage_equiv_eq_image_symm _ $ mul_action.to_perm _

@[to_additive]
lemma subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
iff.symm $ (image_subset_iff).trans $ iff.symm $ iff_of_eq $ congr_arg _ $
  image_equiv_eq_preimage_symm _ $ mul_action.to_perm _

end group

section group_with_zero
variables [group_with_zero α] [mul_action α β] {s : set α} {a : α}

@[simp] lemma smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : set β)
  (x : β) : a • x ∈ a • A ↔ x ∈ A :=
show units.mk0 a ha • _ ∈ _ ↔ _, from smul_mem_smul_set_iff

lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : set β) (x : β) :
  x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show _ ∈ units.mk0 a ha • _ ↔ _, from mem_smul_set_iff_inv_smul_mem

lemma mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_set_iff

lemma preimage_smul₀ (ha : a ≠ 0) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
preimage_smul (units.mk0 a ha) t

lemma preimage_smul_inv₀ (ha : a ≠ 0) (t : set β) :
  (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul ((units.mk0 a ha)⁻¹) t

@[simp] lemma set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} :
  a • A ⊆ a • B ↔ A ⊆ B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_set_smul_iff

lemma set_smul_subset_iff₀ (ha : a ≠ 0) {A B : set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_iff

lemma subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_set_smul_iff

lemma smul_univ₀ (hs : ¬ s ⊆ 0) : s • (univ : set β) = univ :=
let ⟨a, ha, ha₀⟩ := not_subset.1 hs in eq_univ_of_forall $ λ b,
  ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩

lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul₀ ha _⟩

end group_with_zero

end

namespace finset
variables {a : α} {s s₁ s₂ t t₁ t₂ : finset α}

/-- The finset `(1 : finset α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive /-"The finset `(0 : finset α)` is defined as `{0}` in locale `pointwise`. "-/]
protected def has_one [has_one α] : has_one (finset α) := ⟨{1}⟩

localized "attribute [instance] finset.has_one finset.has_zero" in pointwise

@[simp, to_additive]
lemma mem_one [has_one α] : a ∈ (1 : finset α) ↔ a = 1 :=
by simp [has_one.one]

@[simp, to_additive]
theorem one_subset [has_one α] : (1 : finset α) ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

section decidable_eq
variables [decidable_eq α]

/-- The pointwise product of two finite sets `s` and `t`:
`st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[to_additive /-"The pointwise sum of two finite sets `s` and `t`:
`s + t = { x + y | x ∈ s, y ∈ t }`. "-/]
protected def has_mul [has_mul α] : has_mul (finset α) :=
⟨λ s t, (s.product t).image (λ p : α × α, p.1 * p.2)⟩

localized "attribute [instance] finset.has_mul finset.has_add" in pointwise

section has_mul
variables [has_mul α]

@[to_additive]
lemma mul_def : s * t = (s.product t).image (λ p : α × α, p.1 * p.2) := rfl

@[to_additive]
lemma mem_mul {x : α} : x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [finset.mul_def, and.assoc, mem_image, exists_prop, prod.exists, mem_product] }

@[simp, norm_cast, to_additive]
lemma coe_mul : (↑(s * t) : set α) = ↑s * ↑t :=
by { ext, simp only [mem_mul, set.mem_mul, mem_coe] }

@[to_additive]
lemma mul_mem_mul {x y : α} (hx : x ∈ s) (hy : y ∈ t) : x * y ∈ s * t :=
by { simp only [finset.mem_mul], exact ⟨x, y, hx, hy, rfl⟩ }

@[to_additive]
lemma mul_card_le : (s * t).card ≤ s.card * t.card :=
by { convert finset.card_image_le, rw [finset.card_product, mul_comm] }

@[simp, to_additive] lemma empty_mul (s : finset α) : ∅ * s = ∅ :=
eq_empty_of_forall_not_mem (by simp [mem_mul])

@[simp, to_additive] lemma mul_empty (s : finset α) : s * ∅ = ∅ :=
eq_empty_of_forall_not_mem (by simp [mem_mul])

@[simp, to_additive]
lemma mul_nonempty_iff (s t : finset α) : (s * t).nonempty ↔ s.nonempty ∧ t.nonempty :=
by simp [finset.mul_def]

@[to_additive, mono] lemma mul_subset_mul  (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁ * t₁ ⊆ s₂ * t₂ :=
image_subset_image (product_subset_product hs ht)

attribute [mono] add_subset_add

@[simp, to_additive]
lemma mul_singleton (a : α) : s * {a} = s.image (* a) :=
by { rw [mul_def, product_singleton, map_eq_image, image_image], refl }

@[simp, to_additive]
lemma singleton_mul (a : α) : {a} * s = s.image ((*) a) :=
by { rw [mul_def, singleton_product, map_eq_image, image_image], refl }

@[simp, to_additive]
lemma singleton_mul_singleton (a b : α) : ({a} : finset α) * {b} = {a * b} :=
by rw [mul_def, singleton_product_singleton, image_singleton]

end has_mul

section mul_zero_class
variables [mul_zero_class α]

lemma mul_zero_subset (s : finset α) : s * 0 ⊆ 0 := by simp [subset_iff, mem_mul]

lemma zero_mul_subset (s : finset α) : 0 * s ⊆ 0 := by simp [subset_iff, mem_mul]

lemma nonempty.mul_zero (hs : s.nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm $ by simpa [finset.mem_mul] using hs

lemma nonempty.zero_mul (hs : s.nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm $ by simpa [finset.mem_mul] using hs

lemma singleton_zero_mul (s : finset α) :
  {(0 : α)} * s ⊆ {0} :=
by simp [subset_iff, mem_mul]

end mul_zero_class
end decidable_eq

open_locale pointwise
variables {u : finset α} {b : α} {x y : β}

@[to_additive]
lemma singleton_one [has_one α] : ({1} : finset α) = 1 := rfl

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : finset α) := by simp [has_one.one]

@[to_additive]
theorem one_nonempty [has_one α] : (1 : finset α).nonempty := ⟨1, one_mem_one⟩

@[simp, to_additive]
theorem image_one [decidable_eq β] [has_one α] {f : α → β} : image f 1 = {f 1} :=
image_singleton f 1

@[to_additive add_image_prod]
lemma image_mul_prod [decidable_eq α] [has_mul α] :
  image (λ x : α × α, x.fst * x.snd) (s.product t) = s * t := rfl

@[simp, to_additive]
lemma image_mul_left [decidable_eq α] [group α] :
  image (λ b, a * b) t = preimage t (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj a⁻¹).mp) :=
coe_injective $ by simp

@[simp, to_additive]
lemma image_mul_right [decidable_eq α] [group α] :
  image (* b) t = preimage t (* b⁻¹) (assume x hx y hy, (mul_left_inj b⁻¹).mp) :=
coe_injective $ by simp

@[to_additive]
lemma image_mul_left' [decidable_eq α] [group α] :
  image (λ b, a⁻¹ * b) t = preimage t (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) :=
by simp

@[to_additive]
lemma image_mul_right' [decidable_eq α] [group α] :
  image (* b⁻¹) t = preimage t (* b) (assume x hx y hy, (mul_left_inj b).mp) :=
by simp

@[simp, to_additive]
lemma preimage_mul_left_singleton [group α] :
  preimage {b} ((*) a) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹ * b} :=
by { classical, rw [← image_mul_left', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_right_singleton [group α] :
  preimage {b} (* a) (assume x hx y hy, (mul_left_inj a).mp) = {b * a⁻¹} :=
by { classical, rw [← image_mul_right', image_singleton] }

@[simp, to_additive]
lemma preimage_mul_left_one [group α] :
  preimage 1 (λ b, a * b) (assume x hx y hy, (mul_right_inj a).mp) = {a⁻¹} :=
by {classical, rw [← image_mul_left', image_one, mul_one] }

@[simp, to_additive]
lemma preimage_mul_right_one [group α] :
  preimage 1 (* b) (assume x hx y hy, (mul_left_inj b).mp) = {b⁻¹} :=
by {classical, rw [← image_mul_right', image_one, one_mul] }

@[to_additive]
lemma preimage_mul_left_one' [group α] :
  preimage 1 (λ b, a⁻¹ * b) (assume x hx y hy, (mul_right_inj _).mp) = {a} := by simp

@[to_additive]
lemma preimage_mul_right_one' [group α] :
  preimage 1 (* b⁻¹) (assume x hx y hy, (mul_left_inj _).mp) = {b} := by simp

@[to_additive]
protected lemma mul_comm [decidable_eq α] [comm_semigroup α] : s * t = t * s :=
by exact_mod_cast @set.mul_comm _ (s : set α) t _

/-- `finset α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_zero_class` under pointwise operations if `α` is."-/]
protected def mul_one_class [decidable_eq α] [mul_one_class α] : mul_one_class (finset α) :=
function.injective.mul_one_class _ coe_injective (coe_singleton 1) (by simp)

/-- `finset α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_semigroup` under pointwise operations if `α` is. "-/]
protected def semigroup [decidable_eq α] [semigroup α] : semigroup (finset α) :=
function.injective.semigroup _ coe_injective (by simp)

/-- `finset α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_monoid` under pointwise operations if `α` is. "-/]
protected def monoid [decidable_eq α] [monoid α] : monoid (finset α) :=
function.injective.monoid _ coe_injective (coe_singleton 1) (by simp)

/-- `finset α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`finset α` is an `add_comm_monoid` under pointwise operations if `α` is. "-/]
protected def comm_monoid [decidable_eq α] [comm_monoid α] : comm_monoid (finset α) :=
function.injective.comm_monoid _ coe_injective (coe_singleton 1) (by simp)

localized "attribute [instance] finset.mul_one_class finset.add_zero_class finset.semigroup
  finset.add_semigroup finset.monoid finset.add_monoid finset.comm_monoid finset.add_comm_monoid"
  in pointwise

open_locale classical

/-- A finite set `U` contained in the product of two sets `S * S'` is also contained in the product
of two finite sets `T * T' ⊆ S * S'`. -/
@[to_additive]
lemma subset_mul {M : Type*} [monoid M] {S : set M} {S' : set M} {U : finset M} (f : ↑U ⊆ S * S') :
  ∃ (T T' : finset M), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ U ⊆ T * T' :=
begin
  apply finset.induction_on' U,
  { use [∅, ∅], simp only [finset.empty_subset, finset.coe_empty, set.empty_subset, and_self], },
  rintros a s haU hs has ⟨T, T', hS, hS', h⟩,
  obtain ⟨x, y, hx, hy, ha⟩ := set.mem_mul.1 (f haU),
  use [insert x T, insert y T'],
  simp only [finset.coe_insert],
  repeat { rw [set.insert_subset], },
  use [hx, hS, hy, hS'],
  refine finset.insert_subset.mpr ⟨_, _⟩,
  { rw finset.mem_mul,
    use [x,y],
    simpa only [true_and, true_or, eq_self_iff_true, finset.mem_insert], },
  { suffices g : (s : set M) ⊆ insert x T * insert y T', { norm_cast at g, assumption, },
    transitivity ↑(T * T'),
    apply h,
    rw finset.coe_mul,
    apply set.mul_subset_mul (set.subset_insert x T) (set.subset_insert y T'), },
end

end finset

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/
namespace submonoid

variables {M : Type*} [monoid M] {s t u : set M}

@[to_additive]
lemma mul_subset {S : submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
by { rintro _ ⟨p, q, hp, hq, rfl⟩, exact submonoid.mul_mem _ (hs hp) (ht hq) }

@[to_additive]
lemma mul_subset_closure (hs : s ⊆ u) (ht : t ⊆ u) : s * t ⊆ submonoid.closure u :=
mul_subset (subset.trans hs submonoid.subset_closure) (subset.trans ht submonoid.subset_closure)

@[to_additive]
lemma coe_mul_self_eq (s : submonoid M) : (s : set M) * s = s :=
begin
  ext x,
  refine ⟨_, λ h, ⟨x, 1, h, s.one_mem, mul_one x⟩⟩,
  rintros ⟨a, b, ha, hb, rfl⟩,
  exact s.mul_mem ha hb
end

@[to_additive]
lemma closure_mul_le (S T : set M) : closure (S * T) ≤ closure S ⊔ closure T :=
Inf_le $ λ x ⟨s, t, hs, ht, hx⟩, hx ▸ (closure S ⊔ closure T).mul_mem
    (set_like.le_def.mp le_sup_left $ subset_closure hs)
    (set_like.le_def.mp le_sup_right $ subset_closure ht)

@[to_additive]
lemma sup_eq_closure (H K : submonoid M) : H ⊔ K = closure (H * K) :=
le_antisymm
  (sup_le
    (λ h hh, subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩)
    (λ k hk, subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩))
  (by conv_rhs { rw [← closure_eq H, ← closure_eq K] }; apply closure_mul_le)

lemma pow_smul_mem_closure_smul {N : Type*} [comm_monoid N] [mul_action M N]
  [is_scalar_tower M N N] (r : M) (s : set N) {x : N} (hx : x ∈ closure s) :
  ∃ n : ℕ, r ^ n • x ∈ closure (r • s) :=
begin
  apply @closure_induction N _ s
    (λ (x : N), ∃ n : ℕ, r ^ n • x ∈ closure (r • s)) _ hx,
  { intros x hx,
    exact ⟨1, subset_closure ⟨_, hx, by rw pow_one⟩⟩ },
  { exact ⟨0, by simpa using one_mem _⟩ },
  { rintros x y ⟨nx, hx⟩ ⟨ny, hy⟩,
    use nx + ny,
    convert mul_mem _ hx hy,
    rw [pow_add, smul_mul_assoc, mul_smul, mul_comm, ← smul_mul_assoc, mul_comm] }
end

end submonoid

namespace group

lemma card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : monotone f)
  {B : ℕ} (h2 : ∀ n, f n ≤ B) (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) :
  ∀ k, B ≤ k → f k = f B :=
begin
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1),
  { contrapose! h2,
    suffices : ∀ n : ℕ, n ≤ B + 1 → n ≤ f n,
    { exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩ },
    exact λ n, nat.rec (λ h, nat.zero_le (f 0)) (λ n ih h, lt_of_le_of_lt (ih (n.le_succ.trans h))
      (lt_of_le_of_ne (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h)))) n },
  { obtain ⟨n, hn1, hn2⟩ := key,
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n :=
    λ k, nat.rec ⟨hn2, rfl⟩ (λ k ih, ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k,
    replace key : ∀ k : ℕ, n ≤ k → f k = f n :=
    λ k hk, (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2,
    exact λ k hk, (key k (hn1.trans hk)).trans (key B hn1).symm },
end

variables {G : Type*} [group G] [fintype G] (S : set G)

@[to_additive]
lemma card_pow_eq_card_pow_card_univ [∀ (k : ℕ), decidable_pred (∈ (S ^ k))] :
  ∀ k, fintype.card G ≤ k → fintype.card ↥(S ^ k) = fintype.card ↥(S ^ (fintype.card G)) :=
begin
  have hG : 0 < fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩,
  by_cases hS : S = ∅,
  { refine λ k hk, fintype.card_congr _,
    rw [hS, empty_pow _ (ne_of_gt (lt_of_lt_of_le hG hk)), empty_pow _ (ne_of_gt hG)] },
  obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS,
  classical,
  have key : ∀ a (s t : set G), (∀ b : G, b ∈ s → a * b ∈ t) → fintype.card s ≤ fintype.card t,
  { refine λ a s t h, fintype.card_le_of_injective (λ ⟨b, hb⟩, ⟨a * b, h b hb⟩) _,
    rintros ⟨b, hb⟩ ⟨c, hc⟩ hbc,
    exact subtype.ext (mul_left_cancel (subtype.ext_iff.mp hbc)) },
  have mono : monotone (λ n, fintype.card ↥(S ^ n) : ℕ → ℕ) :=
  monotone_nat_of_le_succ (λ n, key a _ _ (λ b hb, set.mul_mem_mul ha hb)),
  convert card_pow_eq_card_pow_card_univ_aux mono (λ n, set_fintype_card_le_univ (S ^ n))
    (λ n h, le_antisymm (mono (n + 1).le_succ) (key a⁻¹ _ _ _)),
  { simp only [finset.filter_congr_decidable, fintype.card_of_finset] },
  replace h : {a} * S ^ n = S ^ (n + 1),
  { refine set.eq_of_subset_of_card_le _ (le_trans (ge_of_eq h) _),
    { exact mul_subset_mul (set.singleton_subset_iff.mpr ha) set.subset.rfl },
    { convert key a (S ^ n) ({a} * S ^ n) (λ b hb, set.mul_mem_mul (set.mem_singleton a) hb) } },
  rw [pow_succ', ←h, mul_assoc, ←pow_succ', h],
  rintros _ ⟨b, c, hb, hc, rfl⟩,
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_left],
end

end group
