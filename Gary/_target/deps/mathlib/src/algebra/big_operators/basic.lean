/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/

import algebra.group.pi
import algebra.ring.opposite
import data.equiv.mul_add
import data.finset.fold
import data.fintype.basic
import data.set.pairwise

/-!
# Big operators

In this file we define products and sums indexed by finite sets (specifically, `finset`).

## Notation

We introduce the following notation, localized in `big_operators`.
To enable the notation, use `open_locale big_operators`.

Let `s` be a `finset α`, and `f : α → β` a function.

* `∏ x in s, f x` is notation for `finset.prod s f` (assuming `β` is a `comm_monoid`)
* `∑ x in s, f x` is notation for `finset.sum s f` (assuming `β` is an `add_comm_monoid`)
* `∏ x, f x` is notation for `finset.prod finset.univ f`
  (assuming `α` is a `fintype` and `β` is a `comm_monoid`)
* `∑ x, f x` is notation for `finset.sum finset.univ f`
  (assuming `α` is a `fintype` and `β` is an `add_comm_monoid`)

## Implementation Notes

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

-/

universes u v w
variables {β : Type u} {α : Type v} {γ : Type w}

namespace finset

/--
`∏ x in s, f x` is the product of `f x`
as `x` ranges over the elements of the finite set `s`.
-/
@[to_additive "`∑ x in s, f x` is the sum of `f x` as `x` ranges over the elements
of the finite set `s`."]
protected def prod [comm_monoid β] (s : finset α) (f : α → β) : β := (s.1.map f).prod

@[simp, to_additive] lemma prod_mk [comm_monoid β] (s : multiset α) (hs : s.nodup) (f : α → β) :
  (⟨s, hs⟩ : finset α).prod f = (s.map f).prod :=
rfl

end finset

/--
There is no established mathematical convention
for the operator precedence of big operators like `∏` and `∑`.
We will have to make a choice.

Online discussions, such as https://math.stackexchange.com/q/185538/30839
seem to suggest that `∏` and `∑` should have the same precedence,
and that this should be somewhere between `*` and `+`.
The latter have precedence levels `70` and `65` respectively,
and we therefore choose the level `67`.

In practice, this means that parentheses should be placed as follows:
```lean
∑ k in K, (a k + b k) = ∑ k in K, a k + ∑ k in K, b k →
  ∏ k in K, a k * b k = (∏ k in K, a k) * (∏ k in K, b k)
```
(Example taken from page 490 of Knuth's *Concrete Mathematics*.)
-/
library_note "operator precedence of big operators"

localized "notation `∑` binders `, ` r:(scoped:67 f, finset.sum finset.univ f) := r"
  in big_operators
localized "notation `∏` binders `, ` r:(scoped:67 f, finset.prod finset.univ f) := r"
  in big_operators

localized "notation `∑` binders ` in ` s `, ` r:(scoped:67 f, finset.sum s f) := r"
  in big_operators
localized "notation `∏` binders ` in ` s `, ` r:(scoped:67 f, finset.prod s f) := r"
  in big_operators

open_locale big_operators

namespace finset
variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

@[to_additive] lemma prod_eq_multiset_prod [comm_monoid β] (s : finset α) (f : α → β) :
  ∏ x in s, f x = (s.1.map f).prod := rfl

@[to_additive]
theorem prod_eq_fold [comm_monoid β] (s : finset α) (f : α → β) :
  ∏ x in s, f x = s.fold (*) 1 f :=
rfl

@[simp] lemma sum_multiset_singleton (s : finset α) :
  s.sum (λ x, {x}) = s.val :=
by simp only [sum_eq_multiset_sum, multiset.sum_map_singleton]

end finset


@[to_additive]
lemma monoid_hom.map_prod [comm_monoid β] [comm_monoid γ] (g : β →* γ) (f : α → β) (s : finset α) :
  g (∏ x in s, f x) = ∏ x in s, g (f x) :=
by simp only [finset.prod_eq_multiset_prod, g.map_multiset_prod, multiset.map_map]

@[to_additive]
lemma mul_equiv.map_prod [comm_monoid β] [comm_monoid γ] (g : β ≃* γ) (f : α → β) (s : finset α) :
  g (∏ x in s, f x) = ∏ x in s, g (f x) :=
g.to_monoid_hom.map_prod f s

lemma ring_hom.map_list_prod [semiring β] [semiring γ] (f : β →+* γ) (l : list β) :
  f l.prod = (l.map f).prod :=
f.to_monoid_hom.map_list_prod l

lemma ring_hom.map_list_sum [non_assoc_semiring β] [non_assoc_semiring γ]
  (f : β →+* γ) (l : list β) :
  f l.sum = (l.map f).sum :=
f.to_add_monoid_hom.map_list_sum l

/-- A morphism into the opposite ring acts on the product by acting on the reversed elements -/
lemma ring_hom.unop_map_list_prod [semiring β] [semiring γ] (f : β →+* γᵐᵒᵖ) (l : list β) :
  mul_opposite.unop (f l.prod) = (l.map (mul_opposite.unop ∘ f)).reverse.prod :=
f.to_monoid_hom.unop_map_list_prod l

lemma ring_hom.map_multiset_prod [comm_semiring β] [comm_semiring γ] (f : β →+* γ)
  (s : multiset β) :
  f s.prod = (s.map f).prod :=
f.to_monoid_hom.map_multiset_prod s

lemma ring_hom.map_multiset_sum [non_assoc_semiring β] [non_assoc_semiring γ]
  (f : β →+* γ) (s : multiset β) :
  f s.sum = (s.map f).sum :=
f.to_add_monoid_hom.map_multiset_sum s

lemma ring_hom.map_prod [comm_semiring β] [comm_semiring γ] (g : β →+* γ) (f : α → β)
  (s : finset α) :
  g (∏ x in s, f x) = ∏ x in s, g (f x) :=
g.to_monoid_hom.map_prod f s

lemma ring_hom.map_sum [non_assoc_semiring β] [non_assoc_semiring γ]
  (g : β →+* γ) (f : α → β) (s : finset α) :
  g (∑ x in s, f x) = ∑ x in s, g (f x) :=
g.to_add_monoid_hom.map_sum f s

@[to_additive]
lemma monoid_hom.coe_finset_prod [mul_one_class β] [comm_monoid γ] (f : α → β →* γ) (s : finset α) :
  ⇑(∏ x in s, f x) = ∏ x in s, f x :=
(monoid_hom.coe_fn β γ).map_prod _ _

-- See also `finset.prod_apply`, with the same conclusion
-- but with the weaker hypothesis `f : α → β → γ`.
@[simp, to_additive]
lemma monoid_hom.finset_prod_apply [mul_one_class β] [comm_monoid γ] (f : α → β →* γ)
  (s : finset α) (b : β) : (∏ x in s, f x) b = ∏ x in s, f x b :=
(monoid_hom.eval b).map_prod _ _

variables {s s₁ s₂ : finset α} {a : α} {f g : α → β}

namespace finset

section comm_monoid
variables [comm_monoid β]

@[simp, to_additive]
lemma prod_empty {f : α → β} : (∏ x in (∅:finset α), f x) = 1 := rfl

@[simp, to_additive]
lemma prod_cons (h : a ∉ s) : (∏ x in (cons a s h), f x) = f a * ∏ x in s, f x :=
fold_cons h

@[simp, to_additive]
lemma prod_insert [decidable_eq α] : a ∉ s → (∏ x in (insert a s), f x) = f a * ∏ x in s, f x :=
fold_insert

/--
The product of `f` over `insert a s` is the same as
the product over `s`, as long as `a` is in `s` or `f a = 1`.
-/
@[simp, to_additive "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `a` is in `s` or `f a = 0`."]
lemma prod_insert_of_eq_one_if_not_mem [decidable_eq α] (h : a ∉ s → f a = 1) :
  ∏ x in insert a s, f x = ∏ x in s, f x :=
begin
  by_cases hm : a ∈ s,
  { simp_rw insert_eq_of_mem hm },
  { rw [prod_insert hm, h hm, one_mul] },
end

/--
The product of `f` over `insert a s` is the same as the product over `s`, as long as `f a = 1`.
-/
@[simp, to_additive "The sum of `f` over `insert a s` is the same as
the sum over `s`, as long as `f a = 0`."]
lemma prod_insert_one [decidable_eq α] (h : f a = 1) :
  ∏ x in insert a s, f x = ∏ x in s, f x :=
prod_insert_of_eq_one_if_not_mem (λ _, h)

@[simp, to_additive]
lemma prod_singleton : (∏ x in (singleton a), f x) = f a :=
eq.trans fold_singleton $ mul_one _

@[to_additive]
lemma prod_pair [decidable_eq α] {a b : α} (h : a ≠ b) :
  (∏ x in ({a, b} : finset α), f x) = f a * f b :=
by rw [prod_insert (not_mem_singleton.2 h), prod_singleton]

@[simp, priority 1100, to_additive]
lemma prod_const_one : (∏ x in s, (1 : β)) = 1 :=
by simp only [finset.prod, multiset.map_const, multiset.prod_repeat, one_pow]

@[simp, to_additive]
lemma prod_image [decidable_eq α] {s : finset γ} {g : γ → α} :
  (∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) → (∏ x in (s.image g), f x) = ∏ x in s, f (g x) :=
fold_image

@[simp, to_additive]
lemma prod_map (s : finset α) (e : α ↪ γ) (f : γ → β) :
  (∏ x in (s.map e), f x) = ∏ x in s, f (e x) :=
by rw [finset.prod, finset.map_val, multiset.map_map]; refl

@[congr, to_additive]
lemma prod_congr (h : s₁ = s₂) : (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g :=
by rw [h]; exact fold_congr
attribute [congr] finset.sum_congr

@[to_additive]
lemma prod_union_inter [decidable_eq α] :
  (∏ x in (s₁ ∪ s₂), f x) * (∏ x in (s₁ ∩ s₂), f x) = (∏ x in s₁, f x) * (∏ x in s₂, f x) :=
fold_union_inter

@[to_additive]
lemma prod_union [decidable_eq α] (h : disjoint s₁ s₂) :
  (∏ x in (s₁ ∪ s₂), f x) = (∏ x in s₁, f x) * (∏ x in s₂, f x) :=
by rw [←prod_union_inter, (disjoint_iff_inter_eq_empty.mp h)]; exact (mul_one _).symm

@[to_additive]
lemma prod_filter_mul_prod_filter_not (s : finset α) (p : α → Prop) [decidable_pred p]
  [decidable_pred (λ x, ¬p x)] (f : α → β) :
  (∏ x in s.filter p, f x) * (∏ x in s.filter (λ x, ¬p x), f x) = ∏ x in s, f x :=
begin
  haveI := classical.dec_eq α,
  rw [← prod_union (filter_inter_filter_neg_eq p s).le, filter_union_filter_neg_eq]
end

section to_list

@[simp, to_additive]
lemma prod_to_list (s : finset α) (f : α → β) : (s.to_list.map f).prod = s.prod f :=
by rw [finset.prod, ← multiset.coe_prod, ← multiset.coe_map, finset.coe_to_list]

end to_list

@[to_additive]
lemma _root_.equiv.perm.prod_comp (σ : equiv.perm α) (s : finset α) (f : α → β)
  (hs : {a | σ a ≠ a} ⊆ s) :
  (∏ x in s, f (σ x)) = ∏ x in s, f x :=
by { convert (prod_map _ σ.to_embedding _).symm, exact (map_perm hs).symm }

@[to_additive]
lemma _root_.equiv.perm.prod_comp' (σ : equiv.perm α) (s : finset α) (f : α → α → β)
  (hs : {a | σ a ≠ a} ⊆ s) :
  (∏ x in s, f (σ x) x) = ∏ x in s, f x (σ.symm x) :=
by { convert σ.prod_comp s (λ x, f x (σ.symm x)) hs, ext, rw equiv.symm_apply_apply }

end comm_monoid

end finset

section
open finset
variables [fintype α] [decidable_eq α] [comm_monoid β]

@[to_additive]
lemma is_compl.prod_mul_prod {s t : finset α} (h : is_compl s t) (f : α → β) :
  (∏ i in s, f i) * (∏ i in t, f i) = ∏ i, f i :=
(finset.prod_union h.disjoint).symm.trans $ by rw [← finset.sup_eq_union, h.sup_eq_top]; refl

end

namespace finset

section comm_monoid
variables [comm_monoid β]

/-- Multiplying the products of a function over `s` and over `sᶜ` gives the whole product.
For a version expressed with subtypes, see `fintype.prod_subtype_mul_prod_subtype`. -/
@[to_additive "Adding the sums of a function over `s` and over `sᶜ` gives the whole sum.
For a version expressed with subtypes, see `fintype.sum_subtype_add_sum_subtype`. "]
lemma prod_mul_prod_compl [fintype α] [decidable_eq α] (s : finset α) (f : α → β) :
  (∏ i in s, f i) * (∏ i in sᶜ, f i) = ∏ i, f i :=
is_compl.prod_mul_prod is_compl_compl f

@[to_additive]
lemma prod_compl_mul_prod [fintype α] [decidable_eq α] (s : finset α) (f : α → β) :
  (∏ i in sᶜ, f i) * (∏ i in s, f i) = ∏ i, f i :=
(@is_compl_compl _ s _).symm.prod_mul_prod f

@[to_additive]
lemma prod_sdiff [decidable_eq α] (h : s₁ ⊆ s₂) :
  (∏ x in (s₂ \ s₁), f x) * (∏ x in s₁, f x) = (∏ x in s₂, f x) :=
by rw [←prod_union sdiff_disjoint, sdiff_union_of_subset h]

@[simp, to_additive]
lemma prod_sum_elim [decidable_eq (α ⊕ γ)]
  (s : finset α) (t : finset γ) (f : α → β) (g : γ → β) :
  ∏ x in s.map function.embedding.inl ∪ t.map function.embedding.inr, sum.elim f g x =
    (∏ x in s, f x) * (∏ x in t, g x) :=
begin
  rw [prod_union, prod_map, prod_map],
  { simp only [sum.elim_inl, function.embedding.inl_apply, function.embedding.inr_apply,
      sum.elim_inr] },
  { simp only [disjoint_left, finset.mem_map, finset.mem_map],
    rintros _ ⟨i, hi, rfl⟩ ⟨j, hj, H⟩,
    cases H }
end

@[to_additive]
lemma prod_bUnion [decidable_eq α] {s : finset γ} {t : γ → finset α}
  (hs : set.pairwise_disjoint ↑s t) :
  (∏ x in (s.bUnion t), f x) = ∏ x in s, ∏ i in t x, f i :=
begin
  haveI := classical.dec_eq γ,
  induction s using finset.induction_on with x s hxs ih hd,
  { simp_rw [bUnion_empty, prod_empty] },
  { simp_rw [coe_insert, set.pairwise_disjoint_insert, mem_coe] at hs,
    have : disjoint (t x) (finset.bUnion s t),
    { exact (disjoint_bUnion_right _ _ _).mpr (λ y hy, hs.2 y hy $ λ H, hxs $ H.substr hy) },
    rw [bUnion_insert, prod_insert hxs, prod_union this, ih hs.1] }
end

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
@[to_additive "Sum over a sigma type equals the sum of fiberwise sums. For rewriting
in the reverse direction, use `finset.sum_sigma'`"]
lemma prod_sigma {σ : α → Type*}
  (s : finset α) (t : Π a, finset (σ a)) (f : sigma σ → β) :
  (∏ x in s.sigma t, f x) = ∏ a in s, ∏ s in (t a), f ⟨a, s⟩ :=
by classical;
calc (∏ x in s.sigma t, f x) =
       ∏ x in s.bUnion (λ a, (t a).map (function.embedding.sigma_mk a)), f x : by rw sigma_eq_bUnion
  ... = ∏ a in s, ∏ x in (t a).map (function.embedding.sigma_mk a), f x :
    prod_bUnion $ assume a₁ ha a₂ ha₂ h x hx,
    by { simp only [inf_eq_inter, mem_inter, mem_map, function.embedding.sigma_mk_apply] at hx,
      rcases hx with ⟨⟨y, hy, rfl⟩, ⟨z, hz, hz'⟩⟩, cc }
  ... = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ :
    prod_congr rfl $ λ _ _, prod_map _ _ _

@[to_additive]
lemma prod_sigma' {σ : α → Type*}
  (s : finset α) (t : Π a, finset (σ a)) (f : Π a, σ a → β) :
  (∏ a in s, ∏ s in (t a), f a s) = ∏ x in s.sigma t, f x.1 x.2 :=
eq.symm $ prod_sigma s t (λ x, f x.1 x.2)

/--
  Reorder a product.

  The difference with `prod_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
-/
@[to_additive "
  Reorder a sum.

  The difference with `sum_bij'` is that the bijection is specified as a surjective injection,
  rather than by an inverse function.
"]
lemma prod_bij {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Π a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
  (i_inj : ∀ a₁ a₂ ha₁ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂) (i_surj : ∀ b ∈ t, ∃ a ha, b = i a ha) :
  (∏ x in s, f x) = (∏ x in t, g x) :=
congr_arg multiset.prod
  (multiset.map_eq_map_of_bij_of_nodup f g s.2 t.2 i hi h i_inj i_surj)

/--
  Reorder a product.

  The difference with `prod_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
-/
@[to_additive "
  Reorder a sum.

  The difference with `sum_bij` is that the bijection is specified with an inverse, rather than
  as a surjective injection.
"]
lemma prod_bij' {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Π a ∈ s, γ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
  (j : Π a ∈ t, α) (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
  (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) :
  (∏ x in s, f x) = (∏ x in t, g x) :=
begin
  refine prod_bij i hi h _ _,
  {intros a1 a2 h1 h2 eq, rw [←left_inv a1 h1, ←left_inv a2 h2], cc,},
  {intros b hb, use j b hb, use hj b hb, exact (right_inv b hb).symm,},
end

@[to_additive] lemma prod_finset_product
  (r : finset (γ × α)) (s : finset γ) (t : γ → finset α)
  (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ × α → β} :
  ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (c, a) :=
begin
  refine eq.trans _ (prod_sigma s t (λ p, f (p.1, p.2))),
  exact prod_bij' (λ p hp, ⟨p.1, p.2⟩) (λ p, mem_sigma.mpr ∘ (h p).mp)
    (λ p hp, congr_arg f prod.mk.eta.symm) (λ p hp, (p.1, p.2))
    (λ p, (h (p.1, p.2)).mpr ∘ mem_sigma.mp) (λ p hp, prod.mk.eta) (λ p hp, p.eta),
end

@[to_additive] lemma prod_finset_product'
  (r : finset (γ × α)) (s : finset γ) (t : γ → finset α)
  (h : ∀ p : γ × α, p ∈ r ↔ p.1 ∈ s ∧ p.2 ∈ t p.1) {f : γ → α → β} :
  ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f c a :=
prod_finset_product r s t h

@[to_additive] lemma prod_finset_product_right
  (r : finset (α × γ)) (s : finset γ) (t : γ → finset α)
  (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α × γ → β} :
  ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (a, c) :=
begin
  refine eq.trans _ (prod_sigma s t (λ p, f (p.2, p.1))),
  exact prod_bij' (λ p hp, ⟨p.2, p.1⟩) (λ p, mem_sigma.mpr ∘ (h p).mp)
    (λ p hp, congr_arg f prod.mk.eta.symm) (λ p hp, (p.2, p.1))
    (λ p, (h (p.2, p.1)).mpr ∘ mem_sigma.mp) (λ p hp, prod.mk.eta) (λ p hp, p.eta),
end

@[to_additive] lemma prod_finset_product_right'
  (r : finset (α × γ)) (s : finset γ) (t : γ → finset α)
  (h : ∀ p : α × γ, p ∈ r ↔ p.2 ∈ s ∧ p.1 ∈ t p.2) {f : α → γ → β} :
  ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f a c :=
prod_finset_product_right r s t h

@[to_additive]
lemma prod_fiberwise_of_maps_to [decidable_eq γ] {s : finset α} {t : finset γ} {g : α → γ}
  (h : ∀ x ∈ s, g x ∈ t) (f : α → β) :
  (∏ y in t, ∏ x in s.filter (λ x, g x = y), f x) = ∏ x in s, f x :=
begin
  letI := classical.dec_eq α,
  rw [← bUnion_filter_eq_of_maps_to h] {occs := occurrences.pos [2]},
  refine (prod_bUnion $ λ x' hx y' hy hne, _).symm,
  rw [function.on_fun, disjoint_filter],
  rintros x hx rfl,
  exact hne
end

@[to_additive]
lemma prod_image' [decidable_eq α] {s : finset γ} {g : γ → α} (h : γ → β)
  (eq : ∀ c ∈ s, f (g c) = ∏ x in s.filter (λ c', g c' = g c), h x) :
  (∏ x in s.image g, f x) = ∏ x in s, h x :=
calc (∏ x in s.image g, f x) = ∏ x in s.image g, ∏ x in s.filter (λ c', g c' = x), h x :
  prod_congr rfl $ λ x hx, let ⟨c, hcs, hc⟩ := mem_image.1 hx in hc ▸ (eq c hcs)
... = ∏ x in s, h x : prod_fiberwise_of_maps_to (λ x, mem_image_of_mem g) _

@[to_additive]
lemma prod_mul_distrib : ∏ x in s, (f x * g x) = (∏ x in s, f x) * (∏ x in s, g x) :=
eq.trans (by rw one_mul; refl) fold_op_distrib

@[to_additive]
lemma prod_comm {s : finset γ} {t : finset α} {f : γ → α → β} :
  (∏ x in s, ∏ y in t, f x y) = (∏ y in t, ∏ x in s, f x y) :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [prod_empty, prod_const_one] },
  { intros _ _ H ih,
    simp only [prod_insert H, prod_mul_distrib, ih] }
end

@[to_additive]
lemma prod_product {s : finset γ} {t : finset α} {f : γ×α → β} :
  (∏ x in s.product t, f x) = ∏ x in s, ∏ y in t, f (x, y) :=
prod_finset_product (s.product t) s (λ a, t) (λ p, mem_product)

/-- An uncurried version of `finset.prod_product`. -/
@[to_additive "An uncurried version of `finset.sum_product`"]
lemma prod_product' {s : finset γ} {t : finset α} {f : γ → α → β} :
  (∏ x in s.product t, f x.1 x.2) = ∏ x in s, ∏ y in t, f x y :=
prod_product

@[to_additive]
lemma prod_product_right {s : finset γ} {t : finset α} {f : γ×α → β} :
  (∏ x in s.product t, f x) = ∏ y in t, ∏ x in s, f (x, y) :=
by rw [prod_product, prod_comm]

/-- An uncurried version of `finset.prod_product_right`. -/
@[to_additive "An uncurried version of `finset.prod_product_right`"]
lemma prod_product_right' {s : finset γ} {t : finset α} {f : γ → α → β} :
  (∏ x in s.product t, f x.1 x.2) = ∏ y in t, ∏ x in s, f x y :=
prod_product_right

@[to_additive]
lemma prod_hom_rel [comm_monoid γ] {r : β → γ → Prop} {f : α → β} {g : α → γ} {s : finset α}
  (h₁ : r 1 1) (h₂ : ∀ a b c, r b c → r (f a * b) (g a * c)) : r (∏ x in s, f x) (∏ x in s, g x) :=
by { delta finset.prod, apply multiset.prod_hom_rel; assumption }

@[to_additive]
lemma prod_eq_one {f : α → β} {s : finset α} (h : ∀ x ∈ s, f x = 1) : (∏ x in s, f x) = 1 :=
calc (∏ x in s, f x) = ∏ x in s, 1 : finset.prod_congr rfl h
  ... = 1 : finset.prod_const_one

@[to_additive]
lemma prod_subset_one_on_sdiff [decidable_eq α] (h : s₁ ⊆ s₂) (hg : ∀ x ∈ (s₂ \ s₁), g x = 1)
  (hfg : ∀ x ∈ s₁, f x = g x) : ∏ i in s₁, f i = ∏ i in s₂, g i :=
begin
  rw [← prod_sdiff h, prod_eq_one hg, one_mul],
  exact prod_congr rfl hfg
end

@[to_additive]
lemma prod_subset (h : s₁ ⊆ s₂) (hf : ∀ x ∈ s₂, x ∉ s₁ → f x = 1) :
  (∏ x in s₁, f x) = ∏ x in s₂, f x :=
by haveI := classical.dec_eq α; exact prod_subset_one_on_sdiff h (by simpa) (λ _ _, rfl)

@[to_additive]
lemma prod_filter_of_ne {p : α → Prop} [decidable_pred p] (hp : ∀ x ∈ s, f x ≠ 1 → p x) :
  (∏ x in (s.filter p), f x) = (∏ x in s, f x) :=
prod_subset (filter_subset _ _) $ λ x,
  by { classical, rw [not_imp_comm, mem_filter], exact λ h₁ h₂, ⟨h₁, hp _ h₁ h₂⟩ }

-- If we use `[decidable_eq β]` here, some rewrites fail because they find a wrong `decidable`
-- instance first; `{∀ x, decidable (f x ≠ 1)}` doesn't work with `rw ← prod_filter_ne_one`
@[to_additive]
lemma prod_filter_ne_one [∀ x, decidable (f x ≠ 1)] :
  (∏ x in (s.filter $ λ x, f x ≠ 1), f x) = (∏ x in s, f x) :=
prod_filter_of_ne $ λ _ _, id

@[to_additive]
lemma prod_filter (p : α → Prop) [decidable_pred p] (f : α → β) :
  (∏ a in s.filter p, f a) = (∏ a in s, if p a then f a else 1) :=
calc (∏ a in s.filter p, f a) = ∏ a in s.filter p, if p a then f a else 1 :
    prod_congr rfl (assume a h, by rw [if_pos (mem_filter.1 h).2])
  ... = ∏ a in s, if p a then f a else 1 :
    begin
      refine prod_subset (filter_subset _ s) (assume x hs h, _),
      rw [mem_filter, not_and] at h,
      exact if_neg (h hs)
    end

@[to_additive]
lemma prod_eq_single_of_mem {s : finset α} {f : α → β} (a : α) (h : a ∈ s)
  (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) : (∏ x in s, f x) = f a :=
begin
  haveI := classical.dec_eq α,
  calc (∏ x in s, f x) = ∏ x in {a}, f x :
      begin
        refine (prod_subset _ _).symm,
        { intros _ H, rwa mem_singleton.1 H },
        { simpa only [mem_singleton] }
      end
      ... = f a : prod_singleton
end

@[to_additive]
lemma prod_eq_single {s : finset α} {f : α → β} (a : α)
  (h₀ : ∀ b ∈ s, b ≠ a → f b = 1) (h₁ : a ∉ s → f a = 1) : (∏ x in s, f x) = f a :=
by haveI := classical.dec_eq α;
from classical.by_cases
  (assume : a ∈ s, prod_eq_single_of_mem a this h₀)
  (assume : a ∉ s,
    (prod_congr rfl $ λ b hb, h₀ b hb $ by rintro rfl; cc).trans $
      prod_const_one.trans (h₁ this).symm)

@[to_additive]
lemma prod_eq_mul_of_mem {s : finset α} {f : α → β} (a b : α) (ha : a ∈ s) (hb : b ∈ s) (hn : a ≠ b)
  (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : (∏ x in s, f x) = (f a) * (f b) :=
begin
  haveI := classical.dec_eq α;
  let s' := ({a, b} : finset α),
  have hu : s' ⊆ s,
  { refine insert_subset.mpr _, apply and.intro ha, apply singleton_subset_iff.mpr hb },
  have hf : ∀ c ∈ s, c ∉ s' → f c = 1,
  { intros c hc hcs,
    apply h₀ c hc,
    apply not_or_distrib.mp,
    intro hab,
    apply hcs,
    apply mem_insert.mpr,
    rw mem_singleton,
    exact hab },
  rw ←prod_subset hu hf,
  exact finset.prod_pair hn
end

@[to_additive]
lemma prod_eq_mul {s : finset α} {f : α → β} (a b : α) (hn : a ≠ b)
  (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) (ha : a ∉ s → f a = 1) (hb : b ∉ s → f b = 1) :
  (∏ x in s, f x) = (f a) * (f b) :=
begin
  haveI := classical.dec_eq α;
  by_cases h₁ : a ∈ s; by_cases h₂ : b ∈ s,
  { exact prod_eq_mul_of_mem a b h₁ h₂ hn h₀ },
  { rw [hb h₂, mul_one],
    apply prod_eq_single_of_mem a h₁,
    exact λ c hc hca, h₀ c hc ⟨hca, ne_of_mem_of_not_mem hc h₂⟩ },
  { rw [ha h₁, one_mul],
    apply prod_eq_single_of_mem b h₂,
    exact λ c hc hcb, h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, hcb⟩ },
  { rw [ha h₁, hb h₂, mul_one],
    exact trans
      (prod_congr rfl (λ c hc, h₀ c hc ⟨ne_of_mem_of_not_mem hc h₁, ne_of_mem_of_not_mem hc h₂⟩))
      prod_const_one }
end

@[to_additive]
lemma prod_attach {f : α → β} : (∏ x in s.attach, f x) = (∏ x in s, f x) :=
by haveI := classical.dec_eq α; exact
  calc (∏ x in s.attach, f x.val) = (∏ x in (s.attach).image subtype.val, f x) :
    by rw [prod_image]; exact assume x _ y _, subtype.eq
  ... = _ : by rw [attach_image_val]

/-- A product over `s.subtype p` equals one over `s.filter p`. -/
@[simp, to_additive "A sum over `s.subtype p` equals one over `s.filter p`."]
lemma prod_subtype_eq_prod_filter (f : α → β) {p : α → Prop} [decidable_pred p] :
  ∏ x in s.subtype p, f x = ∏ x in s.filter p, f x :=
begin
  conv_lhs { erw ←prod_map (s.subtype p) (function.embedding.subtype _) f },
  exact prod_congr (subtype_map _) (λ x hx, rfl)
end

/-- If all elements of a `finset` satisfy the predicate `p`, a product
over `s.subtype p` equals that product over `s`. -/
@[to_additive "If all elements of a `finset` satisfy the predicate `p`, a sum
over `s.subtype p` equals that sum over `s`."]
lemma prod_subtype_of_mem (f : α → β) {p : α → Prop} [decidable_pred p]
    (h : ∀ x ∈ s, p x) : ∏ x in s.subtype p, f x = ∏ x in s, f x :=
by simp_rw [prod_subtype_eq_prod_filter, filter_true_of_mem h]

/-- A product of a function over a `finset` in a subtype equals a
product in the main type of a function that agrees with the first
function on that `finset`. -/
@[to_additive "A sum of a function over a `finset` in a subtype equals a
sum in the main type of a function that agrees with the first
function on that `finset`."]
lemma prod_subtype_map_embedding {p : α → Prop} {s : finset {x // p x}} {f : {x // p x} → β}
    {g : α → β} (h : ∀ x : {x // p x}, x ∈ s → g x = f x) :
  ∏ x in s.map (function.embedding.subtype _), g x = ∏ x in s, f x :=
begin
  rw finset.prod_map,
  exact finset.prod_congr rfl h
end

@[to_additive]
lemma prod_finset_coe (f : α → β) (s : finset α) :
  ∏ (i : (s : set α)), f i = ∏ i in s, f i :=
prod_attach

@[to_additive]
lemma prod_subtype {p : α → Prop} {F : fintype (subtype p)} (s : finset α)
  (h : ∀ x, x ∈ s ↔ p x) (f : α → β) :
  ∏ a in s, f a = ∏ a : subtype p, f a :=
have (∈ s) = p, from set.ext h, by { substI p, rw [←prod_finset_coe], congr }

@[to_additive] lemma prod_apply_dite {s : finset α} {p : α → Prop} {hp : decidable_pred p}
  [decidable_pred (λ x, ¬ p x)] (f : Π (x : α), p x → γ) (g : Π (x : α), ¬p x → γ)
  (h : γ → β) :
  (∏ x in s, h (if hx : p x then f x hx else g x hx)) =
  (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, h (g x.1 (mem_filter.mp x.2).2)) :=
calc ∏ x in s, h (if hx : p x then f x hx else g x hx)
    = (∏ x in s.filter p, h (if hx : p x then f x hx else g x hx)) *
    (∏ x in s.filter (λ x, ¬ p x), h (if hx : p x then f x hx else g x hx)) :
  (prod_filter_mul_prod_filter_not s p _).symm
... = (∏ x in (s.filter p).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, h (if hx : p x.1 then f x.1 hx else g x.1 hx)) :
  congr_arg2 _ prod_attach.symm prod_attach.symm
... = (∏ x in (s.filter p).attach, h (f x.1 (mem_filter.mp x.2).2)) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, h (g x.1 (mem_filter.mp x.2).2)) :
  congr_arg2 _
    (prod_congr rfl (λ x hx, congr_arg h (dif_pos (mem_filter.mp x.2).2)))
    (prod_congr rfl (λ x hx, congr_arg h (dif_neg (mem_filter.mp x.2).2)))

@[to_additive] lemma prod_apply_ite {s : finset α}
  {p : α → Prop} {hp : decidable_pred p} (f g : α → γ) (h : γ → β) :
  (∏ x in s, h (if p x then f x else g x)) =
  (∏ x in s.filter p, h (f x)) * (∏ x in s.filter (λ x, ¬ p x), h (g x)) :=
trans (prod_apply_dite _ _ _)
  (congr_arg2 _ (@prod_attach _ _ _ _ (h ∘ f)) (@prod_attach _ _ _ _ (h ∘ g)))

@[to_additive] lemma prod_dite {s : finset α} {p : α → Prop} {hp : decidable_pred p}
  (f : Π (x : α), p x → β) (g : Π (x : α), ¬p x → β) :
  (∏ x in s, if hx : p x then f x hx else g x hx) =
  (∏ x in (s.filter p).attach, f x.1 (mem_filter.mp x.2).2) *
    (∏ x in (s.filter (λ x, ¬ p x)).attach, g x.1 (mem_filter.mp x.2).2) :=
by simp [prod_apply_dite _ _ (λ x, x)]

@[to_additive] lemma prod_ite {s : finset α}
  {p : α → Prop} {hp : decidable_pred p} (f g : α → β) :
  (∏ x in s, if p x then f x else g x) =
  (∏ x in s.filter p, f x) * (∏ x in s.filter (λ x, ¬ p x), g x) :=
by simp [prod_apply_ite _ _ (λ x, x)]

@[to_additive] lemma prod_ite_of_false {p : α → Prop} {hp : decidable_pred p} (f g : α → β)
  (h : ∀ x ∈ s, ¬p x) : (∏ x in s, if p x then f x else g x) = (∏ x in s, g x) :=
by { rw prod_ite, simp [filter_false_of_mem h, filter_true_of_mem h] }

@[to_additive] lemma prod_ite_of_true {p : α → Prop} {hp : decidable_pred p} (f g : α → β)
  (h : ∀ x ∈ s, p x) : (∏ x in s, if p x then f x else g x) = (∏ x in s, f x) :=
by { simp_rw ←(ite_not (p _)), apply prod_ite_of_false, simpa }

@[to_additive] lemma prod_apply_ite_of_false {p : α → Prop} {hp : decidable_pred p} (f g : α → γ)
  (k : γ → β) (h : ∀ x ∈ s, ¬p x) :
  (∏ x in s, k (if p x then f x else g x)) = (∏ x in s, k (g x)) :=
by { simp_rw apply_ite k, exact prod_ite_of_false _ _ h }

@[to_additive] lemma prod_apply_ite_of_true {p : α → Prop} {hp : decidable_pred p} (f g : α → γ)
  (k : γ → β) (h : ∀ x ∈ s, p x) :
  (∏ x in s, k (if p x then f x else g x)) = (∏ x in s, k (f x)) :=
by { simp_rw apply_ite k, exact prod_ite_of_true _ _ h }

@[to_additive]
lemma prod_extend_by_one [decidable_eq α] (s : finset α) (f : α → β) :
  ∏ i in s, (if i ∈ s then f i else 1) = ∏ i in s, f i :=
prod_congr rfl $ λ i hi, if_pos hi

@[simp, to_additive]
lemma prod_dite_eq [decidable_eq α] (s : finset α) (a : α) (b : Π x : α, a = x → β) :
  (∏ x in s, (if h : a = x then b x h else 1)) = ite (a ∈ s) (b a rfl) 1 :=
begin
  split_ifs with h,
  { rw [finset.prod_eq_single a, dif_pos rfl],
    { intros, rw dif_neg, cc },
    { cc } },
  { rw finset.prod_eq_one,
    intros, rw dif_neg, intro, cc }
end

@[simp, to_additive]
lemma prod_dite_eq' [decidable_eq α] (s : finset α) (a : α) (b : Π x : α, x = a → β) :
  (∏ x in s, (if h : x = a then b x h else 1)) = ite (a ∈ s) (b a rfl) 1 :=
begin
  split_ifs with h,
  { rw [finset.prod_eq_single a, dif_pos rfl],
    { intros, rw dif_neg, cc },
    { cc } },
  { rw finset.prod_eq_one,
    intros, rw dif_neg, intro, cc }
end

@[simp, to_additive] lemma prod_ite_eq [decidable_eq α] (s : finset α) (a : α) (b : α → β) :
  (∏ x in s, (ite (a = x) (b x) 1)) = ite (a ∈ s) (b a) 1 :=
prod_dite_eq s a (λ x _, b x)

/--
  When a product is taken over a conditional whose condition is an equality test on the index
  and whose alternative is 1, then the product's value is either the term at that index or `1`.

  The difference with `prod_ite_eq` is that the arguments to `eq` are swapped.
-/
@[simp, to_additive] lemma prod_ite_eq' [decidable_eq α] (s : finset α) (a : α) (b : α → β) :
  (∏ x in s, (ite (x = a) (b x) 1)) = ite (a ∈ s) (b a) 1 :=
prod_dite_eq' s a (λ x _, b x)

@[to_additive]
lemma prod_ite_index (p : Prop) [decidable p] (s t : finset α) (f : α → β) :
  (∏ x in if p then s else t, f x) = if p then ∏ x in s, f x else ∏ x in t, f x :=
apply_ite (λ s, ∏ x in s, f x) _ _ _

@[simp, to_additive]
lemma prod_dite_irrel (p : Prop) [decidable p] (s : finset α) (f : p → α → β) (g : ¬p → α → β):
  (∏ x in s, if h : p then f h x else g h x) = if h : p then ∏ x in s, f h x else ∏ x in s, g h x :=
by { split_ifs with h; refl }

@[simp] lemma sum_pi_single' {ι M : Type*} [decidable_eq ι] [add_comm_monoid M]
  (i : ι) (x : M) (s : finset ι) :
  ∑ j in s, pi.single i x j = if i ∈ s then x else 0 :=
sum_dite_eq' _ _ _

@[simp] lemma sum_pi_single {ι : Type*} {M : ι → Type*}
  [decidable_eq ι] [Π i, add_comm_monoid (M i)] (i : ι) (f : Π i, M i) (s : finset ι) :
  ∑ j in s, pi.single j (f j) i = if i ∈ s then f i else 0 :=
sum_dite_eq _ _ _

@[to_additive]
lemma prod_bij_ne_one {s : finset α} {t : finset γ} {f : α → β} {g : γ → β}
  (i : Π a ∈ s, f a ≠ 1 → γ) (hi : ∀ a h₁ h₂, i a h₁ h₂ ∈ t)
  (i_inj : ∀ a₁ a₂ h₁₁ h₁₂ h₂₁ h₂₂, i a₁ h₁₁ h₁₂ = i a₂ h₂₁ h₂₂ → a₁ = a₂)
  (i_surj : ∀ b ∈ t, g b ≠ 1 → ∃ a h₁ h₂, b = i a h₁ h₂)
  (h : ∀ a h₁ h₂, f a = g (i a h₁ h₂)) :
  (∏ x in s, f x) = (∏ x in t, g x) :=
by classical; exact
calc (∏ x in s, f x) = ∏ x in (s.filter $ λ x, f x ≠ 1), f x : prod_filter_ne_one.symm
  ... = ∏ x in (t.filter $ λ x, g x ≠ 1), g x :
    prod_bij (assume a ha, i a (mem_filter.mp ha).1 (mem_filter.mp ha).2)
      (assume a ha, (mem_filter.mp ha).elim $ λ h₁ h₂, mem_filter.mpr
        ⟨hi a h₁ h₂, λ hg, h₂ (hg ▸ h a h₁ h₂)⟩)
      (assume a ha, (mem_filter.mp ha).elim $ h a)
      (assume a₁ a₂ ha₁ ha₂,
        (mem_filter.mp ha₁).elim $ λ ha₁₁ ha₁₂,
          (mem_filter.mp ha₂).elim $ λ ha₂₁ ha₂₂, i_inj a₁ a₂ _ _ _ _)
      (assume b hb, (mem_filter.mp hb).elim $ λ h₁ h₂,
        let ⟨a, ha₁, ha₂, eq⟩ := i_surj b h₁ h₂ in ⟨a, mem_filter.mpr ⟨ha₁, ha₂⟩, eq⟩)
  ... = (∏ x in t, g x) : prod_filter_ne_one

@[to_additive] lemma prod_dite_of_false {p : α → Prop} {hp : decidable_pred p}
  (h : ∀ x ∈ s, ¬ p x) (f : Π (x : α), p x → β) (g : Π (x : α), ¬p x → β) :
  (∏ x in s, if hx : p x then f x hx else g x hx) =
  ∏ (x : s), g x.val (h x.val x.property) :=
prod_bij (λ x hx, ⟨x,hx⟩) (λ x hx, by simp) (λ a ha, by { dsimp, rw dif_neg })
  (λ a₁ a₂ h₁ h₂ hh, congr_arg coe hh) (λ b hb, ⟨b.1, b.2, by simp⟩)

@[to_additive] lemma prod_dite_of_true {p : α → Prop} {hp : decidable_pred p}
  (h : ∀ x ∈ s, p x) (f : Π (x : α), p x → β) (g : Π (x : α), ¬p x → β) :
  (∏ x in s, if hx : p x then f x hx else g x hx) =
  ∏ (x : s), f x.val (h x.val x.property) :=
prod_bij (λ x hx, ⟨x,hx⟩) (λ x hx, by simp) (λ a ha, by { dsimp, rw dif_pos })
  (λ a₁ a₂ h₁ h₂ hh, congr_arg coe hh) (λ b hb, ⟨b.1, b.2, by simp⟩)

@[to_additive]
lemma nonempty_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : s.nonempty :=
s.eq_empty_or_nonempty.elim (λ H, false.elim $ h $ H.symm ▸ prod_empty) id

@[to_additive]
lemma exists_ne_one_of_prod_ne_one (h : (∏ x in s, f x) ≠ 1) : ∃ a ∈ s, f a ≠ 1 :=
begin
  classical,
  rw ← prod_filter_ne_one at h,
  rcases nonempty_of_prod_ne_one h with ⟨x, hx⟩,
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩
end

@[to_additive]
lemma prod_range_succ_comm (f : ℕ → β) (n : ℕ) :
  ∏ x in range (n + 1), f x = f n * ∏ x in range n, f x :=
by rw [range_succ, prod_insert not_mem_range_self]

@[to_additive]
lemma prod_range_succ (f : ℕ → β) (n : ℕ) :
  ∏ x in range (n + 1), f x = (∏ x in range n, f x) * f n :=
by simp only [mul_comm, prod_range_succ_comm]

@[to_additive]
lemma prod_range_succ' (f : ℕ → β) :
  ∀ n : ℕ, (∏ k in range (n + 1), f k) = (∏ k in range n, f (k+1)) * f 0
| 0       := prod_range_succ _ _
| (n + 1) := by rw [prod_range_succ _ n, mul_right_comm, ← prod_range_succ', prod_range_succ]

@[to_additive]
lemma eventually_constant_prod {u : ℕ → β} {N : ℕ} (hu : ∀ n ≥ N, u n = 1) {n : ℕ} (hn : N ≤ n) :
  ∏ k in range (n + 1), u k = ∏ k in range (N + 1), u k :=
begin
  obtain ⟨m, rfl : n = N + m⟩ := le_iff_exists_add.mp hn,
  clear hn,
  induction m with m hm,
  { simp },
  erw [prod_range_succ, hm],
  simp [hu]
end

@[to_additive]
lemma prod_range_add (f : ℕ → β) (n m : ℕ) :
  ∏ x in range (n + m), f x =
  (∏ x in range n, f x) * (∏ x in range m, f (n + x)) :=
begin
  induction m with m hm,
  { simp },
  { rw [nat.add_succ, prod_range_succ, hm, prod_range_succ, mul_assoc], },
end

@[to_additive]
lemma prod_range_add_div_prod_range {α : Type*} [comm_group α] (f : ℕ → α) (n m : ℕ) :
  (∏ k in range (n + m), f k) / (∏ k in range n, f k) = ∏ k in finset.range m, f (n + k) :=
div_eq_of_eq_mul' (prod_range_add f n m)

@[to_additive]
lemma prod_range_zero (f : ℕ → β) :
  ∏ k in range 0, f k = 1 :=
by rw [range_zero, prod_empty]

@[to_additive sum_range_one]
lemma prod_range_one (f : ℕ → β) :
  ∏ k in range 1, f k = f 0 :=
by { rw [range_one], apply @prod_singleton β ℕ 0 f }

open multiset

@[to_additive] lemma prod_multiset_map_count [decidable_eq α] (s : multiset α)
  {M : Type*} [comm_monoid M] (f : α → M) :
  (s.map f).prod = ∏ m in s.to_finset, (f m) ^ (s.count m) :=
begin
  induction s using multiset.induction_on with a s ih,
  { simp only [prod_const_one, count_zero, prod_zero, pow_zero, multiset.map_zero] },
  simp only [multiset.prod_cons, map_cons, to_finset_cons, ih],
  by_cases has : a ∈ s.to_finset,
  { rw [insert_eq_of_mem has, ← insert_erase has, prod_insert (not_mem_erase _ _),
        prod_insert (not_mem_erase _ _), ← mul_assoc, count_cons_self, pow_succ],
    congr' 1, refine prod_congr rfl (λ x hx, _),
    rw [count_cons_of_ne (ne_of_mem_erase hx)] },
  rw [prod_insert has, count_cons_self, count_eq_zero_of_not_mem (mt mem_to_finset.2 has), pow_one],
  congr' 1, refine prod_congr rfl (λ x hx, _),
  rw count_cons_of_ne,
  rintro rfl, exact has hx
end

@[to_additive]
lemma prod_multiset_count [decidable_eq α] [comm_monoid α] (s : multiset α) :
  s.prod = ∏ m in s.to_finset, m ^ (s.count m) :=
by { convert prod_multiset_map_count s id, rw map_id }

@[to_additive]
lemma prod_multiset_count_of_subset [decidable_eq α] [comm_monoid α]
  (m : multiset α) (s : finset α) (hs : m.to_finset ⊆ s) :
  m.prod = ∏ i in s, i ^ (m.count i) :=
begin
  rw prod_multiset_count,
  apply prod_subset hs,
  rintros x - hx,
  rw [mem_to_finset] at hx,
  rw [count_eq_zero_of_not_mem hx, pow_zero],
end

@[to_additive] lemma prod_mem_multiset [decidable_eq α]
  (m : multiset α) (f : {x // x ∈ m} → β) (g : α → β)
  (hfg : ∀ x, f x = g x) :
  ∏ (x : {x // x ∈ m}), f x = ∏ x in m.to_finset, g x :=
prod_bij (λ x _, x.1) (λ x _, multiset.mem_to_finset.mpr x.2)
  (λ _ _, hfg _)
  (λ _ _ _ _ h, by { ext, assumption })
  (λ y hy, ⟨⟨y, multiset.mem_to_finset.mp hy⟩, finset.mem_univ _, rfl⟩)

/--
To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[to_additive "To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands."]
lemma prod_induction {M : Type*} [comm_monoid M] (f : α → M) (p : M → Prop)
  (p_mul : ∀ a b, p a → p b → p (a * b)) (p_one : p 1) (p_s : ∀ x ∈ s, p $ f x) :
  p $ ∏ x in s, f x :=
multiset.prod_induction _ _ p_mul p_one (multiset.forall_mem_map_iff.mpr p_s)

/--
To prove a property of a product, it suffices to prove that
the property is multiplicative and holds on factors.
-/
@[to_additive "To prove a property of a sum, it suffices to prove that
the property is additive and holds on summands."]
lemma prod_induction_nonempty {M : Type*} [comm_monoid M] (f : α → M) (p : M → Prop)
  (p_mul : ∀ a b, p a → p b → p (a * b)) (hs_nonempty : s.nonempty) (p_s : ∀ x ∈ s, p $ f x) :
  p $ ∏ x in s, f x :=
multiset.prod_induction_nonempty p p_mul (by simp [nonempty_iff_ne_empty.mp hs_nonempty])
  (multiset.forall_mem_map_iff.mpr p_s)

/--
For any product along `{0, ..., n-1}` of a commutative-monoid-valued function, we can verify that
it's equal to a different function just by checking ratios of adjacent terms.
This is a multiplicative discrete analogue of the fundamental theorem of calculus. -/
lemma prod_range_induction {M : Type*} [comm_monoid M]
  (f s : ℕ → M) (h0 : s 0 = 1) (h : ∀ n, s (n + 1) = s n * f n) (n : ℕ) :
  ∏ k in finset.range n, f k = s n :=
begin
  induction n with k hk,
  { simp only [h0, finset.prod_range_zero] },
  { simp only [hk, finset.prod_range_succ, h, mul_comm] }
end

/--
For any sum along `{0, ..., n-1}` of a commutative-monoid-valued function,
we can verify that it's equal to a different function
just by checking differences of adjacent terms.
This is a discrete analogue
of the fundamental theorem of calculus.
-/
lemma sum_range_induction {M : Type*} [add_comm_monoid M]
  (f s : ℕ → M) (h0 : s 0 = 0) (h : ∀ n, s (n + 1) = s n + f n) (n : ℕ) :
  ∑ k in finset.range n, f k = s n :=
@prod_range_induction (multiplicative M) _ f s h0 h n

/-- A telescoping sum along `{0, ..., n-1}` of an additive commutative group valued function
reduces to the difference of the last and first terms.-/
lemma sum_range_sub {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  ∑ i in range n, (f (i+1) - f i) = f n - f 0 :=
by { apply sum_range_induction; simp }

lemma sum_range_sub' {G : Type*} [add_comm_group G] (f : ℕ → G) (n : ℕ) :
  ∑ i in range n, (f i - f (i+1)) = f 0 - f n :=
by { apply sum_range_induction; simp }

/-- A telescoping product along `{0, ..., n-1}` of a commutative group valued function
reduces to the ratio of the last and first factors.-/
@[to_additive]
lemma prod_range_div {M : Type*} [comm_group M] (f : ℕ → M) (n : ℕ) :
  ∏ i in range n, (f (i+1) * (f i)⁻¹) = f n * (f 0)⁻¹ :=
by simpa only [← div_eq_mul_inv] using @sum_range_sub (additive M) _ f n

@[to_additive]
lemma prod_range_div' {M : Type*} [comm_group M] (f : ℕ → M) (n : ℕ) :
  ∏ i in range n, (f i * (f (i+1))⁻¹) = (f 0) * (f n)⁻¹ :=
by simpa only [← div_eq_mul_inv] using @sum_range_sub' (additive M) _ f n

/--
A telescoping sum along `{0, ..., n-1}` of an `ℕ`-valued function
reduces to the difference of the last and first terms
when the function we are summing is monotone.
-/
lemma sum_range_sub_of_monotone {f : ℕ → ℕ} (h : monotone f) (n : ℕ) :
  ∑ i in range n, (f (i+1) - f i) = f n - f 0 :=
begin
  refine sum_range_induction _ _ (tsub_self _) (λ n, _) _,
  have h₁ : f n ≤ f (n+1) := h (nat.le_succ _),
  have h₂ : f 0 ≤ f n := h (nat.zero_le _),
  rw [tsub_add_eq_add_tsub h₂, add_tsub_cancel_of_le h₁],
end

@[simp, to_additive] lemma prod_const (b : β) : (∏ x in s, b) = b ^ s.card :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (λ a s has ih,
by rw [prod_insert has, card_insert_of_not_mem has, pow_succ, ih])

@[to_additive]
lemma pow_eq_prod_const (b : β) : ∀ n, b ^ n = ∏ k in range n, b := by simp

@[to_additive sum_nsmul]
lemma prod_pow (s : finset α) (n : ℕ) (f : α → β) :
  ∏ x in s, f x ^ n = (∏ x in s, f x) ^ n :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp) (by simp [mul_pow] {contextual := tt})

@[to_additive]
lemma prod_flip {n : ℕ} (f : ℕ → β) :
  ∏ r in range (n + 1), f (n - r) = ∏ k in range (n + 1), f k :=
begin
  induction n with n ih,
  { rw [prod_range_one, prod_range_one] },
  { rw [prod_range_succ', prod_range_succ _ (nat.succ n)],
    simp [← ih] }
end

@[to_additive]
lemma prod_involution {s : finset α} {f : α → β} :
  ∀ (g : Π a ∈ s, α)
  (h : ∀ a ha, f a * f (g a ha) = 1)
  (g_ne : ∀ a ha, f a ≠ 1 → g a ha ≠ a)
  (g_mem : ∀ a ha, g a ha ∈ s)
  (g_inv : ∀ a ha, g (g a ha) (g_mem a ha) = a),
  (∏ x in s, f x) = 1 :=
by haveI := classical.dec_eq α;
haveI := classical.dec_eq β; exact
finset.strong_induction_on s
  (λ s ih g h g_ne g_mem g_inv,
    s.eq_empty_or_nonempty.elim (λ hs, hs.symm ▸ rfl)
      (λ ⟨x, hx⟩,
      have hmem : ∀ y ∈ (s.erase x).erase (g x hx), y ∈ s,
        from λ y hy, (mem_of_mem_erase (mem_of_mem_erase hy)),
      have g_inj : ∀ {x hx y hy}, g x hx = g y hy → x = y,
        from λ x hx y hy h, by rw [← g_inv x hx, ← g_inv y hy]; simp [h],
      have ih': ∏ y in erase (erase s x) (g x hx), f y = (1 : β) :=
        ih ((s.erase x).erase (g x hx))
          ⟨subset.trans (erase_subset _ _) (erase_subset _ _),
            λ h, not_mem_erase (g x hx) (s.erase x) (h (g_mem x hx))⟩
          (λ y hy, g y (hmem y hy))
          (λ y hy, h y (hmem y hy))
          (λ y hy, g_ne y (hmem y hy))
          (λ y hy, mem_erase.2 ⟨λ (h : g y _ = g x hx), by simpa [g_inj h] using hy,
            mem_erase.2 ⟨λ (h : g y _ = x),
              have y = g x hx, from g_inv y (hmem y hy) ▸ by simp [h],
              by simpa [this] using hy, g_mem y (hmem y hy)⟩⟩)
          (λ y hy, g_inv y (hmem y hy)),
      if hx1 : f x = 1
      then ih' ▸ eq.symm (prod_subset hmem
        (λ y hy hy₁,
          have y = x ∨ y = g x hx, by simp [hy] at hy₁; tauto,
          this.elim (λ hy, hy.symm ▸ hx1)
            (λ hy, h x hx ▸ hy ▸ hx1.symm ▸ (one_mul _).symm)))
      else by rw [← insert_erase hx, prod_insert (not_mem_erase _ _),
        ← insert_erase (mem_erase.2 ⟨g_ne x hx hx1, g_mem x hx⟩),
        prod_insert (not_mem_erase _ _), ih', mul_one, h x hx]))


/-- The product of the composition of functions `f` and `g`, is the product
over `b ∈ s.image g` of `f b` to the power of the cardinality of the fibre of `b`. See also
`finset.prod_image`. -/
lemma prod_comp [decidable_eq γ] (f : γ → β) (g : α → γ) :
  ∏ a in s, f (g a) = ∏ b in s.image g, f b ^ (s.filter (λ a, g a = b)).card  :=
calc ∏ a in s, f (g a)
    = ∏ x in (s.image g).sigma (λ b : γ, s.filter (λ a, g a = b)), f (g x.2) :
  prod_bij (λ a ha, ⟨g a, a⟩) (by simp; tauto) (λ _ _, rfl) (by simp) -- `(by finish)` closes this
  (by { rintro ⟨b_fst, b_snd⟩ H,
        simp only [mem_image, exists_prop, mem_filter, mem_sigma] at H,
        tauto })
... = ∏ b in s.image g, ∏ a in s.filter (λ a, g a = b), f (g a) : prod_sigma _ _ _
... = ∏ b in s.image g, ∏ a in s.filter (λ a, g a = b), f b :
  prod_congr rfl (λ b hb, prod_congr rfl (by simp {contextual := tt}))
... = ∏ b in s.image g, f b ^ (s.filter (λ a, g a = b)).card :
  prod_congr rfl (λ _ _, prod_const _)

@[to_additive]
lemma prod_piecewise [decidable_eq α] (s t : finset α) (f g : α → β) :
  (∏ x in s, (t.piecewise f g) x) = (∏ x in s ∩ t, f x) * (∏ x in s \ t, g x) :=
by { rw [piecewise, prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter], }

@[to_additive]
lemma prod_inter_mul_prod_diff [decidable_eq α] (s t : finset α) (f : α → β) :
  (∏ x in s ∩ t, f x) * (∏ x in s \ t, f x) = (∏ x in s, f x) :=
by { convert (s.prod_piecewise t f f).symm, simp [finset.piecewise] }

@[to_additive]
lemma prod_eq_mul_prod_diff_singleton [decidable_eq α] {s : finset α} {i : α} (h : i ∈ s)
  (f : α → β) : ∏ x in s, f x = f i * ∏ x in s \ {i}, f x :=
by { convert (s.prod_inter_mul_prod_diff {i} f).symm, simp [h] }

@[to_additive]
lemma prod_eq_prod_diff_singleton_mul [decidable_eq α] {s : finset α} {i : α} (h : i ∈ s)
  (f : α → β) : ∏ x in s, f x = (∏ x in s \ {i}, f x) * f i :=
by { rw [prod_eq_mul_prod_diff_singleton h, mul_comm] }

@[to_additive]
lemma _root_.fintype.prod_eq_mul_prod_compl [decidable_eq α] [fintype α] (a : α) (f : α → β) :
  ∏ i, f i = (f a) * ∏ i in {a}ᶜ, f i :=
prod_eq_mul_prod_diff_singleton (mem_univ a) f

@[to_additive]
lemma _root_.fintype.prod_eq_prod_compl_mul [decidable_eq α] [fintype α] (a : α) (f : α → β) :
  ∏ i, f i = (∏ i in {a}ᶜ, f i) * f a :=
prod_eq_prod_diff_singleton_mul (mem_univ a) f

lemma dvd_prod_of_mem (f : α → β) {a : α} {s : finset α} (ha : a ∈ s) :
  f a ∣ ∏ i in s, f i :=
begin
  classical,
  rw finset.prod_eq_mul_prod_diff_singleton ha,
  exact dvd_mul_right _ _,
end

/-- A product can be partitioned into a product of products, each equivalent under a setoid. -/
@[to_additive "A sum can be partitioned into a sum of sums, each equivalent under a setoid."]
lemma prod_partition (R : setoid α) [decidable_rel R.r] :
  (∏ x in s, f x) = ∏ xbar in s.image quotient.mk, ∏ y in s.filter (λ y, ⟦y⟧ = xbar), f y :=
begin
  refine (finset.prod_image' f (λ x hx, _)).symm,
  refl,
end

/-- If we can partition a product into subsets that cancel out, then the whole product cancels. -/
@[to_additive "If we can partition a sum into subsets that cancel out, then the whole sum cancels."]
lemma prod_cancels_of_partition_cancels (R : setoid α) [decidable_rel R.r]
  (h : ∀ x ∈ s, (∏ a in s.filter (λ y, y ≈ x), f a) = 1) : (∏ x in s, f x) = 1 :=
begin
  rw [prod_partition R, ←finset.prod_eq_one],
  intros xbar xbar_in_s,
  obtain ⟨x, x_in_s, xbar_eq_x⟩ := mem_image.mp xbar_in_s,
  rw [←xbar_eq_x, filter_congr (λ y _, @quotient.eq _ R y x)],
  apply h x x_in_s,
end

@[to_additive]
lemma prod_update_of_not_mem [decidable_eq α] {s : finset α} {i : α}
  (h : i ∉ s) (f : α → β) (b : β) : (∏ x in s, function.update f i b x) = (∏ x in s, f x) :=
begin
  apply prod_congr rfl (λ j hj, _),
  have : j ≠ i, by { assume eq, rw eq at hj, exact h hj },
  simp [this]
end

@[to_additive]
lemma prod_update_of_mem [decidable_eq α] {s : finset α} {i : α} (h : i ∈ s) (f : α → β) (b : β) :
  (∏ x in s, function.update f i b x) = b * (∏ x in s \ (singleton i), f x) :=
by { rw [update_eq_piecewise, prod_piecewise], simp [h] }

/-- If a product of a `finset` of size at most 1 has a given value, so
do the terms in that product. -/
@[to_additive eq_of_card_le_one_of_sum_eq "If a sum of a `finset` of size at most 1 has a given
value, so do the terms in that sum."]
lemma eq_of_card_le_one_of_prod_eq {s : finset α} (hc : s.card ≤ 1) {f : α → β} {b : β}
    (h : ∏ x in s, f x = b) : ∀ x ∈ s, f x = b :=
begin
  intros x hx,
  by_cases hc0 : s.card = 0,
  { exact false.elim (card_ne_zero_of_mem hx hc0) },
  { have h1 : s.card = 1 := le_antisymm hc (nat.one_le_of_lt (nat.pos_of_ne_zero hc0)),
    rw card_eq_one at h1,
    cases h1 with x2 hx2,
    rw [hx2, mem_singleton] at hx,
    simp_rw hx2 at h,
    rw hx,
    rw prod_singleton at h,
    exact h }
end

/-- Taking a product over `s : finset α` is the same as multiplying the value on a single element
`f a` by the product of `s.erase a`. -/
@[to_additive "Taking a sum over `s : finset α` is the same as adding the value on a single element
`f a` to the sum over `s.erase a`."]
lemma mul_prod_erase [decidable_eq α] (s : finset α) (f : α → β) {a : α} (h : a ∈ s) :
  f a * (∏ x in s.erase a, f x) = ∏ x in s, f x :=
by rw [← prod_insert (not_mem_erase a s), insert_erase h]

/-- A variant of `finset.mul_prod_erase` with the multiplication swapped. -/
@[to_additive "A variant of `finset.add_sum_erase` with the addition swapped."]
lemma prod_erase_mul [decidable_eq α] (s : finset α) (f : α → β) {a : α} (h : a ∈ s) :
  (∏ x in s.erase a, f x) * f a = ∏ x in s, f x :=
by rw [mul_comm, mul_prod_erase s f h]

/-- If a function applied at a point is 1, a product is unchanged by
removing that point, if present, from a `finset`. -/
@[to_additive "If a function applied at a point is 0, a sum is unchanged by
removing that point, if present, from a `finset`."]
lemma prod_erase [decidable_eq α] (s : finset α) {f : α → β} {a : α} (h : f a = 1) :
  ∏ x in s.erase a, f x = ∏ x in s, f x :=
begin
  rw ←sdiff_singleton_eq_erase,
  refine prod_subset (sdiff_subset _ _) (λ x hx hnx, _),
  rw sdiff_singleton_eq_erase at hnx,
  rwa eq_of_mem_of_not_mem_erase hx hnx
end

/-- If a product is 1 and the function is 1 except possibly at one
point, it is 1 everywhere on the `finset`. -/
@[to_additive "If a sum is 0 and the function is 0 except possibly at one
point, it is 0 everywhere on the `finset`."]
lemma eq_one_of_prod_eq_one {s : finset α} {f : α → β} {a : α} (hp : ∏ x in s, f x = 1)
    (h1 : ∀ x ∈ s, x ≠ a → f x = 1) : ∀ x ∈ s, f x = 1 :=
begin
  intros x hx,
  classical,
  by_cases h : x = a,
  { rw h,
    rw h at hx,
    rw [←prod_subset (singleton_subset_iff.2 hx)
                      (λ t ht ha, h1 t ht (not_mem_singleton.1 ha)),
        prod_singleton] at hp,
    exact hp },
  { exact h1 x hx h }
end

lemma prod_pow_boole [decidable_eq α] (s : finset α) (f : α → β) (a : α) :
  (∏ x in s, (f x)^(ite (a = x) 1 0)) = ite (a ∈ s) (f a) 1 :=
by simp

lemma prod_dvd_prod_of_dvd {S : finset α} (g1 g2 : α → β) (h : ∀ a ∈ S, g1 a ∣ g2 a) :
  S.prod g1 ∣ S.prod g2 :=
begin
  classical,
  apply finset.induction_on' S, { simp },
  intros a T haS _ haT IH,
  repeat {rw finset.prod_insert haT},
  exact mul_dvd_mul (h a haS) IH,
end

end comm_monoid

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
lemma prod_add_prod_eq [comm_semiring β] {s : finset α} {i : α} {f g h : α → β}
  (hi : i ∈ s) (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j)
  (h3 : ∀ j ∈ s, j ≠ i → h j = f j) : ∏ i in s, g i + ∏ i in s, h i = ∏ i in s, f i :=
by { classical, simp_rw [prod_eq_mul_prod_diff_singleton hi, ← h1, right_distrib],
     congr' 2; apply prod_congr rfl; simpa }

lemma card_eq_sum_ones (s : finset α) : s.card = ∑ _ in s, 1 :=
by simp

lemma sum_const_nat {m : ℕ} {f : α → ℕ} (h₁ : ∀ x ∈ s, f x = m) :
  (∑ x in s, f x) = card s * m :=
begin
  rw [← nat.nsmul_eq_mul, ← sum_const],
  apply sum_congr rfl h₁
end

@[simp]
lemma sum_boole {s : finset α} {p : α → Prop} [non_assoc_semiring β] {hp : decidable_pred p} :
  (∑ x in s, if p x then (1 : β) else (0 : β)) = (s.filter p).card :=
by simp [sum_ite]

lemma sum_comp [add_comm_monoid β] [decidable_eq γ] (f : γ → β) (g : α → γ) :
  ∑ a in s, f (g a) = ∑ b in s.image g, (s.filter (λ a, g a = b)).card • (f b) :=
@prod_comp (multiplicative β) _ _ _ _ _ _ _
attribute [to_additive "The sum of the composition of functions `f` and `g`, is the sum
over `b ∈ s.image g` of `f b` times of the cardinality of the fibre of `b`. See also
`finset.sum_image`."] prod_comp

lemma eq_sum_range_sub [add_comm_group β] (f : ℕ → β) (n : ℕ) :
  f n = f 0 + ∑ i in range n, (f (i+1) - f i) :=
by rw [finset.sum_range_sub, add_sub_cancel'_right]

lemma eq_sum_range_sub' [add_comm_group β] (f : ℕ → β) (n : ℕ) :
  f n = ∑ i in range (n + 1), if i = 0 then f 0 else f i - f (i - 1) :=
begin
  conv_lhs { rw [finset.eq_sum_range_sub f] },
  simp [finset.sum_range_succ', add_comm]
end

section opposite

open mul_opposite

/-- Moving to the opposite additive commutative monoid commutes with summing. -/
@[simp] lemma op_sum [add_comm_monoid β] {s : finset α} (f : α → β) :
  op (∑ x in s, f x) = ∑ x in s, op (f x) :=
(op_add_equiv : β ≃+ βᵐᵒᵖ).map_sum _ _

@[simp] lemma unop_sum [add_comm_monoid β] {s : finset α} (f : α → βᵐᵒᵖ) :
  unop (∑ x in s, f x) = ∑ x in s, unop (f x) :=
(op_add_equiv : β ≃+ βᵐᵒᵖ).symm.map_sum _ _

end opposite

section comm_group
variables [comm_group β]

@[simp, to_additive]
lemma prod_inv_distrib : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ := multiset.prod_map_inv'

@[to_additive zsmul_sum]
lemma prod_zpow (f : α → β) (s : finset α) (n : ℤ) :
  (∏ a in s, f a) ^ n = ∏ a in s, (f a) ^ n :=
multiset.prod_map_zpow.symm

@[to_additive]
lemma prod_sdiff_div_prod_sdiff [decidable_eq α] :
  (∏ (x : α) in s₂ \ s₁, f x) / (∏ (x : α) in s₁ \ s₂, f x)
  = (∏ (x : α) in s₂, f x) / (∏ (x : α) in s₁, f x) :=
by simp [← finset.prod_sdiff (@inf_le_left _ _ s₁ s₂),
  ← finset.prod_sdiff (@inf_le_right _ _ s₁ s₂)]

end comm_group

@[simp] theorem card_sigma {σ : α → Type*} (s : finset α) (t : Π a, finset (σ a)) :
  card (s.sigma t) = ∑ a in s, card (t a) :=
multiset.card_sigma _ _

lemma card_bUnion [decidable_eq β] {s : finset α} {t : α → finset β}
  (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → disjoint (t x) (t y)) :
  (s.bUnion t).card = ∑ u in s, card (t u) :=
calc (s.bUnion t).card = ∑ i in s.bUnion t, 1 : by simp
... = ∑ a in s, ∑ i in t a, 1 : finset.sum_bUnion h
... = ∑ u in s, card (t u) : by simp

lemma card_bUnion_le [decidable_eq β] {s : finset α} {t : α → finset β} :
  (s.bUnion t).card ≤ ∑ a in s, (t a).card :=
by haveI := classical.dec_eq α; exact
finset.induction_on s (by simp)
  (λ a s has ih,
    calc ((insert a s).bUnion t).card ≤ (t a).card + (s.bUnion t).card :
    by rw bUnion_insert; exact finset.card_union_le _ _
    ... ≤ ∑ a in insert a s, card (t a) :
    by rw sum_insert has; exact add_le_add_left ih _)

theorem card_eq_sum_card_fiberwise [decidable_eq β] {f : α → β} {s : finset α} {t : finset β}
  (H : ∀ x ∈ s, f x ∈ t) :
  s.card = ∑ a in t, (s.filter (λ x, f x = a)).card :=
by simp only [card_eq_sum_ones, sum_fiberwise_of_maps_to H]

theorem card_eq_sum_card_image [decidable_eq β] (f : α → β) (s : finset α) :
  s.card = ∑ a in s.image f, (s.filter (λ x, f x = a)).card :=
card_eq_sum_card_fiberwise (λ _, mem_image_of_mem _)

@[simp] lemma sum_sub_distrib [add_comm_group β] :
  ∑ x in s, (f x - g x) = (∑ x in s, f x) - (∑ x in s, g x) :=
by simpa only [sub_eq_add_neg] using sum_add_distrib.trans (congr_arg _ sum_neg_distrib)

section prod_eq_zero
variables [comm_monoid_with_zero β]

lemma prod_eq_zero (ha : a ∈ s) (h : f a = 0) : (∏ x in s, f x) = 0 :=
by { haveI := classical.dec_eq α, rw [←prod_erase_mul _ _ ha, h, mul_zero] }

lemma prod_boole {s : finset α} {p : α → Prop} [decidable_pred p] :
  ∏ i in s, ite (p i) (1 : β) (0 : β) = ite (∀ i ∈ s, p i) 1 0 :=
begin
  split_ifs,
  { apply prod_eq_one,
    intros i hi,
    rw if_pos (h i hi) },
  { push_neg at h,
    rcases h with ⟨i, hi, hq⟩,
    apply prod_eq_zero hi,
    rw [if_neg hq] },
end

variables [nontrivial β] [no_zero_divisors β]

lemma prod_eq_zero_iff : (∏ x in s, f x) = 0 ↔ (∃ a ∈ s, f a = 0) :=
begin
  classical,
  apply finset.induction_on s,
  exact ⟨not.elim one_ne_zero, λ ⟨_, H, _⟩, H.elim⟩,
  assume a s ha ih,
  rw [prod_insert ha, mul_eq_zero, bex_def, exists_mem_insert, ih, ← bex_def]
end

theorem prod_ne_zero_iff : (∏ x in s, f x) ≠ 0 ↔ (∀ a ∈ s, f a ≠ 0) :=
by { rw [ne, prod_eq_zero_iff], push_neg }

end prod_eq_zero

section comm_group_with_zero
variables [comm_group_with_zero β]

@[simp]
lemma prod_inv_distrib' : (∏ x in s, (f x)⁻¹) = (∏ x in s, f x)⁻¹ :=
begin
  classical,
  by_cases h : ∃ x ∈ s, f x = 0,
  { simpa [prod_eq_zero_iff.mpr h, prod_eq_zero_iff] using h },
  { push_neg at h,
    have h' := prod_ne_zero_iff.mpr h,
    have hf : ∀ x ∈ s, (f x)⁻¹ * f x = 1 := λ x hx, inv_mul_cancel (h x hx),
    apply mul_right_cancel₀ h',
    simp [h, h', ← finset.prod_mul_distrib, prod_congr rfl hf] }
end

end comm_group_with_zero

@[to_additive]
lemma prod_unique_nonempty {α β : Type*} [comm_monoid β] [unique α]
  (s : finset α) (f : α → β) (h : s.nonempty) :
  (∏ x in s, f x) = f default :=
begin
  obtain ⟨a, ha⟩ := h,
  have : s = {a},
  { ext b,
    simpa [subsingleton.elim a b] using ha },
  rw [this, finset.prod_singleton, subsingleton.elim a default]
end

end finset

namespace fintype

open finset

/-- `fintype.prod_bijective` is a variant of `finset.prod_bij` that accepts `function.bijective`.

See `function.bijective.prod_comp` for a version without `h`. -/
@[to_additive "`fintype.sum_equiv` is a variant of `finset.sum_bij` that accepts
`function.bijective`.

See `function.bijective.sum_comp` for a version without `h`. "]
lemma prod_bijective {α β M : Type*} [fintype α] [fintype β] [comm_monoid M]
  (e : α → β) (he : function.bijective e) (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
  ∏ x : α, f x = ∏ x : β, g x :=
prod_bij
  (λ x _, e x)
  (λ x _, mem_univ (e x))
  (λ x _, h x)
  (λ x x' _ _ h, he.injective h)
  (λ y _, (he.surjective y).imp $ λ a h, ⟨mem_univ _, h.symm⟩)

/-- `fintype.prod_equiv` is a specialization of `finset.prod_bij` that
automatically fills in most arguments.

See `equiv.prod_comp` for a version without `h`.
-/
@[to_additive "`fintype.sum_equiv` is a specialization of `finset.sum_bij` that
automatically fills in most arguments.

See `equiv.sum_comp` for a version without `h`.
"]
lemma prod_equiv {α β M : Type*} [fintype α] [fintype β] [comm_monoid M]
  (e : α ≃ β) (f : α → M) (g : β → M) (h : ∀ x, f x = g (e x)) :
  ∏ x : α, f x = ∏ x : β, g x :=
prod_bijective e e.bijective f g h

@[to_additive]
lemma prod_finset_coe [comm_monoid β] :
  ∏ (i : (s : set α)), f i = ∏ i in s, f i :=
(finset.prod_subtype s (λ _, iff.rfl) f).symm

@[to_additive]
lemma prod_unique {α β : Type*} [comm_monoid β] [unique α] (f : α → β) :
  (∏ x : α, f x) = f default :=
by rw [univ_unique, prod_singleton]

@[to_additive] lemma prod_empty {α β : Type*} [comm_monoid β] [is_empty α] (f : α → β) :
  (∏ x : α, f x) = 1 :=
by rw [eq_empty_of_is_empty (univ : finset α), finset.prod_empty]

@[to_additive]
lemma prod_subsingleton {α β : Type*} [comm_monoid β] [subsingleton α] (f : α → β) (a : α) :
  (∏ x : α, f x) = f a :=
begin
  haveI : unique α := unique_of_subsingleton a,
  convert prod_unique f
end

@[to_additive]
lemma prod_subtype_mul_prod_subtype {α β : Type*} [fintype α] [comm_monoid β]
  (p : α → Prop) (f : α → β) [decidable_pred p] :
  (∏ (i : {x // p x}), f i) * (∏ i : {x // ¬ p x}, f i) = ∏ i, f i :=
begin
  classical,
  let s := {x | p x}.to_finset,
  rw [← finset.prod_subtype s, ← finset.prod_subtype sᶜ],
  { exact finset.prod_mul_prod_compl _ _ },
  { simp },
  { simp }
end

end fintype

namespace list

@[to_additive] lemma prod_to_finset {M : Type*} [decidable_eq α] [comm_monoid M]
  (f : α → M) : ∀ {l : list α} (hl : l.nodup), l.to_finset.prod f = (l.map f).prod
| [] _ := by simp
| (a :: l) hl := let ⟨not_mem, hl⟩ := list.nodup_cons.mp hl in
  by simp [finset.prod_insert (mt list.mem_to_finset.mp not_mem), prod_to_finset hl]

end list

namespace multiset

variables [decidable_eq α]

@[simp] lemma to_finset_sum_count_eq (s : multiset α) :
  (∑ a in s.to_finset, s.count a) = s.card :=
multiset.induction_on s rfl
  (assume a s ih,
    calc (∑ x in to_finset (a ::ₘ s), count x (a ::ₘ s)) =
      ∑ x in to_finset (a ::ₘ s), ((if x = a then 1 else 0) + count x s) :
        finset.sum_congr rfl $ λ _ _, by split_ifs;
        [simp only [h, count_cons_self, nat.one_add], simp only [count_cons_of_ne h, zero_add]]
      ... = card (a ::ₘ s) :
      begin
        by_cases a ∈ s.to_finset,
        { have : ∑ x in s.to_finset, ite (x = a) 1 0 = ∑ x in {a}, ite (x = a) 1 0,
          { rw [finset.sum_ite_eq', if_pos h, finset.sum_singleton, if_pos rfl], },
          rw [to_finset_cons, finset.insert_eq_of_mem h, finset.sum_add_distrib, ih, this,
            finset.sum_singleton, if_pos rfl, add_comm, card_cons] },
        { have ha : a ∉ s, by rwa mem_to_finset at h,
          have : ∑ x in to_finset s, ite (x = a) 1 0 = ∑ x in to_finset s, 0, from
            finset.sum_congr rfl (λ x hx, if_neg $ by rintro rfl; cc),
          rw [to_finset_cons, finset.sum_insert h, if_pos rfl, finset.sum_add_distrib, this,
            finset.sum_const_zero, ih, count_eq_zero_of_not_mem ha, zero_add, add_comm, card_cons] }
      end)

lemma count_sum' {s : finset β} {a : α} {f : β → multiset α} :
  count a (∑ x in s, f x) = ∑ x in s, count a (f x) :=
by { dunfold finset.sum, rw count_sum }

@[simp] lemma to_finset_sum_count_nsmul_eq (s : multiset α) :
  (∑ a in s.to_finset, s.count a • {a}) = s :=
begin
  apply ext', intro b,
  rw count_sum',
  have h : count b s = count b (count b s • {b}),
  { rw [count_nsmul, count_singleton_self, mul_one] },
  rw h, clear h,
  apply finset.sum_eq_single b,
  { intros c h hcb, rw count_nsmul, convert mul_zero (count c s),
    apply count_eq_zero.mpr, exact finset.not_mem_singleton.mpr (ne.symm hcb) },
  { intro hb, rw [count_eq_zero_of_not_mem (mt mem_to_finset.2 hb), count_nsmul, zero_mul]}
end

theorem exists_smul_of_dvd_count (s : multiset α) {k : ℕ}
  (h : ∀ (a : α), a ∈ s → k ∣ multiset.count a s) :
  ∃ (u : multiset α), s = k • u :=
begin
  use ∑ a in s.to_finset, (s.count a / k) • {a},
  have h₂ : ∑ (x : α) in s.to_finset, k • (count x s / k) • ({x} : multiset α) =
    ∑ (x : α) in s.to_finset, count x s • {x},
  { apply finset.sum_congr rfl,
    intros x hx,
    rw [← mul_nsmul, nat.mul_div_cancel' (h x (mem_to_finset.mp hx))] },
  rw [← finset.sum_nsmul, h₂, to_finset_sum_count_nsmul_eq]
end

lemma to_finset_prod_dvd_prod [comm_monoid α] (S : multiset α) : S.to_finset.prod id ∣ S.prod :=
begin
  rw finset.prod_eq_multiset_prod,
  refine multiset.prod_dvd_prod_of_le _,
  simp [multiset.erase_dup_le S],
end

@[to_additive]
lemma prod_sum {α : Type*} {ι : Type*} [comm_monoid α] (f : ι → multiset α) (s : finset ι) :
  (∑ x in s, f x).prod = ∏ x in s, (f x).prod :=
begin
  classical,
  induction s using finset.induction_on with a t hat ih,
  { rw [finset.sum_empty, finset.prod_empty, multiset.prod_zero] },
  { rw [finset.sum_insert hat, finset.prod_insert hat, multiset.prod_add, ih] }
end

end multiset

@[simp, norm_cast] lemma nat.cast_sum [add_comm_monoid β] [has_one β] (s : finset α) (f : α → ℕ) :
  ↑(∑ x in s, f x : ℕ) = (∑ x in s, (f x : β)) :=
(nat.cast_add_monoid_hom β).map_sum f s

@[simp, norm_cast] lemma int.cast_sum [add_comm_group β] [has_one β] (s : finset α) (f : α → ℤ) :
  ↑(∑ x in s, f x : ℤ) = (∑ x in s, (f x : β)) :=
(int.cast_add_hom β).map_sum f s

@[simp, norm_cast] lemma nat.cast_prod {R : Type*} [comm_semiring R] (f : α → ℕ) (s : finset α) :
  (↑∏ i in s, f i : R) = ∏ i in s, f i :=
(nat.cast_ring_hom R).map_prod _ _

@[simp, norm_cast] lemma int.cast_prod {R : Type*} [comm_ring R] (f : α → ℤ) (s : finset α) :
  (↑∏ i in s, f i : R) = ∏ i in s, f i :=
(int.cast_ring_hom R).map_prod _ _

@[simp, norm_cast] lemma units.coe_prod {M : Type*} [comm_monoid M] (f : α → Mˣ)
  (s : finset α) : (↑∏ i in s, f i : M) = ∏ i in s, f i :=
(units.coe_hom M).map_prod _ _

lemma nat_abs_sum_le {ι : Type*} (s : finset ι) (f : ι → ℤ) :
  (∑ i in s, f i).nat_abs ≤ ∑ i in s, (f i).nat_abs :=
begin
  classical,
  apply finset.induction_on s,
  { simp only [finset.sum_empty, int.nat_abs_zero] },
  { intros i s his IH,
    simp only [his, finset.sum_insert, not_false_iff],
    exact (int.nat_abs_add_le _ _).trans (add_le_add le_rfl IH) }
end
