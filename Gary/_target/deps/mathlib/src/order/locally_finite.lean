/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.preimage

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

Many theorems about these intervals can be found in `data.finset.locally_finite`.

## Examples

Naturally occurring locally finite orders are `ℕ`, `ℤ`, `ℕ+`, `fin n`, `α × β` the product of two
locally finite orders, `α →₀ β` the finitely supported functions to a locally finite order `β`...

## Main declarations

In a `locally_finite_order`,
* `finset.Icc`: Closed-closed interval as a finset.
* `finset.Ico`: Closed-open interval as a finset.
* `finset.Ioc`: Open-closed interval as a finset.
* `finset.Ioo`: Open-open interval as a finset.
* `multiset.Icc`: Closed-closed interval as a multiset.
* `multiset.Ico`: Closed-open interval as a multiset.
* `multiset.Ioc`: Open-closed interval as a multiset.
* `multiset.Ioo`: Open-open interval as a multiset.

When it's also an `order_top`,
* `finset.Ici`: Closed-infinite interval as a finset.
* `finset.Ioi`: Open-infinite interval as a finset.
* `multiset.Ici`: Closed-infinite interval as a multiset.
* `multiset.Ioi`: Open-infinite interval as a multiset.

When it's also an `order_bot`,
* `finset.Iic`: Infinite-open interval as a finset.
* `finset.Iio`: Infinite-closed interval as a finset.
* `multiset.Iic`: Infinite-open interval as a multiset.
* `multiset.Iio`: Infinite-closed interval as a multiset.

## Instances

A `locally_finite_order` instance can be built
* for a subtype of a locally finite order. See `subtype.locally_finite_order`.
* for the product of two locally finite orders. See `prod.locally_finite_order`.
* for any fintype (but it is noncomputable). See `fintype.to_locally_finite_order`.
* from a definition of `finset.Icc` alone. See `locally_finite_order.of_Icc`.
* by pulling back `locally_finite_order β` through an order embedding `f : α →o β`. See
  `order_embedding.locally_finite_order`.

Instances for concrete types are proved in their respective files:
* `ℕ` is in `data.nat.interval`
* `ℤ` is in `data.int.interval`
* `ℕ+` is in `data.pnat.interval`
* `fin n` is in `data.fin.interval`
* `finset α` is in `data.finset.interval`
* `Σ i, α i` is in `data.sigma.interval`
Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `locally_finite_order` instance for `α ×ₗ β` where `locally_finite_order α` and
`fintype β`.

Provide the `locally_finite_order` instance for `α →₀ β` where `β` is locally finite. Provide the
`locally_finite_order` instance for `Π₀ i, β i` where all the `β i` are locally finite.

From `linear_order α`, `no_max_order α`, `locally_finite_order α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `order_bot α` or
`no_min_order α` and `nonempty α`. When `order_bot α`, we can match `a : α` to `(Iio a).card`.

We can provide `succ_order α` from `linear_order α` and `locally_finite_order α` using

```lean
lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin -- very non golfed
  have h : (finset.Ioc x ub).nonempty := ⟨ub, finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  { have := finset.min'_mem _ h,
    simp * at * },
  rintro y hxy,
  obtain hy | hy := le_total y ub,
  apply finset.min'_le,
  simp * at *,
  exact (finset.min'_le _ _ (finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩)).trans hy,
end
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `succ_order`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/

open finset function

/-- A locally finite order is an order where bounded intervals are finite. When you don't care too
much about definitional equality, you can use `locally_finite_order.of_Icc` or
`locally_finite_order.of_finite_Icc` to build a locally finite order from just `finset.Icc`. -/
class locally_finite_order (α : Type*) [preorder α] :=
(finset_Icc : α → α → finset α)
(finset_Ico : α → α → finset α)
(finset_Ioc : α → α → finset α)
(finset_Ioo : α → α → finset α)
(finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b)
(finset_mem_Ico : ∀ a b x : α, x ∈ finset_Ico a b ↔ a ≤ x ∧ x < b)
(finset_mem_Ioc : ∀ a b x : α, x ∈ finset_Ioc a b ↔ a < x ∧ x ≤ b)
(finset_mem_Ioo : ∀ a b x : α, x ∈ finset_Ioo a b ↔ a < x ∧ x < b)

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `decidable_rel (≤)` but
only `preorder`. -/
def locally_finite_order.of_Icc' (α : Type*) [preorder α] [decidable_rel ((≤) : α → α → Prop)]
  (finset_Icc : α → α → finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) :
  locally_finite_order α :=
{ finset_Icc := finset_Icc,
  finset_Ico := λ a b, (finset_Icc a b).filter (λ x, ¬b ≤ x),
  finset_Ioc := λ a b, (finset_Icc a b).filter (λ x, ¬x ≤ a),
  finset_Ioo := λ a b, (finset_Icc a b).filter (λ x, ¬x ≤ a ∧ ¬b ≤ x),
  finset_mem_Icc := mem_Icc,
  finset_mem_Ico := λ a b x, by rw [finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_not_le],
  finset_mem_Ioc := λ a b x, by rw [finset.mem_filter, mem_Icc, and.right_comm, lt_iff_le_not_le],
  finset_mem_Ioo := λ a b x, by rw [finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_not_le,
    lt_iff_le_not_le] }

/-- A constructor from a definition of `finset.Icc` alone, the other ones being derived by removing
the ends. As opposed to `locally_finite_order.of_Icc`, this one requires `partial_order` but only
`decidable_eq`. -/
def locally_finite_order.of_Icc (α : Type*) [partial_order α] [decidable_eq α]
  (finset_Icc : α → α → finset α) (mem_Icc : ∀ a b x, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b) :
  locally_finite_order α :=
{ finset_Icc := finset_Icc,
  finset_Ico := λ a b, (finset_Icc a b).filter (λ x, x ≠ b),
  finset_Ioc := λ a b, (finset_Icc a b).filter (λ x, a ≠ x),
  finset_Ioo := λ a b, (finset_Icc a b).filter (λ x, a ≠ x ∧ x ≠ b),
  finset_mem_Icc := mem_Icc,
  finset_mem_Ico := λ a b x, by rw [finset.mem_filter, mem_Icc, and_assoc, lt_iff_le_and_ne],
  finset_mem_Ioc := λ a b x, by rw [finset.mem_filter, mem_Icc, and.right_comm, lt_iff_le_and_ne],
  finset_mem_Ioo := λ a b x, by rw [finset.mem_filter, mem_Icc, and_and_and_comm, lt_iff_le_and_ne,
    lt_iff_le_and_ne] }

variables {α β : Type*}

/-! ### Intervals as finsets -/

namespace finset
section preorder
variables [preorder α] [locally_finite_order α] {a b x : α}

/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a finset.
-/
def Icc (a b : α) : finset α := locally_finite_order.finset_Icc a b

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a finset.
-/
def Ico (a b : α) : finset α := locally_finite_order.finset_Ico a b

/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a finset.
-/
def Ioc (a b : α) : finset α := locally_finite_order.finset_Ioc a b

/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a finset.
-/
def Ioo (a b : α) : finset α := locally_finite_order.finset_Ioo a b

@[simp] lemma mem_Icc : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
locally_finite_order.finset_mem_Icc a b x

@[simp] lemma mem_Ico : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
locally_finite_order.finset_mem_Ico a b x

@[simp] lemma mem_Ioc : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
locally_finite_order.finset_mem_Ioc a b x

@[simp] lemma mem_Ioo : x ∈ Ioo a b ↔ a < x ∧ x < b :=
locally_finite_order.finset_mem_Ioo a b x

@[simp, norm_cast]
lemma coe_Icc (a b : α) : (Icc a b : set α) = set.Icc a b := set.ext $ λ _, mem_Icc

@[simp, norm_cast]
lemma coe_Ico (a b : α) : (Ico a b : set α) = set.Ico a b := set.ext $ λ _, mem_Ico

@[simp, norm_cast]
lemma coe_Ioc (a b : α) : (Ioc a b : set α) = set.Ioc a b := set.ext $ λ _, mem_Ioc

@[simp, norm_cast]
lemma coe_Ioo (a b : α) : (Ioo a b : set α) = set.Ioo a b := set.ext $ λ _, mem_Ioo

end preorder

section order_top
variables [preorder α] [order_top α] [locally_finite_order α] {a x : α}

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def Ici (a : α) : finset α := Icc a ⊤

/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def Ioi (a : α) : finset α := Ioc a ⊤

lemma Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ := rfl
lemma Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ := rfl

@[simp, norm_cast] lemma coe_Ici (a : α) : (Ici a : set α) = set.Ici a :=
by rw [Ici, coe_Icc, set.Icc_top]

@[simp, norm_cast] lemma coe_Ioi (a : α) : (Ioi a : set α) = set.Ioi a :=
by rw [Ioi, coe_Ioc, set.Ioc_top]

@[simp] lemma mem_Ici : x ∈ Ici a ↔ a ≤ x := by rw [←set.mem_Ici, ←coe_Ici, mem_coe]
@[simp] lemma mem_Ioi : x ∈ Ioi a ↔ a < x := by rw [←set.mem_Ioi, ←coe_Ioi, mem_coe]

end order_top

section order_bot
variables [preorder α] [order_bot α] [locally_finite_order α] {b x : α}

/-- The finset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a finset. -/
def Iic (b : α) : finset α := Icc ⊥ b

/-- The finset of elements `x` such that `x < b`. Basically `set.Iio b` as a finset. -/
def Iio (b : α) : finset α := Ico ⊥ b

lemma Iic_eq_Icc : Iic = Icc (⊥ : α) := rfl
lemma Iio_eq_Ico : Iio = Ico (⊥ : α) := rfl

@[simp, norm_cast] lemma coe_Iic (b : α) : (Iic b : set α) = set.Iic b :=
by rw [Iic, coe_Icc, set.Icc_bot]

@[simp, norm_cast] lemma coe_Iio (b : α) : (Iio b : set α) = set.Iio b :=
by rw [Iio, coe_Ico, set.Ico_bot]

@[simp] lemma mem_Iic : x ∈ Iic b ↔ x ≤ b := by rw [←set.mem_Iic, ←coe_Iic, mem_coe]
@[simp] lemma mem_Iio : x ∈ Iio b ↔ x < b := by rw [←set.mem_Iio, ←coe_Iio, mem_coe]

end order_bot
end finset

/-! ### Intervals as multisets -/

namespace multiset
section preorder
variables [preorder α] [locally_finite_order α]

/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a
multiset. -/
def Icc (a b : α) : multiset α := (finset.Icc a b).val

/-- The multiset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a
multiset. -/
def Ico (a b : α) : multiset α := (finset.Ico a b).val

/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a
multiset. -/
def Ioc (a b : α) : multiset α := (finset.Ioc a b).val

/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a
multiset. -/
def Ioo (a b : α) : multiset α := (finset.Ioo a b).val

@[simp] lemma mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
by rw [Icc, ←finset.mem_def, finset.mem_Icc]

@[simp] lemma mem_Ico {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
by rw [Ico, ←finset.mem_def, finset.mem_Ico]

@[simp] lemma mem_Ioc {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
by rw [Ioc, ←finset.mem_def, finset.mem_Ioc]

@[simp] lemma mem_Ioo {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
by rw [Ioo, ←finset.mem_def, finset.mem_Ioo]

end preorder

section order_top
variables [preorder α] [order_top α] [locally_finite_order α]

/-- The multiset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a multiset. -/
def Ici (a : α) : multiset α := (finset.Ici a).val

/-- The multiset of elements `x` such that `a < x`. Basically `set.Ioi a` as a multiset. -/
def Ioi (a : α) : multiset α := (finset.Ioi a).val

@[simp] lemma mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x := by rw [Ici, ←finset.mem_def, finset.mem_Ici]
@[simp] lemma mem_Ioi {a x : α} : x ∈ Ioi a ↔ a < x := by rw [Ioi, ←finset.mem_def, finset.mem_Ioi]

end order_top

section order_bot
variables [preorder α] [order_bot α] [locally_finite_order α]

/-- The multiset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a multiset. -/
def Iic (b : α) : multiset α := (finset.Iic b).val

/-- The multiset of elements `x` such that `x < b`. Basically `set.Iio b` as a multiset. -/
def Iio (b : α) : multiset α := (finset.Iio b).val

@[simp] lemma mem_Iic {b x : α} : x ∈ Iic b ↔ x ≤ b := by rw [Iic, ←finset.mem_def, finset.mem_Iic]
@[simp] lemma mem_Iio {b x : α} : x ∈ Iio b ↔ x < b := by rw [Iio, ←finset.mem_def, finset.mem_Iio]

end order_bot
end multiset

/-! ### Finiteness of `set` intervals -/

namespace set
section preorder
variables [preorder α] [locally_finite_order α] (a b : α)

instance fintype_Icc : fintype (Icc a b) :=
fintype.of_finset (finset.Icc a b) (λ x, by rw [finset.mem_Icc, mem_Icc])

instance fintype_Ico : fintype (Ico a b) :=
fintype.of_finset (finset.Ico a b) (λ x, by rw [finset.mem_Ico, mem_Ico])

instance fintype_Ioc : fintype (Ioc a b) :=
fintype.of_finset (finset.Ioc a b) (λ x, by rw [finset.mem_Ioc, mem_Ioc])

instance fintype_Ioo : fintype (Ioo a b) :=
fintype.of_finset (finset.Ioo a b) (λ x, by rw [finset.mem_Ioo, mem_Ioo])

lemma finite_Icc : (Icc a b).finite := ⟨set.fintype_Icc a b⟩
lemma finite_Ico : (Ico a b).finite := ⟨set.fintype_Ico a b⟩
lemma finite_Ioc : (Ioc a b).finite := ⟨set.fintype_Ioc a b⟩
lemma finite_Ioo : (Ioo a b).finite := ⟨set.fintype_Ioo a b⟩

end preorder

section order_top
variables [preorder α] [order_top α] [locally_finite_order α] (a : α)

instance fintype_Ici : fintype (Ici a) :=
fintype.of_finset (finset.Ici a) (λ x, by rw [finset.mem_Ici, mem_Ici])

instance fintype_Ioi : fintype (Ioi a) :=
fintype.of_finset (finset.Ioi a) (λ x, by rw [finset.mem_Ioi, mem_Ioi])

lemma finite_Ici : (Ici a).finite := ⟨set.fintype_Ici a⟩
lemma finite_Ioi : (Ioi a).finite := ⟨set.fintype_Ioi a⟩

end order_top

section order_bot
variables [preorder α] [order_bot α] [locally_finite_order α] (b : α)

instance fintype_Iic : fintype (Iic b) :=
fintype.of_finset (finset.Iic b) (λ x, by rw [finset.mem_Iic, mem_Iic])

instance fintype_Iio : fintype (Iio b) :=
fintype.of_finset (finset.Iio b) (λ x, by rw [finset.mem_Iio, mem_Iio])

lemma finite_Iic : (Iic b).finite := ⟨set.fintype_Iic b⟩
lemma finite_Iio : (Iio b).finite := ⟨set.fintype_Iio b⟩

end order_bot

end set

/-! ### Instances -/

open finset

section preorder
variables [preorder α]

/-- A noncomputable constructor from the finiteness of all closed intervals. -/
noncomputable def locally_finite_order.of_finite_Icc (h : ∀ a b : α, (set.Icc a b).finite) :
  locally_finite_order α :=
@locally_finite_order.of_Icc' α _ (classical.dec_rel _)
  (λ a b, (h a b).to_finset)
  (λ a b x, by rw [set.finite.mem_to_finset, set.mem_Icc])

/-- A fintype is noncomputably a locally finite order. -/
noncomputable def fintype.to_locally_finite_order [fintype α] : locally_finite_order α :=
{ finset_Icc := λ a b, (set.finite.of_fintype (set.Icc a b)).to_finset,
  finset_Ico := λ a b, (set.finite.of_fintype (set.Ico a b)).to_finset,
  finset_Ioc := λ a b, (set.finite.of_fintype (set.Ioc a b)).to_finset,
  finset_Ioo := λ a b, (set.finite.of_fintype (set.Ioo a b)).to_finset,
  finset_mem_Icc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Icc],
  finset_mem_Ico := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ico],
  finset_mem_Ioc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ioc],
  finset_mem_Ioo := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ioo] }

instance : subsingleton (locally_finite_order α) :=
subsingleton.intro (λ h₀ h₁, begin
  cases h₀,
  cases h₁,
  have hIcc : h₀_finset_Icc = h₁_finset_Icc,
  { ext a b x, rw [h₀_finset_mem_Icc, h₁_finset_mem_Icc] },
  have hIco : h₀_finset_Ico = h₁_finset_Ico,
  { ext a b x, rw [h₀_finset_mem_Ico, h₁_finset_mem_Ico] },
  have hIoc : h₀_finset_Ioc = h₁_finset_Ioc,
  { ext a b x, rw [h₀_finset_mem_Ioc, h₁_finset_mem_Ioc] },
  have hIoo : h₀_finset_Ioo = h₁_finset_Ioo,
  { ext a b x, rw [h₀_finset_mem_Ioo, h₁_finset_mem_Ioo] },
  simp_rw [hIcc, hIco, hIoc, hIoo],
end)

variables [preorder β] [locally_finite_order β]

-- Should this be called `locally_finite_order.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `locally_finite_order` on `β` to `α`. -/
noncomputable def order_embedding.locally_finite_order (f : α ↪o β) : locally_finite_order α :=
{ finset_Icc := λ a b, (Icc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_Ico := λ a b, (Ico (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_Ioc := λ a b, (Ioc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_Ioo := λ a b, (Ioo (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_mem_Icc := λ a b x, by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le],
  finset_mem_Ico := λ a b x, by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt],
  finset_mem_Ioc := λ a b x, by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le],
  finset_mem_Ioo := λ a b x, by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt] }

open order_dual

variables [locally_finite_order α] (a b : α)

/-- Note we define `Icc (to_dual a) (to_dual b)` as `Icc α _ _ b a` (which has type `finset α` not
`finset (order_dual α)`!) instead of `(Icc b a).map to_dual.to_embedding` as this means the
following is defeq:
```
lemma this : (Icc (to_dual (to_dual a)) (to_dual (to_dual b)) : _) = (Icc a b : _) := rfl
```
-/
instance : locally_finite_order (order_dual α) :=
{ finset_Icc := λ a b, @Icc α _ _ (of_dual b) (of_dual a),
  finset_Ico := λ a b, @Ioc α _ _ (of_dual b) (of_dual a),
  finset_Ioc := λ a b, @Ico α _ _ (of_dual b) (of_dual a),
  finset_Ioo := λ a b, @Ioo α _ _ (of_dual b) (of_dual a),
  finset_mem_Icc := λ a b x, mem_Icc.trans (and_comm _ _),
  finset_mem_Ico := λ a b x, mem_Ioc.trans (and_comm _ _),
  finset_mem_Ioc := λ a b x, mem_Ico.trans (and_comm _ _),
  finset_mem_Ioo := λ a b x, mem_Ioo.trans (and_comm _ _) }

lemma Icc_to_dual : Icc (to_dual a) (to_dual b) = (Icc b a).map to_dual.to_embedding :=
begin
  refine eq.trans _ map_refl.symm,
  ext c,
  rw [mem_Icc, mem_Icc],
  exact and_comm _ _,
end

lemma Ico_to_dual : Ico (to_dual a) (to_dual b) = (Ioc b a).map to_dual.to_embedding :=
begin
  refine eq.trans _ map_refl.symm,
  ext c,
  rw [mem_Ico, mem_Ioc],
  exact and_comm _ _,
end

lemma Ioc_to_dual : Ioc (to_dual a) (to_dual b) = (Ico b a).map to_dual.to_embedding :=
begin
  refine eq.trans _ map_refl.symm,
  ext c,
  rw [mem_Ioc, mem_Ico],
  exact and_comm _ _,
end

lemma Ioo_to_dual : Ioo (to_dual a) (to_dual b) = (Ioo b a).map to_dual.to_embedding :=
begin
  refine eq.trans _ map_refl.symm,
  ext c,
  rw [mem_Ioo, mem_Ioo],
  exact and_comm _ _,
end

instance [decidable_rel ((≤) : α × β → α × β → Prop)] : locally_finite_order (α × β) :=
locally_finite_order.of_Icc' (α × β)
  (λ a b, (Icc a.fst b.fst).product (Icc a.snd b.snd))
  (λ a b x, by { rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm], refl })

end preorder

/-!
#### `with_top`, `with_bot`

Adding a `⊤` to a locally finite `order_top` keeps it locally finite.
Adding a `⊥` to a locally finite `order_bot` keeps it locally finite.
-/

namespace with_top
variables (α) [partial_order α] [order_top α] [locally_finite_order α]

local attribute [pattern] coe
local attribute [simp] option.mem_iff

instance : locally_finite_order (with_top α) :=
{ finset_Icc := λ a b, match a, b with
    |       ⊤,       ⊤ := {⊤}
    |       ⊤, (b : α) := ∅
    | (a : α),       ⊤ := insert_none (Ici a)
    | (a : α), (b : α) := (Icc a b).map embedding.coe_option
    end,
  finset_Ico := λ a b, match a, b with
    |      ⊤,      _ := ∅
    | (a : α),      ⊤ := (Ici a).map embedding.coe_option
    | (a : α), (b : α) := (Ico a b).map embedding.coe_option
    end,
  finset_Ioc := λ a b, match a, b with
    |      ⊤,      _ := ∅
    | (a : α),      ⊤ := insert_none (Ioi a)
    | (a : α), (b : α) := (Ioc a b).map embedding.coe_option
    end,
  finset_Ioo := λ a b, match a, b with
    |      ⊤,      _ := ∅
    | (a : α),      ⊤ := (Ioi a).map embedding.coe_option
    | (a : α), (b : α) := (Ioo a b).map embedding.coe_option
    end,
  finset_mem_Icc := λ a b x, match a, b, x with
    |       ⊤,       ⊤,       x := mem_singleton.trans (le_antisymm_iff.trans $ and_comm _ _)
    |       ⊤, (b : α),       x := iff_of_false (not_mem_empty _)
                                     (λ h, (h.1.trans h.2).not_lt $ coe_lt_top _)
    | (a : α),       ⊤,       ⊤ := by simp [with_top.locally_finite_order._match_1]
    | (a : α),       ⊤, (x : α) := by simp [with_top.locally_finite_order._match_1, coe_eq_coe]
    | (a : α), (b : α),       ⊤ := by simp [with_top.locally_finite_order._match_1]
    | (a : α), (b : α), (x : α) := by simp [with_top.locally_finite_order._match_1, coe_eq_coe]
    end,
  finset_mem_Ico := λ a b x, match a, b, x with
    |       ⊤,       b,       x := iff_of_false (not_mem_empty _)
                                     (λ h, not_top_lt $ h.1.trans_lt h.2)
    | (a : α),       ⊤,       ⊤ := by simp [with_top.locally_finite_order._match_2]
    | (a : α),       ⊤, (x : α) := by simp [with_top.locally_finite_order._match_2, coe_eq_coe,
                                        coe_lt_top]
    | (a : α), (b : α),       ⊤ := by simp [with_top.locally_finite_order._match_2]
    | (a : α), (b : α), (x : α) := by simp [with_top.locally_finite_order._match_2, coe_eq_coe,
                                        coe_lt_coe]
    end,
  finset_mem_Ioc := λ a b x, match a, b, x with
    |       ⊤,       b,       x := iff_of_false (not_mem_empty _)
                                     (λ h, not_top_lt $ h.1.trans_le h.2)
    | (a : α),       ⊤,       ⊤ := by simp [with_top.locally_finite_order._match_3, coe_lt_top]
    | (a : α),       ⊤, (x : α) := by simp [with_top.locally_finite_order._match_3, coe_eq_coe,
                                        coe_lt_coe]
    | (a : α), (b : α),       ⊤ := by simp [with_top.locally_finite_order._match_3]
    | (a : α), (b : α), (x : α) := by simp [with_top.locally_finite_order._match_3, coe_eq_coe,
                                        coe_lt_coe]
    end,
  finset_mem_Ioo := λ a b x, match a, b, x with
    |       ⊤,       b,       x := iff_of_false (not_mem_empty _)
                                     (λ h, not_top_lt $ h.1.trans h.2)
    | (a : α),       ⊤,       ⊤ := by simp [with_top.locally_finite_order._match_4, coe_lt_top]
    | (a : α),       ⊤, (x : α) := by simp [with_top.locally_finite_order._match_4, coe_eq_coe,
                                        coe_lt_coe, coe_lt_top]
    | (a : α), (b : α),       ⊤ := by simp [with_top.locally_finite_order._match_4]
    | (a : α), (b : α), (x : α) := by simp [with_top.locally_finite_order._match_4, coe_eq_coe,
                                        coe_lt_coe]
    end }

variables (a b : α)

lemma Icc_coe_top : Icc (a : with_top α) ⊤ = insert_none (Ici a) := rfl
lemma Icc_coe_coe : Icc (a : with_top α) b = (Icc a b).map embedding.coe_option := rfl
lemma Ico_coe_top : Ico (a : with_top α) ⊤ = (Ici a).map embedding.coe_option := rfl
lemma Ico_coe_coe : Ico (a : with_top α) b = (Ico a b).map embedding.coe_option := rfl
lemma Ioc_coe_top : Ioc (a : with_top α) ⊤ = insert_none (Ioi a) := rfl
lemma Ioc_coe_coe : Ioc (a : with_top α) b = (Ioc a b).map embedding.coe_option := rfl
lemma Ioo_coe_top : Ioo (a : with_top α) ⊤ = (Ioi a).map embedding.coe_option := rfl
lemma Ioo_coe_coe : Ioo (a : with_top α) b = (Ioo a b).map embedding.coe_option := rfl

end with_top

namespace with_bot
variables (α) [partial_order α] [order_bot α] [locally_finite_order α]

instance : locally_finite_order (with_bot α) :=
@order_dual.locally_finite_order (with_top (order_dual α)) _ _

variables (a b : α)

lemma Icc_bot_coe : Icc (⊥ : with_bot α) b = insert_none (Iic b) := rfl
lemma Icc_coe_coe : Icc (a : with_bot α) b = (Icc a b).map embedding.coe_option := rfl
lemma Ico_bot_coe : Ico (⊥ : with_bot α) b = insert_none (Iio b) := rfl
lemma Ico_coe_coe : Ico (a : with_bot α) b = (Ico a b).map embedding.coe_option := rfl
lemma Ioc_bot_coe : Ioc (⊥ : with_bot α) b = (Iic b).map embedding.coe_option := rfl
lemma Ioc_coe_coe : Ioc (a : with_bot α) b = (Ioc a b).map embedding.coe_option := rfl
lemma Ioo_bot_coe : Ioo (⊥ : with_bot α) b = (Iio b).map embedding.coe_option := rfl
lemma Ioo_coe_coe : Ioo (a : with_bot α) b = (Ioo a b).map embedding.coe_option := rfl

end with_bot

/-! #### Subtype of a locally finite order -/

variables [preorder α] [locally_finite_order α] (p : α → Prop) [decidable_pred p]

instance : locally_finite_order (subtype p) :=
{ finset_Icc := λ a b, (Icc (a : α) b).subtype p,
  finset_Ico := λ a b, (Ico (a : α) b).subtype p,
  finset_Ioc := λ a b, (Ioc (a : α) b).subtype p,
  finset_Ioo := λ a b, (Ioo (a : α) b).subtype p,
  finset_mem_Icc := λ a b x, by simp_rw [finset.mem_subtype, mem_Icc, subtype.coe_le_coe],
  finset_mem_Ico := λ a b x, by simp_rw [finset.mem_subtype, mem_Ico, subtype.coe_le_coe,
    subtype.coe_lt_coe],
  finset_mem_Ioc := λ a b x, by simp_rw [finset.mem_subtype, mem_Ioc, subtype.coe_le_coe,
    subtype.coe_lt_coe],
  finset_mem_Ioo := λ a b x, by simp_rw [finset.mem_subtype, mem_Ioo, subtype.coe_lt_coe] }

variables (a b : subtype p)

namespace finset

lemma subtype_Icc_eq : Icc a b = (Icc (a : α) b).subtype p := rfl
lemma subtype_Ico_eq : Ico a b = (Ico (a : α) b).subtype p := rfl
lemma subtype_Ioc_eq : Ioc a b = (Ioc (a : α) b).subtype p := rfl
lemma subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).subtype p := rfl

variables (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)
include hp

lemma map_subtype_embedding_Icc : (Icc a b).map (function.embedding.subtype p) = Icc (a : α) b :=
begin
  rw subtype_Icc_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Icc at hx,
  exact hp hx.1 hx.2 a.prop b.prop,
end

lemma map_subtype_embedding_Ico : (Ico a b).map (function.embedding.subtype p) = Ico (a : α) b :=
begin
  rw subtype_Ico_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Ico at hx,
  exact hp hx.1 hx.2.le a.prop b.prop,
end

lemma map_subtype_embedding_Ioc : (Ioc a b).map (function.embedding.subtype p) = Ioc (a : α) b :=
begin
  rw subtype_Ioc_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Ioc at hx,
  exact hp hx.1.le hx.2 a.prop b.prop,
end

lemma map_subtype_embedding_Ioo : (Ioo a b).map (function.embedding.subtype p) = Ioo (a : α) b :=
begin
  rw subtype_Ioo_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Ioo at hx,
  exact hp hx.1.le hx.2.le a.prop b.prop,
end

end finset
