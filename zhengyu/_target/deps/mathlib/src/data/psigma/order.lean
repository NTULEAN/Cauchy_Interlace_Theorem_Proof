/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Minchao Wu
-/
import data.sigma.lex
import order.lexicographic

/-!
# Lexicographic order on a sigma type

This file defines the lexicographic order on `Σₗ' i, α i`. `a` is less than `b` if its summand is
strictly less than the summand of `b` or they are in the same summand and `a` is less than `b`
there.

## Notation

* `Σₗ' i, α i`: Sigma type equipped with the lexicographic order. A type synonym of `Σ' i, α i`.

## See also

Related files are:
* `data.finset.colex`: Colexicographic order on finite sets.
* `data.list.lex`: Lexicographic order on lists.
* `data.sigma.order`: Lexicographic order on `Σₗ i, α i`. Basically a twin of this file.
* `order.lexicographic`: Lexicographic order on `α × β`.

## TODO

Define the disjoint order on `Σ' i, α i`, where `x ≤ y` only if `x.fst = y.fst`.

Prove that a sigma type is a `no_max_order`, `no_min_order`, `densely_ordered` when its summands
are.
-/

variables {ι : Type*} {α : ι → Type*}

namespace psigma

notation `Σₗ'` binders `, ` r:(scoped p, _root_.lex (psigma p)) := r

/-- The lexicographical `≤` on a sigma type. -/
instance lex.has_le [has_lt ι] [Π i, has_le (α i)] : has_le (Σₗ' i, α i) :=
{ le := lex (<) (λ i, (≤)) }

/-- The lexicographical `<` on a sigma type. -/
instance lex.has_lt [has_lt ι] [Π i, has_lt (α i)] : has_lt (Σₗ' i, α i) :=
{ lt := lex (<) (λ i, (<)) }

instance lex.preorder [preorder ι] [Π i, preorder (α i)] : preorder (Σₗ' i, α i) :=
{ le_refl := λ ⟨i, a⟩, lex.right _ le_rfl,
  le_trans :=
  begin
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ ⟨a₃, b₃⟩ ⟨h₁l, h₁r⟩ ⟨h₂l, h₂r⟩,
    { left, apply lt_trans, repeat { assumption } },
    { left, assumption },
    { left, assumption },
    { right, apply le_trans, repeat { assumption } }
  end,
  lt_iff_le_not_le :=
  begin
    refine λ a b, ⟨λ hab, ⟨hab.mono_right (λ i a b, le_of_lt), _⟩, _⟩,
    { rintro (⟨j, i, b, a, hji⟩ | ⟨i, b, a, hba⟩);
        obtain (⟨_, _, _, _, hij⟩ | ⟨_, _, _, hab⟩) := hab,
      { exact hij.not_lt hji },
      { exact lt_irrefl _ hji },
      { exact lt_irrefl _ hij },
      { exact hab.not_le hba } },
    { rintro ⟨⟨i, j, a, b, hij⟩ |⟨i, a, b, hab⟩, hba⟩,
      { exact lex.left _ _ hij },
      { exact lex.right _ (hab.lt_of_not_le $ λ h, hba $ lex.right _ h) } }
  end,
  .. lex.has_le,
  .. lex.has_lt }

/-- Dictionary / lexicographic partial_order for dependent pairs. -/
instance lex.partial_order [partial_order ι] [Π i, partial_order (α i)] :
  partial_order (Σₗ' i, α i) :=
{ le_antisymm :=
  begin
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
      (⟨_, _, _, _, hlt₁⟩ | ⟨_, _, _, hlt₁⟩) (⟨_, _, _, _, hlt₂⟩ | ⟨_, _, _, hlt₂⟩),
    { exact (lt_irrefl a₁ $ hlt₁.trans hlt₂).elim },
    { exact (lt_irrefl a₁ hlt₁).elim },
    { exact (lt_irrefl a₁ hlt₂).elim },
    { rw hlt₁.antisymm hlt₂ }
  end
  .. lex.preorder }

/-- Dictionary / lexicographic linear_order for pairs. -/
instance lex.linear_order [linear_order ι] [Π i, linear_order (α i)] : linear_order (Σₗ' i, α i) :=
{ le_total :=
  begin
  rintro ⟨i, a⟩ ⟨j, b⟩,
  obtain hij | rfl | hji := lt_trichotomy i j,
  { exact or.inl (lex.left _ _ hij) },
  { obtain hab | hba := le_total a b,
    { exact or.inl (lex.right _ hab) },
    { exact or.inr (lex.right _ hba) } },
  { exact or.inr (lex.left _ _ hji) }
  end,
  decidable_eq := psigma.decidable_eq,
  decidable_le := lex.decidable _ _,
  decidable_lt := lex.decidable _ _,
  .. lex.partial_order }

end psigma
