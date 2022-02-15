/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn, Mario Carneiro
-/
import data.list.big_operators

/-!
# Join of a list of lists

This file proves basic properties of `list.join`, which concatenates a list of lists. It is defined
in [`data.list.defs`](./data/list/defs).
-/

variables {α β : Type*}

namespace list

attribute [simp] join

@[simp] lemma join_nil : [([] : list α)].join = [] := rfl

@[simp] lemma join_eq_nil : ∀ {L : list (list α)}, join L = [] ↔ ∀ l ∈ L, l = []
| []       := iff_of_true rfl (forall_mem_nil _)
| (l :: L) := by simp only [join, append_eq_nil, join_eq_nil, forall_mem_cons]

@[simp] lemma join_append (L₁ L₂ : list (list α)) : join (L₁ ++ L₂) = join L₁ ++ join L₂ :=
by induction L₁; [refl, simp only [*, join, cons_append, append_assoc]]

@[simp] lemma join_filter_empty_eq_ff [decidable_pred (λ l : list α, l.empty = ff)] :
  ∀ {L : list (list α)}, join (L.filter (λ l, l.empty = ff)) = L.join
| []              := rfl
| ([] :: L)       := by simp [@join_filter_empty_eq_ff L]
| ((a :: l) :: L) := by simp [@join_filter_empty_eq_ff L]

@[simp] lemma join_filter_ne_nil [decidable_pred (λ l : list α, l ≠ [])] {L : list (list α)} :
  join (L.filter (λ l, l ≠ [])) = L.join :=
by simp [join_filter_empty_eq_ff, ← empty_iff_eq_nil]

lemma join_join (l : list (list (list α))) : l.join.join = (l.map join).join :=
by { induction l, simp, simp [l_ih] }

@[simp] lemma length_join (L : list (list α)) : length (join L) = sum (map length L) :=
by induction L; [refl, simp only [*, join, map, sum_cons, length_append]]

@[simp] lemma length_bind (l : list α) (f : α → list β) :
  length (list.bind l f) = sum (map (length ∘ f) l) :=
by rw [list.bind, length_join, map_map]

/-- In a join, taking the first elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join of the first `i` sublists. -/
lemma take_sum_join (L : list (list α)) (i : ℕ) :
  L.join.take ((L.map length).take i).sum = (L.take i).join :=
begin
  induction L generalizing i, { simp },
  cases i, { simp },
  simp [take_append, L_ih]
end

/-- In a join, dropping all the elements up to an index which is the sum of the lengths of the
first `i` sublists, is the same as taking the join after dropping the first `i` sublists. -/
lemma drop_sum_join (L : list (list α)) (i : ℕ) :
  L.join.drop ((L.map length).take i).sum = (L.drop i).join :=
begin
  induction L generalizing i, { simp },
  cases i, { simp },
  simp [drop_append, L_ih],
end

/-- Taking only the first `i+1` elements in a list, and then dropping the first `i` ones, one is
left with a list of length `1` made of the `i`-th element of the original list. -/
lemma drop_take_succ_eq_cons_nth_le (L : list α) {i : ℕ} (hi : i < L.length) :
  (L.take (i+1)).drop i = [nth_le L i hi] :=
begin
  induction L generalizing i,
  { simp only [length] at hi, exact (nat.not_succ_le_zero i hi).elim },
  cases i, { simp },
  have : i < L_tl.length,
  { simp at hi,
    exact nat.lt_of_succ_lt_succ hi },
  simp [L_ih this],
  refl
end

/-- In a join of sublists, taking the slice between the indices `A` and `B - 1` gives back the
original sublist of index `i` if `A` is the sum of the lenghts of sublists of index `< i`, and
`B` is the sum of the lengths of sublists of index `≤ i`. -/
lemma drop_take_succ_join_eq_nth_le (L : list (list α)) {i : ℕ} (hi : i < L.length) :
  (L.join.take ((L.map length).take (i+1)).sum).drop ((L.map length).take i).sum = nth_le L i hi :=
begin
  have : (L.map length).take i = ((L.take (i+1)).map length).take i, by simp [map_take, take_take],
  simp [take_sum_join, this, drop_sum_join, drop_take_succ_eq_cons_nth_le _ hi]
end

/-- Auxiliary lemma to control elements in a join. -/
lemma sum_take_map_length_lt1 (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  ((L.map length).take i).sum + j < ((L.map length).take (i+1)).sum :=
by simp [hi, sum_take_succ, hj]

/-- Auxiliary lemma to control elements in a join. -/
lemma sum_take_map_length_lt2 (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  ((L.map length).take i).sum + j < L.join.length :=
begin
  convert lt_of_lt_of_le (sum_take_map_length_lt1 L hi hj) (monotone_sum_take _ hi),
  have : L.length = (L.map length).length, by simp,
  simp [this, -length_map]
end

/-- The `n`-th element in a join of sublists is the `j`-th element of the `i`th sublist,
where `n` can be obtained in terms of `i` and `j` by adding the lengths of all the sublists
of index `< i`, and adding `j`. -/
lemma nth_le_join (L : list (list α)) {i j : ℕ}
  (hi : i < L.length) (hj : j < (nth_le L i hi).length) :
  nth_le L.join (((L.map length).take i).sum + j) (sum_take_map_length_lt2 L hi hj) =
  nth_le (nth_le L i hi) j hj :=
by rw [nth_le_take L.join (sum_take_map_length_lt2 L hi hj) (sum_take_map_length_lt1 L hi hj),
  nth_le_drop, nth_le_of_eq (drop_take_succ_join_eq_nth_le L hi)]

/-- Two lists of sublists are equal iff their joins coincide, as well as the lengths of the
sublists. -/
theorem eq_iff_join_eq (L L' : list (list α)) :
  L = L' ↔ L.join = L'.join ∧ map length L = map length L' :=
begin
  refine ⟨λ H, by simp [H], _⟩,
  rintros ⟨join_eq, length_eq⟩,
  apply ext_le,
  { have : length (map length L) = length (map length L'), by rw length_eq,
    simpa using this },
  { assume n h₁ h₂,
    rw [← drop_take_succ_join_eq_nth_le, ← drop_take_succ_join_eq_nth_le, join_eq, length_eq] }
end

end list
