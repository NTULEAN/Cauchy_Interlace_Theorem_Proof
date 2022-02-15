/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.fin.basic
import data.list.sort
import data.list.duplicate

/-!
# Equivalence between `fin (length l)` and elements of a list

Given a list `l`,

* if `l` has no duplicates, then `list.nodup.nth_le_equiv` is the equivalence between
  `fin (length l)` and `{x // x ∈ l}` sending `⟨i, hi⟩` to `⟨nth_le l i hi, _⟩` with the inverse
  sending `⟨x, hx⟩` to `⟨index_of x l, _⟩`;

* if `l` has no duplicates and contains every element of a type `α`, then
  `list.nodup.nth_le_equiv_of_forall_mem_list` defines an equivalence between
  `fin (length l)` and `α`;  if `α` does not have decidable equality, then
  there is a bijection `list.nodup.nth_le_bijection_of_forall_mem_list`;

* if `l` is sorted w.r.t. `(<)`, then `list.sorted.nth_le_iso` is the same bijection reinterpreted
  as an `order_iso`.

-/

namespace list

variable {α : Type*}

namespace nodup

/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
a bijection `fin l.length → α`.  See `list.nodup.nth_le_equiv_of_forall_mem_list`
for a version giving an equivalence when there is decidable equality. -/
@[simps]
def nth_le_bijection_of_forall_mem_list (l : list α) (nd : l.nodup) (h : ∀ (x : α), x ∈ l) :
  {f : fin l.length → α // function.bijective f} :=
⟨λ i, l.nth_le i i.property, λ i j h, fin.ext $ (nd.nth_le_inj_iff _ _).1 h,
 λ x, let ⟨i, hi, hl⟩ := list.mem_iff_nth_le.1 (h x) in ⟨⟨i, hi⟩, hl⟩⟩

variable [decidable_eq α]

/-- If `l` has no duplicates, then `list.nth_le` defines an equivalence between `fin (length l)` and
the set of elements of `l`. -/
@[simps]
def nth_le_equiv (l : list α) (H : nodup l) : fin (length l) ≃ {x // x ∈ l} :=
{ to_fun := λ i, ⟨nth_le l i i.2, nth_le_mem l i i.2⟩,
  inv_fun := λ x, ⟨index_of ↑x l, index_of_lt_length.2 x.2⟩,
  left_inv := λ i, by simp [H],
  right_inv := λ x, by simp }

/-- If `l` lists all the elements of `α` without duplicates, then `list.nth_le` defines
an equivalence between `fin l.length` and `α`.

See `list.nodup.nth_le_bijection_of_forall_mem_list` for a version without
decidable equality. -/
@[simps]
def nth_le_equiv_of_forall_mem_list (l : list α) (nd : l.nodup) (h : ∀ (x : α), x ∈ l) :
  fin l.length ≃ α :=
{ to_fun := λ i, l.nth_le i i.2,
  inv_fun := λ a, ⟨_, index_of_lt_length.2 (h a)⟩,
  left_inv := λ i, by simp [nd],
  right_inv := λ a, by simp }

end nodup

namespace sorted

variables [preorder α] {l : list α}

lemma nth_le_mono (h : l.sorted (≤)) :
  monotone (λ i : fin l.length, l.nth_le i i.2) :=
λ i j, h.rel_nth_le_of_le _ _

lemma nth_le_strict_mono (h : l.sorted (<)) :
  strict_mono (λ i : fin l.length, l.nth_le i i.2) :=
λ i j, h.rel_nth_le_of_lt _ _

variable [decidable_eq α]

/-- If `l` is a list sorted w.r.t. `(<)`, then `list.nth_le` defines an order isomorphism between
`fin (length l)` and the set of elements of `l`. -/
def nth_le_iso (l : list α) (H : sorted (<) l) : fin (length l) ≃o {x // x ∈ l} :=
{ to_equiv := H.nodup.nth_le_equiv l,
  map_rel_iff' := λ i j, H.nth_le_strict_mono.le_iff_le }

variables (H : sorted (<) l) {x : {x // x ∈ l}} {i : fin l.length}

@[simp] lemma coe_nth_le_iso_apply : (H.nth_le_iso l i : α) = nth_le l i i.2 := rfl
@[simp] lemma coe_nth_le_iso_symm_apply : ((H.nth_le_iso l).symm x : ℕ) = index_of ↑x l := rfl

end sorted

section sublist

/--
If there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`,
then `sublist l l'`.
-/
lemma sublist_of_order_embedding_nth_eq {l l' : list α} (f : ℕ ↪o ℕ)
  (hf : ∀ (ix : ℕ), l.nth ix = l'.nth (f ix)) :
  l <+ l' :=
begin
  induction l with hd tl IH generalizing l' f,
  { simp },
  have : some hd = _ := hf 0,
  rw [eq_comm, list.nth_eq_some] at this,
  obtain ⟨w, h⟩ := this,
  let f' : ℕ ↪o ℕ := order_embedding.of_map_le_iff (λ i, f (i + 1) - (f 0 + 1))
    (λ a b, by simp [tsub_le_tsub_iff_right, nat.succ_le_iff, nat.lt_succ_iff]),
  have : ∀ ix, tl.nth ix = (l'.drop (f 0 + 1)).nth (f' ix),
  { intro ix,
    simp [list.nth_drop, add_tsub_cancel_of_le, nat.succ_le_iff, ←hf] },
  rw [←list.take_append_drop (f 0 + 1) l', ←list.singleton_append],
  apply list.sublist.append _ (IH _ this),
  rw [list.singleton_sublist, ←h, l'.nth_le_take _ (nat.lt_succ_self _)],
  apply list.nth_le_mem
end

/--
A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `ℕ` into `ℕ` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
lemma sublist_iff_exists_order_embedding_nth_eq {l l' : list α} :
  l <+ l' ↔ ∃ (f : ℕ ↪o ℕ), ∀ (ix : ℕ), l.nth ix = l'.nth (f ix) :=
begin
  split,
  { intro H,
    induction H with xs ys y H IH xs ys x H IH,
    { simp },
    { obtain ⟨f, hf⟩ := IH,
      refine ⟨f.trans (order_embedding.of_strict_mono (+ 1) (λ _, by simp)), _⟩,
      simpa using hf },
    { obtain ⟨f, hf⟩ := IH,
      refine ⟨order_embedding.of_map_le_iff
        (λ (ix : ℕ), if ix = 0 then 0 else (f ix.pred).succ) _, _⟩,
      { rintro ⟨_|a⟩ ⟨_|b⟩;
        simp [nat.succ_le_succ_iff] },
      { rintro ⟨_|i⟩,
        { simp },
        { simpa using hf _ } } } },
  { rintro ⟨f, hf⟩,
    exact sublist_of_order_embedding_nth_eq f hf }
end

/--
A `l : list α` is `sublist l l'` for `l' : list α` iff
there is `f`, an order-preserving embedding of `fin l.length` into `fin l'.length` such that
any element of `l` found at index `ix` can be found at index `f ix` in `l'`.
-/
lemma sublist_iff_exists_fin_order_embedding_nth_le_eq {l l' : list α} :
  l <+ l' ↔ ∃ (f : fin l.length ↪o fin l'.length),
    ∀ (ix : fin l.length), l.nth_le ix ix.is_lt = l'.nth_le (f ix) (f ix).is_lt :=
begin
  rw sublist_iff_exists_order_embedding_nth_eq,
  split,
  { rintro ⟨f, hf⟩,
    have h : ∀ {i : ℕ} (h : i < l.length), f i < l'.length,
    { intros i hi,
      specialize hf i,
      rw [nth_le_nth hi, eq_comm, nth_eq_some] at hf,
      obtain ⟨h, -⟩ := hf,
      exact h },
    refine ⟨order_embedding.of_map_le_iff (λ ix, ⟨f ix, h ix.is_lt⟩) _, _⟩,
    { simp },
    { intro i,
      apply option.some_injective,
      simpa [←nth_le_nth] using hf _ } },
  { rintro ⟨f, hf⟩,
    refine ⟨order_embedding.of_strict_mono
      (λ i, if hi : i < l.length then f ⟨i, hi⟩ else i + l'.length) _, _⟩,
    { intros i j h,
      dsimp only,
      split_ifs with hi hj hj hi,
      { simpa using h },
      { rw add_comm,
        exact lt_add_of_lt_of_pos (fin.is_lt _) (i.zero_le.trans_lt h) },
      { exact absurd (h.trans hj) hi },
      { simpa using h } },
    { intro i,
      simp only [order_embedding.coe_of_strict_mono],
      split_ifs with hi,
      { rw [nth_le_nth hi, nth_le_nth, ←hf],
        simp },
      { rw [nth_len_le, nth_len_le],
        { simp },
        { simpa using hi } } } }
end

/--
An element `x : α` of `l : list α` is a duplicate iff it can be found
at two distinct indices `n m : ℕ` inside the list `l`.
-/
lemma duplicate_iff_exists_distinct_nth_le {l : list α} {x : α} :
  l.duplicate x ↔ ∃ (n : ℕ) (hn : n < l.length) (m : ℕ) (hm : m < l.length) (h : n < m),
    x = l.nth_le n hn ∧ x = l.nth_le m hm :=
begin
  classical,
  rw [duplicate_iff_two_le_count, le_count_iff_repeat_sublist,
      sublist_iff_exists_fin_order_embedding_nth_le_eq],
  split,
  { rintro ⟨f, hf⟩,
    refine ⟨f ⟨0, by simp⟩, fin.is_lt _, f ⟨1, by simp⟩, fin.is_lt _, by simp, _, _⟩,
    { simpa using hf ⟨0, by simp⟩ },
    { simpa using hf ⟨1, by simp⟩ } },
  { rintro ⟨n, hn, m, hm, hnm, h, h'⟩,
    refine ⟨order_embedding.of_strict_mono (λ i, if (i : ℕ) = 0 then ⟨n, hn⟩ else ⟨m, hm⟩) _, _⟩,
    { rintros ⟨⟨_|i⟩, hi⟩ ⟨⟨_|j⟩, hj⟩,
      { simp },
      { simp [hnm] },
      { simp },
      { simp only [nat.lt_succ_iff, nat.succ_le_succ_iff, repeat, length, nonpos_iff_eq_zero]
          at hi hj,
        simp [hi, hj] } },
    { rintros ⟨⟨_|i⟩, hi⟩,
      { simpa using h },
      { simpa using h' } } }
end

end sublist

end list
