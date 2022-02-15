/-
Copyright (c) 2020 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/
import data.list.range

/-!
# Lemmas about list.*_with_index functions.

Some specification lemmas for `list.map_with_index`, `list.mmap_with_index`, `list.foldl_with_index`
and `list.foldr_with_index`.
-/

universes u v

open function

namespace list

variables {α : Type u} {β : Type v}

section map_with_index

@[simp] lemma map_with_index_nil {α β} (f : ℕ → α → β) :
  map_with_index f [] = [] := rfl

lemma map_with_index_core_eq (l : list α) (f : ℕ → α → β) (n : ℕ) :
  l.map_with_index_core f n = l.map_with_index (λ i a, f (i + n) a) :=
begin
  induction l with hd tl hl generalizing f n,
  { simpa },
  { rw [map_with_index],
    simp [map_with_index_core, hl, add_left_comm, add_assoc, add_comm] }
end

lemma map_with_index_eq_enum_map (l : list α) (f : ℕ → α → β) :
  l.map_with_index f = l.enum.map (function.uncurry f) :=
begin
  induction l with hd tl hl generalizing f,
  { simp [list.enum_eq_zip_range] },
  { rw [map_with_index, map_with_index_core, map_with_index_core_eq, hl],
    simp [enum_eq_zip_range, range_succ_eq_map, zip_with_map_left,
    map_uncurry_zip_eq_zip_with] }
end

@[simp] lemma map_with_index_cons {α β} (l : list α) (f : ℕ → α → β) (a : α) :
  map_with_index f (a :: l) = f 0 a :: map_with_index (λ i, f (i + 1)) l :=
by simp [map_with_index_eq_enum_map, enum_eq_zip_range, map_uncurry_zip_eq_zip_with,
         range_succ_eq_map, zip_with_map_left]

@[simp] lemma length_map_with_index {α β} (l : list α) (f : ℕ → α → β) :
  (l.map_with_index f).length = l.length :=
begin
  induction l with hd tl IH generalizing f,
  { simp },
  { simp [IH] }
end

@[simp] lemma nth_le_map_with_index {α β} (l : list α) (f : ℕ → α → β) (i : ℕ) (h : i < l.length)
  (h' : i < (l.map_with_index f).length := h.trans_le (l.length_map_with_index f).ge):
  (l.map_with_index f).nth_le i h' = f i (l.nth_le i h) :=
by simp [map_with_index_eq_enum_map, enum_eq_zip_range]

lemma map_with_index_eq_of_fn {α β} (l : list α) (f : ℕ → α → β) :
  l.map_with_index f = of_fn (λ (i : fin l.length), f (i : ℕ) (l.nth_le i i.is_lt)) :=
begin
  induction l with hd tl IH generalizing f,
  { simp },
  { simpa [IH] }
end

end map_with_index

section foldr_with_index

/-- Specification of `foldr_with_index_aux`. -/
def foldr_with_index_aux_spec (f : ℕ → α → β → β) (start : ℕ) (b : β)
  (as : list α) : β :=
foldr (uncurry f) b $ enum_from start as

theorem foldr_with_index_aux_spec_cons (f : ℕ → α → β → β) (start b a as) :
  foldr_with_index_aux_spec f start b (a :: as) =
  f start a (foldr_with_index_aux_spec f (start + 1) b as) :=
rfl

theorem foldr_with_index_aux_eq_foldr_with_index_aux_spec (f : ℕ → α → β → β)
  (start b as) :
  foldr_with_index_aux f start b as = foldr_with_index_aux_spec f start b as :=
begin
  induction as generalizing start,
  { refl },
  { simp only [foldr_with_index_aux, foldr_with_index_aux_spec_cons, *] }
end

theorem foldr_with_index_eq_foldr_enum (f : ℕ → α → β → β) (b : β) (as : list α) :
  foldr_with_index f b as = foldr (uncurry f) b (enum as) :=
by simp only
    [foldr_with_index, foldr_with_index_aux_spec,
     foldr_with_index_aux_eq_foldr_with_index_aux_spec, enum]

end foldr_with_index


theorem indexes_values_eq_filter_enum (p : α → Prop) [decidable_pred p]
  (as : list α) :
  indexes_values p as = filter (p ∘ prod.snd) (enum as) :=
by simp [indexes_values, foldr_with_index_eq_foldr_enum, uncurry, filter_eq_foldr]

theorem find_indexes_eq_map_indexes_values (p : α → Prop) [decidable_pred p]
  (as : list α) :
  find_indexes p as = map prod.fst (indexes_values p as) :=
by simp only
    [indexes_values_eq_filter_enum, map_filter_eq_foldr, find_indexes,
     foldr_with_index_eq_foldr_enum, uncurry]


section foldl_with_index

/-- Specification of `foldl_with_index_aux`. -/
def foldl_with_index_aux_spec (f : ℕ → α → β → α) (start : ℕ) (a : α)
  (bs : list β) : α :=
foldl (λ a (p : ℕ × β), f p.fst a p.snd) a $ enum_from start bs

theorem foldl_with_index_aux_spec_cons (f : ℕ → α → β → α) (start a b bs) :
  foldl_with_index_aux_spec f start a (b :: bs) =
  foldl_with_index_aux_spec f (start + 1) (f start a b) bs :=
rfl

theorem foldl_with_index_aux_eq_foldl_with_index_aux_spec (f : ℕ → α → β → α)
  (start a bs) :
  foldl_with_index_aux f start a bs = foldl_with_index_aux_spec f start a bs :=
begin
  induction bs generalizing start a,
  { refl },
  { simp [foldl_with_index_aux, foldl_with_index_aux_spec_cons, *] }
end

theorem foldl_with_index_eq_foldl_enum (f : ℕ → α → β → α) (a : α) (bs : list β) :
  foldl_with_index f a bs =
  foldl (λ a (p : ℕ × β), f p.fst a p.snd) a (enum bs) :=
by simp only
    [foldl_with_index, foldl_with_index_aux_spec,
     foldl_with_index_aux_eq_foldl_with_index_aux_spec, enum]

end foldl_with_index


section mfold_with_index

variables {m : Type u → Type v} [monad m]

theorem mfoldr_with_index_eq_mfoldr_enum {α β} (f : ℕ → α → β → m β) (b : β) (as : list α) :
  mfoldr_with_index f b as = mfoldr (uncurry f) b (enum as) :=
by simp only
    [mfoldr_with_index, mfoldr_eq_foldr, foldr_with_index_eq_foldr_enum, uncurry]

theorem mfoldl_with_index_eq_mfoldl_enum [is_lawful_monad m] {α β}
  (f : ℕ → β → α → m β) (b : β) (as : list α) :
  mfoldl_with_index f b as =
    mfoldl (λ b (p : ℕ × α), f p.fst b p.snd) b (enum as) :=
by rw [mfoldl_with_index, mfoldl_eq_foldl, foldl_with_index_eq_foldl_enum]

end mfold_with_index


section mmap_with_index

variables {m : Type u → Type v} [applicative m]

/-- Specification of `mmap_with_index_aux`. -/
def mmap_with_index_aux_spec {α β} (f : ℕ → α → m β) (start : ℕ) (as : list α) :
  m (list β) :=
list.traverse (uncurry f) $ enum_from start as
-- Note: `traverse` the class method would require a less universe-polymorphic
-- `m : Type u → Type u`.

theorem mmap_with_index_aux_spec_cons {α β} (f : ℕ → α → m β) (start : ℕ)
  (a : α) (as : list α) :
  mmap_with_index_aux_spec f start (a :: as) =
    list.cons <$> f start a <*> mmap_with_index_aux_spec f (start + 1) as :=
rfl

theorem mmap_with_index_aux_eq_mmap_with_index_aux_spec {α β} (f : ℕ → α → m β)
  (start : ℕ) (as : list α) :
  mmap_with_index_aux f start as = mmap_with_index_aux_spec f start as :=
begin
  induction as generalizing start,
  { refl },
  { simp [mmap_with_index_aux, mmap_with_index_aux_spec_cons, *] }
end

theorem mmap_with_index_eq_mmap_enum {α β} (f : ℕ → α → m β) (as : list α) :
  mmap_with_index f as = list.traverse (uncurry f) (enum as) :=
by simp only
    [mmap_with_index, mmap_with_index_aux_spec,
     mmap_with_index_aux_eq_mmap_with_index_aux_spec, enum ]

end mmap_with_index


section mmap_with_index'

variables {m : Type u → Type v} [applicative m] [is_lawful_applicative m]

theorem mmap_with_index'_aux_eq_mmap_with_index_aux {α} (f : ℕ → α → m punit)
  (start : ℕ) (as : list α) :
  mmap_with_index'_aux f start as =
  mmap_with_index_aux f start as *> pure punit.star :=
by induction as generalizing start;
    simp [mmap_with_index'_aux, mmap_with_index_aux, *, seq_right_eq, const, -comp_const]
      with functor_norm

theorem mmap_with_index'_eq_mmap_with_index {α} (f : ℕ → α → m punit) (as : list α) :
  mmap_with_index' f as = mmap_with_index f as *> pure punit.star :=
by apply mmap_with_index'_aux_eq_mmap_with_index_aux

end mmap_with_index'

end list
