/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import data.finsupp.order
import order.well_founded_set


/-!
# Partial well ordering on finsupps

This file contains the fact that finitely supported functions from a fintype are
partially well ordered when the codomain is a linear order that is well ordered.
It is in a separate file for now so as to not add imports to the file `order.well_founded_set`.

## Main statements

* `finsupp.is_pwo` - finitely supported functions from a fintype are partially well ordered when
  the codomain is a linear order that is well ordered

## Tags

Dickson, order, partial well order
-/


/-- A version of **Dickson's lemma** any subset of functions `σ →₀ α` is partially well
ordered, when `σ` is a `fintype` and `α` is a linear well order.
This version uses finsupps on a fintype as it is intended for use with `mv_power_series`.
-/
lemma finsupp.is_pwo {α σ : Type*} [has_zero α] [linear_order α] [is_well_order α (<)] [fintype σ]
  (S : set (σ →₀ α)) : S.is_pwo :=
begin
  rw ← finsupp.equiv_fun_on_fintype.symm.image_preimage S,
  refine set.partially_well_ordered_on.image_of_monotone_on (pi.is_pwo _) (λ a b ha hb, id),
end
