/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import topology.separation

/-!
# Idempotents in topological semigroups

This file provides a sufficient condition for a semigroup `M` to contain an idempotent (i.e. an
element `m` such that `m * m = m `), namely that `M` is a nonempty compact Hausdorff space where
right-multiplication by constants is continuous.

We also state a corresponding lemma guaranteeing that a subset of `M` contains an idempotent.
-/

/-- Any nonempty compact Hausdorff semigroup where right-multiplication is continuous contains
an idempotent, i.e. an `m` such that `m * m = m`. -/
@[to_additive "Any nonempty compact Hausdorff additive semigroup where right-addition is continuous
contains an idempotent, i.e. an `m` such that `m + m = m`"]
lemma exists_idempotent_of_compact_t2_of_continuous_mul_left {M} [nonempty M] [semigroup M]
  [topological_space M] [compact_space M] [t2_space M]
  (continuous_mul_left : ∀ r : M, continuous (* r)) : ∃ m : M, m * m = m :=
begin
/- We apply Zorn's lemma to the poset of nonempty closed subsemigroups of `M`. It will turn out that
any minimal element is `{m}` for an idempotent `m : M`. -/
  let S : set (set M) := { N : set M | is_closed N ∧ N.nonempty ∧ ∀ m m' ∈ N, m * m' ∈ N },
  suffices : ∃ N ∈ S, ∀ N' ∈ S, N' ⊆ N → N' = N,
  { rcases this with ⟨N, ⟨N_closed, ⟨m, hm⟩, N_mul⟩, N_minimal⟩,
    use m,
/- We now have an element `m : M` of a minimal subsemigroup `N`, and want to show `m + m = m`.
We first show that every element of `N` is of the form `m' + m`.-/
    have scaling_eq_self : (* m) '' N = N,
    { apply N_minimal,
      { refine ⟨(continuous_mul_left m).is_closed_map _ N_closed,
          ⟨_, ⟨m, hm, rfl⟩⟩, _⟩,
        rintros _ ⟨m'', hm'', rfl⟩ _ ⟨m', hm', rfl⟩,
        refine ⟨m'' * m * m', N_mul _ (N_mul _ hm'' _ hm) _ hm', mul_assoc _ _ _⟩, },
      { rintros _ ⟨m', hm', rfl⟩,
        exact N_mul _ hm' _ hm, }, },
/- In particular, this means that `m' * m = m` for some `m'`. We now use minimality again to show
that this holds for _all_ `m' ∈ N`. -/
    have absorbing_eq_self : N ∩ { m' | m' * m = m} = N,
    { apply N_minimal,
      { refine ⟨N_closed.inter ((t1_space.t1 m).preimage (continuous_mul_left m)), _, _⟩,
        { rw ←scaling_eq_self at hm, exact hm },
        { rintros m'' ⟨mem'', eq'' : _ = m⟩ m' ⟨mem', eq' : _ = m⟩,
          refine ⟨N_mul _ mem'' _ mem', _⟩,
          rw [set.mem_set_of_eq, mul_assoc, eq', eq''], }, },
      apply set.inter_subset_left, },
/- Thus `m * m = m` as desired. -/
    rw ←absorbing_eq_self at hm,
    exact hm.2, },
  apply zorn.zorn_superset,
  intros c hcs hc,
  refine ⟨⋂₀ c, ⟨is_closed_sInter $ λ t ht, (hcs ht).1, _, _⟩, _⟩,
  { obtain rfl | hcnemp := c.eq_empty_or_nonempty,
    { rw set.sInter_empty, apply set.univ_nonempty, },
    convert @is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ _
      (c.nonempty_coe_sort.mpr hcnemp) (coe : c → set M) _ _ _ _,
    { simp only [subtype.range_coe_subtype, set.set_of_mem_eq] } ,
    { refine directed_on_iff_directed.mp (zorn.chain.directed_on _), exact hc.symm, },
    { intro i, exact (hcs i.property).2.1, },
    { intro i, exact (hcs i.property).1.is_compact, },
    { intro i, exact (hcs i.property).1, }, },
  { intros m hm m' hm',
    rw set.mem_sInter,
    intros t ht,
    exact (hcs ht).2.2 m (set.mem_sInter.mp hm t ht) m' (set.mem_sInter.mp hm' t ht) },
  { intros s hs, exact set.sInter_subset_of_mem hs, },
end

/-- A version of `exists_idempotent_of_compact_t2_of_continuous_mul_left` where the idempotent lies
in some specified nonempty compact subsemigroup. -/
@[to_additive exists_idempotent_in_compact_add_subsemigroup "A version of
`exists_idempotent_of_compact_t2_of_continuous_add_left` where the idempotent lies in some specified
nonempty compact additive subsemigroup."]
lemma exists_idempotent_in_compact_subsemigroup {M} [semigroup M] [topological_space M] [t2_space M]
  (continuous_mul_left : ∀ r : M, continuous (* r))
  (s : set M) (snemp : s.nonempty) (s_compact : is_compact s) (s_add : ∀ x y ∈ s, x * y ∈ s) :
  ∃ m ∈ s, m * m = m :=
begin
  let M' := { m // m ∈ s },
  letI : semigroup M' :=
    { mul       := λ p q, ⟨p.1 * q.1, s_add _ p.2 _ q.2⟩,
      mul_assoc := λ p q r, subtype.eq (mul_assoc _ _ _) },
  haveI : compact_space M' := is_compact_iff_compact_space.mp s_compact,
  haveI : nonempty M' := nonempty_subtype.mpr snemp,
  have : ∀ p : M', continuous (* p) := λ p, continuous_subtype_mk _
    ((continuous_mul_left p.1).comp continuous_subtype_val),
  obtain ⟨⟨m, hm⟩, idem⟩ := exists_idempotent_of_compact_t2_of_continuous_mul_left this,
  exact ⟨m, hm, subtype.ext_iff.mp idem⟩,
end
