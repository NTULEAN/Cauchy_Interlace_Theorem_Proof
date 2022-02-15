/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
import group_theory.finiteness
import data.multiset.finset_ops
import algebra.algebra.tower
import order.order_iso_nat
import ring_theory.ideal.operations
import order.compactly_generated
import linear_algebra.linear_independent

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `submodule.fg N : Prop` is the assertion that `N` is finitely generated as an `R`-module.

* `is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` is Nakayama's lemma, in the following form:
  if N is a finitely generated submodule of an ambient R-module M and I is an ideal of R
  such that N ⊆ IN, then there exists r ∈ 1 + I such that rN = 0.

* `is_noetherian_iff_well_founded` is the theorem that an R-module M is Noetherian iff
  `>` is well-founded on `submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `ring_theory.polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

open set
open_locale big_operators pointwise

namespace submodule
variables {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [module R M]

/-- A submodule of `M` is finitely generated if it is the span of a finite subset of `M`. -/
def fg (N : submodule R M) : Prop := ∃ S : finset M, submodule.span R ↑S = N

theorem fg_def {N : submodule R M} :
  N.fg ↔ ∃ S : set M, finite S ∧ span R S = N :=
⟨λ ⟨t, h⟩, ⟨_, finset.finite_to_set t, h⟩, begin
  rintro ⟨t', h, rfl⟩,
  rcases finite.exists_finset_coe h with ⟨t, rfl⟩,
  exact ⟨t, rfl⟩
end⟩

lemma fg_iff_add_submonoid_fg (P : submodule ℕ M) :
  P.fg ↔ P.to_add_submonoid.fg :=
⟨λ ⟨S, hS⟩, ⟨S, by simpa [← span_nat_eq_add_submonoid_closure] using hS⟩,
  λ ⟨S, hS⟩, ⟨S, by simpa [← span_nat_eq_add_submonoid_closure] using hS⟩⟩

lemma fg_iff_add_subgroup_fg {G : Type*} [add_comm_group G] (P : submodule ℤ G) :
  P.fg ↔ P.to_add_subgroup.fg :=
⟨λ ⟨S, hS⟩, ⟨S, by simpa [← span_int_eq_add_subgroup_closure] using hS⟩,
  λ ⟨S, hS⟩, ⟨S, by simpa [← span_int_eq_add_subgroup_closure] using hS⟩⟩

lemma fg_iff_exists_fin_generating_family {N : submodule R M} :
  N.fg ↔ ∃ (n : ℕ) (s : fin n → M), span R (range s) = N :=
begin
  rw fg_def,
  split,
  { rintros ⟨S, Sfin, hS⟩,
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding,
    exact ⟨n, f, hS⟩, },
  { rintros ⟨n, s, hs⟩,
    refine ⟨range s, finite_range s, hs⟩ },
end

/-- **Nakayama's Lemma**. Atiyah-Macdonald 2.5, Eisenbud 4.7, Matsumura 2.2,
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV) -/
theorem exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [comm_ring R]
  {M : Type*} [add_comm_group M] [module R M]
  (I : ideal R) (N : submodule R M) (hn : N.fg) (hin : N ≤ I • N) :
  ∃ r : R, r - 1 ∈ I ∧ ∀ n ∈ N, r • n = (0 : M) :=
begin
  rw fg_def at hn, rcases hn with ⟨s, hfs, hs⟩,
  have : ∃ r : R, r - 1 ∈ I ∧ N ≤ (I • span R s).comap (linear_map.lsmul R M r) ∧ s ⊆ N,
  { refine ⟨1, _, _, _⟩,
    { rw sub_self, exact I.zero_mem },
    { rw [hs], intros n hn, rw [mem_comap], change (1:R) • n ∈ I • N, rw one_smul, exact hin hn },
    { rw [← span_le, hs], exact le_refl N } },
  clear hin hs, revert this,
  refine set.finite.dinduction_on hfs (λ H, _) (λ i s his hfs ih H, _),
  { rcases H with ⟨r, hr1, hrn, hs⟩, refine ⟨r, hr1, λ n hn, _⟩, specialize hrn hn,
    rwa [mem_comap, span_empty, smul_bot, mem_bot] at hrn },
  apply ih, rcases H with ⟨r, hr1, hrn, hs⟩,
  rw [← set.singleton_union, span_union, smul_sup] at hrn,
  rw [set.insert_subset] at hs,
  have : ∃ c : R, c - 1 ∈ I ∧ c • i ∈ I • span R s,
  { specialize hrn hs.1, rw [mem_comap, mem_sup] at hrn,
    rcases hrn with ⟨y, hy, z, hz, hyz⟩, change y + z = r • i at hyz,
    rw mem_smul_span_singleton at hy, rcases hy with ⟨c, hci, rfl⟩,
    use r-c, split,
    { rw [sub_right_comm], exact I.sub_mem hr1 hci },
    { rw [sub_smul, ← hyz, add_sub_cancel'], exact hz } },
  rcases this with ⟨c, hc1, hci⟩, refine ⟨c * r, _, _, hs.2⟩,
  { rw [← ideal.quotient.eq, ring_hom.map_one] at hr1 hc1 ⊢,
    rw [ring_hom.map_mul, hc1, hr1, mul_one] },
  { intros n hn, specialize hrn hn, rw [mem_comap, mem_sup] at hrn,
    rcases hrn with ⟨y, hy, z, hz, hyz⟩, change y + z = r • n at hyz,
    rw mem_smul_span_singleton at hy, rcases hy with ⟨d, hdi, rfl⟩,
    change _ • _ ∈ I • span R s,
    rw [mul_smul, ← hyz, smul_add, smul_smul, mul_comm, mul_smul],
    exact add_mem _ (smul_mem _ _ hci) (smul_mem _ _ hz) }
end

theorem fg_bot : (⊥ : submodule R M).fg :=
⟨∅, by rw [finset.coe_empty, span_empty]⟩

lemma _root_.subalgebra.fg_bot_to_submodule {R A : Type*}
  [comm_semiring R] [semiring A] [algebra R A] :
  (⊥ : subalgebra R A).to_submodule.fg :=
⟨{1}, by simp [algebra.to_submodule_bot] ⟩

theorem fg_span {s : set M} (hs : finite s) : fg (span R s) :=
⟨hs.to_finset, by rw [hs.coe_to_finset]⟩

theorem fg_span_singleton (x : M) : fg (R ∙ x) :=
fg_span (finite_singleton x)

theorem fg_sup {N₁ N₂ : submodule R M}
  (hN₁ : N₁.fg) (hN₂ : N₂.fg) : (N₁ ⊔ N₂).fg :=
let ⟨t₁, ht₁⟩ := fg_def.1 hN₁, ⟨t₂, ht₂⟩ := fg_def.1 hN₂ in
fg_def.2 ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩

variables {P : Type*} [add_comm_monoid P] [module R P]
variables (f : M →ₗ[R] P)

theorem fg.map {N : submodule R M} (hs : N.fg) : (N.map f).fg :=
let ⟨t, ht⟩ := fg_def.1 hs in fg_def.2 ⟨f '' t, ht.1.image _, by rw [span_image, ht.2]⟩

variables {f}

lemma fg_of_fg_map_injective (f : M →ₗ[R] P) (hf : function.injective f) {N : submodule R M}
  (hfn : (N.map f).fg) : N.fg :=
let ⟨t, ht⟩ := hfn in ⟨t.preimage f $ λ x _ y _ h, hf h,
submodule.map_injective_of_injective hf $ by { rw [f.map_span, finset.coe_preimage,
    set.image_preimage_eq_inter_range, set.inter_eq_self_of_subset_left, ht],
  rw [← linear_map.range_coe, ← span_le, ht, ← map_top], exact map_mono le_top }⟩

lemma fg_of_fg_map {R M P : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group P] [module R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) {N : submodule R M}
  (hfn : (N.map f).fg) : N.fg :=
fg_of_fg_map_injective f (linear_map.ker_eq_bot.1 hf) hfn

lemma fg_top (N : submodule R M) : (⊤ : submodule R N).fg ↔ N.fg :=
⟨λ h, N.range_subtype ▸ map_top N.subtype ▸ h.map _,
λ h, fg_of_fg_map_injective N.subtype subtype.val_injective $ by rwa [map_top, range_subtype]⟩

lemma fg_of_linear_equiv (e : M ≃ₗ[R] P) (h : (⊤ : submodule R P).fg) :
  (⊤ : submodule R M).fg :=
e.symm.range ▸ map_top (e.symm : P →ₗ[R] M) ▸ h.map _

theorem fg_prod {sb : submodule R M} {sc : submodule R P}
  (hsb : sb.fg) (hsc : sc.fg) : (sb.prod sc).fg :=
let ⟨tb, htb⟩ := fg_def.1 hsb, ⟨tc, htc⟩ := fg_def.1 hsc in
fg_def.2 ⟨linear_map.inl R M P '' tb ∪ linear_map.inr R M P '' tc,
  (htb.1.image _).union (htc.1.image _),
  by rw [linear_map.span_inl_union_inr, htb.2, htc.2]⟩

theorem fg_pi {ι : Type*} {M : ι → Type*} [fintype ι] [Π i, add_comm_monoid (M i)]
  [Π i, module R (M i)] {p : Π i, submodule R (M i)} (hsb : ∀ i, (p i).fg) :
  (submodule.pi set.univ p).fg :=
begin
  classical,
  simp_rw fg_def at hsb ⊢,
  choose t htf hts using hsb,
  refine ⟨
    ⋃ i, (linear_map.single i : _ →ₗ[R] _) '' t i, set.finite_Union $ λ i, (htf i).image _, _⟩,
  simp_rw [span_Union, span_image, hts, submodule.supr_map_single],
end

/-- If 0 → M' → M → M'' → 0 is exact and M' and M'' are
finitely generated then so is M. -/
theorem fg_of_fg_map_of_fg_inf_ker {R M P : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group P] [module R P] (f : M →ₗ[R] P)
  {s : submodule R M} (hs1 : (s.map f).fg) (hs2 : (s ⊓ f.ker).fg) : s.fg :=
begin
  haveI := classical.dec_eq R, haveI := classical.dec_eq M, haveI := classical.dec_eq P,
  cases hs1 with t1 ht1, cases hs2 with t2 ht2,
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y,
  { intros y hy,
    have : y ∈ map f s, { rw ← ht1, exact subset_span hy },
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩,
    exact ⟨x, hx1, hx2⟩ },
  have : ∃ g : P → M, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y,
  { choose g hg1 hg2,
    existsi λ y, if H : y ∈ t1 then g y H else 0,
    intros y H, split,
    { simp only [dif_pos H], apply hg1 },
    { simp only [dif_pos H], apply hg2 } },
  cases this with g hg, clear this,
  existsi t1.image g ∪ t2,
  rw [finset.coe_union, span_union, finset.coe_image],
  apply le_antisymm,
  { refine sup_le (span_le.2 $ image_subset_iff.2 _) (span_le.2 _),
    { intros y hy, exact (hg y hy).1 },
    { intros x hx, have := subset_span hx,
      rw ht2 at this,
      exact this.1 } },
  intros x hx,
  have : f x ∈ map f s, { rw mem_map, exact ⟨x, hx, rfl⟩ },
  rw [← ht1,← set.image_id ↑t1, finsupp.mem_span_image_iff_total] at this,
  rcases this with ⟨l, hl1, hl2⟩,
  refine mem_sup.2 ⟨(finsupp.total M M R id).to_fun
    ((finsupp.lmap_domain R R g : (P →₀ R) → M →₀ R) l), _,
    x - finsupp.total M M R id ((finsupp.lmap_domain R R g : (P →₀ R) → M →₀ R) l),
    _, add_sub_cancel'_right _ _⟩,
  { rw [← set.image_id (g '' ↑t1), finsupp.mem_span_image_iff_total], refine ⟨_, _, rfl⟩,
    haveI : inhabited P := ⟨0⟩,
    rw [← finsupp.lmap_domain_supported _ _ g, mem_map],
    refine ⟨l, hl1, _⟩,
    refl, },
  rw [ht2, mem_inf], split,
  { apply s.sub_mem hx,
    rw [finsupp.total_apply, finsupp.lmap_domain_apply, finsupp.sum_map_domain_index],
    refine s.sum_mem _,
    { intros y hy, exact s.smul_mem _ (hg y (hl1 hy)).1 },
    { exact zero_smul _ }, { exact λ _ _ _, add_smul _ _ _ } },
  { rw [linear_map.mem_ker, f.map_sub, ← hl2],
    rw [finsupp.total_apply, finsupp.total_apply, finsupp.lmap_domain_apply],
    rw [finsupp.sum_map_domain_index, finsupp.sum, finsupp.sum, f.map_sum],
    rw sub_eq_zero,
    refine finset.sum_congr rfl (λ y hy, _),
    unfold id,
    rw [f.map_smul, (hg y (hl1 hy)).2],
    { exact zero_smul _ }, { exact λ _ _ _, add_smul _ _ _ } }
end

/-- An ideal of `R` is finitely generated if it is the span of a finite subset of `R`.

This is defeq to `submodule.fg`, but unfolds more nicely. -/
def _root_.ideal.fg (I : ideal R) : Prop := ∃ S : finset R, ideal.span ↑S = I

/-- The image of a finitely generated ideal is finitely generated.

This is the `ideal` version of `submodule.fg.map`. -/
lemma _root_.ideal.fg.map {R S : Type*} [semiring R] [semiring S] {I : ideal R} (h : I.fg)
  (f : R →+* S) : (I.map f).fg :=
begin
  classical,
  obtain ⟨s, hs⟩ := h,
  refine ⟨s.image f, _⟩,
  rw [finset.coe_image, ←ideal.map_span, hs],
end

/-- The kernel of the composition of two linear maps is finitely generated if both kernels are and
the first morphism is surjective. -/
lemma fg_ker_comp {R M N P : Type*} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] [add_comm_group P] [module R P] (f : M →ₗ[R] N)
  (g : N →ₗ[R] P) (hf1 : f.ker.fg) (hf2 : g.ker.fg) (hsur : function.surjective f) :
  (g.comp f).ker.fg :=
begin
  rw linear_map.ker_comp,
  apply fg_of_fg_map_of_fg_inf_ker f,
  { rwa [submodule.map_comap_eq, linear_map.range_eq_top.2 hsur, top_inf_eq] },
  { rwa [inf_of_le_right (show f.ker ≤ (comap f g.ker), from comap_mono bot_le)] }
end

lemma fg_restrict_scalars {R S M : Type*} [comm_ring R] [comm_ring S] [algebra R S]
  [add_comm_group M] [module S M] [module R M] [is_scalar_tower R S M] (N : submodule S M)
  (hfin : N.fg) (h : function.surjective (algebra_map R S)) : (submodule.restrict_scalars R N).fg :=
begin
  obtain ⟨X, rfl⟩ := hfin,
  use X,
  exact submodule.span_eq_restrict_scalars R S M X h
end

lemma _root_.ideal.fg_ker_comp {R S A : Type*} [comm_ring R] [comm_ring S] [comm_ring A]
  (f : R →+* S) (g : S →+* A) (hf : f.ker.fg) (hg : g.ker.fg) (hsur : function.surjective f) :
  (g.comp f).ker.fg :=
begin
  letI : algebra R S := ring_hom.to_algebra f,
  letI : algebra R A := ring_hom.to_algebra (g.comp f),
  letI : algebra S A := ring_hom.to_algebra g,
  letI : is_scalar_tower R S A := is_scalar_tower.of_algebra_map_eq (λ _, rfl),
  let f₁ := algebra.linear_map R S,
  let g₁ := (is_scalar_tower.to_alg_hom R S A).to_linear_map,
  exact fg_ker_comp f₁ g₁ hf (fg_restrict_scalars g.ker hg hsur) hsur
end

/-- Finitely generated submodules are precisely compact elements in the submodule lattice. -/
theorem fg_iff_compact (s : submodule R M) : s.fg ↔ complete_lattice.is_compact_element s :=
begin
  classical,
  -- Introduce shorthand for span of an element
  let sp : M → submodule R M := λ a, span R {a},
  -- Trivial rewrite lemma; a small hack since simp (only) & rw can't accomplish this smoothly.
  have supr_rw : ∀ t : finset M, (⨆ x ∈ t, sp x) = (⨆ x ∈ (↑t : set M), sp x), from λ t, by refl,
  split,
  { rintro ⟨t, rfl⟩,
    rw [span_eq_supr_of_singleton_spans, ←supr_rw, ←(finset.sup_eq_supr t sp)],
    apply complete_lattice.finset_sup_compact_of_compact,
    exact λ n _, singleton_span_is_compact_element n, },
  { intro h,
    -- s is the Sup of the spans of its elements.
    have sSup : s = Sup (sp '' ↑s),
    by rw [Sup_eq_supr, supr_image, ←span_eq_supr_of_singleton_spans, eq_comm, span_eq],
    -- by h, s is then below (and equal to) the sup of the spans of finitely many elements.
    obtain ⟨u, ⟨huspan, husup⟩⟩ := h (sp '' ↑s) (le_of_eq sSup),
    have ssup : s = u.sup id,
    { suffices : u.sup id ≤ s, from le_antisymm husup this,
      rw [sSup, finset.sup_id_eq_Sup], exact Sup_le_Sup huspan, },
    obtain ⟨t, ⟨hts, rfl⟩⟩ := finset.subset_image_iff.mp huspan,
    rw [finset.sup_finset_image, function.comp.left_id, finset.sup_eq_supr, supr_rw,
      ←span_eq_supr_of_singleton_spans, eq_comm] at ssup,
    exact ⟨t, ssup⟩, },
end

end submodule

/--
`is_noetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
class is_noetherian (R M) [semiring R] [add_comm_monoid M] [module R M] : Prop :=
(noetherian : ∀ (s : submodule R M), s.fg)

section
variables {R : Type*} {M : Type*} {P : Type*}
variables [semiring R] [add_comm_monoid M] [add_comm_monoid P]
variables [module R M] [module R P]
open is_noetherian
include R

/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
lemma is_noetherian_def : is_noetherian R M ↔ ∀ (s : submodule R M), s.fg :=
⟨λ h, h.noetherian, is_noetherian.mk⟩

theorem is_noetherian_submodule {N : submodule R M} :
  is_noetherian R N ↔ ∀ s : submodule R M, s ≤ N → s.fg :=
begin
  refine ⟨λ ⟨hn⟩, λ s hs, have s ≤ N.subtype.range, from (N.range_subtype).symm ▸ hs,
    submodule.map_comap_eq_self this ▸ (hn _).map _, λ h, ⟨λ s, _⟩⟩,
  have f := (submodule.equiv_map_of_injective N.subtype subtype.val_injective s).symm,
  have h₁ := h (s.map N.subtype) (submodule.map_subtype_le N s),
  have h₂ : (⊤ : submodule R (s.map N.subtype)).map (↑f : _ →ₗ[R] s) = ⊤ := by simp,
  have h₃ := ((submodule.fg_top _).2 h₁).map (↑f : _ →ₗ[R] s),
  exact (submodule.fg_top _).1 (h₂ ▸ h₃),
end

theorem is_noetherian_submodule_left {N : submodule R M} :
  is_noetherian R N ↔ ∀ s : submodule R M, (N ⊓ s).fg :=
is_noetherian_submodule.trans
⟨λ H s, H _ inf_le_left, λ H s hs, (inf_of_le_right hs) ▸ H _⟩

theorem is_noetherian_submodule_right {N : submodule R M} :
  is_noetherian R N ↔ ∀ s : submodule R M, (s ⊓ N).fg :=
is_noetherian_submodule.trans
⟨λ H s, H _ inf_le_right, λ H s hs, (inf_of_le_left hs) ▸ H _⟩

instance is_noetherian_submodule' [is_noetherian R M] (N : submodule R M) : is_noetherian R N :=
is_noetherian_submodule.2 $ λ _ _, is_noetherian.noetherian _

lemma is_noetherian_of_le {s t : submodule R M} [ht : is_noetherian R t]
   (h : s ≤ t) : is_noetherian R s :=
is_noetherian_submodule.mpr (λ s' hs', is_noetherian_submodule.mp ht _ (le_trans hs' h))

variable (M)
theorem is_noetherian_of_surjective (f : M →ₗ[R] P) (hf : f.range = ⊤)
  [is_noetherian R M] : is_noetherian R P :=
⟨λ s, have (s.comap f).map f = s, from submodule.map_comap_eq_self $ hf.symm ▸ le_top,
this ▸ (noetherian _).map _⟩
variable {M}

theorem is_noetherian_of_linear_equiv (f : M ≃ₗ[R] P)
  [is_noetherian R M] : is_noetherian R P :=
is_noetherian_of_surjective _ f.to_linear_map f.range

lemma is_noetherian_top_iff :
  is_noetherian R (⊤ : submodule R M) ↔ is_noetherian R M :=
begin
  unfreezingI { split; assume h },
  { exact is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl) },
  { exact is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl).symm },
end

lemma is_noetherian_of_injective [is_noetherian R P] (f : M →ₗ[R] P) (hf : function.injective f) :
  is_noetherian R M :=
is_noetherian_of_linear_equiv (linear_equiv.of_injective f hf).symm

lemma fg_of_injective [is_noetherian R P] {N : submodule R M} (f : M →ₗ[R] P)
  (hf : function.injective f) : N.fg :=
@@is_noetherian.noetherian _ _ _ (is_noetherian_of_injective f hf) N

end

section
variables {R : Type*} {M : Type*} {P : Type*}
variables [ring R] [add_comm_group M] [add_comm_group P]
variables [module R M] [module R P]
open is_noetherian
include R

lemma is_noetherian_of_ker_bot [is_noetherian R P] (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
  is_noetherian R M :=
is_noetherian_of_linear_equiv (linear_equiv.of_injective f $ linear_map.ker_eq_bot.mp hf).symm

lemma fg_of_ker_bot [is_noetherian R P] {N : submodule R M} (f : M →ₗ[R] P) (hf : f.ker = ⊥) :
  N.fg :=
@@is_noetherian.noetherian _ _ _ (is_noetherian_of_ker_bot f hf) N

instance is_noetherian_prod [is_noetherian R M]
  [is_noetherian R P] : is_noetherian R (M × P) :=
⟨λ s, submodule.fg_of_fg_map_of_fg_inf_ker (linear_map.snd R M P) (noetherian _) $
have s ⊓ linear_map.ker (linear_map.snd R M P) ≤ linear_map.range (linear_map.inl R M P),
from λ x ⟨hx1, hx2⟩, ⟨x.1, prod.ext rfl $ eq.symm $ linear_map.mem_ker.1 hx2⟩,
submodule.map_comap_eq_self this ▸ (noetherian _).map _⟩

instance is_noetherian_pi {R ι : Type*} {M : ι → Type*} [ring R]
  [Π i, add_comm_group (M i)] [Π i, module R (M i)] [fintype ι]
  [∀ i, is_noetherian R (M i)] : is_noetherian R (Π i, M i) :=
begin
  haveI := classical.dec_eq ι,
  suffices on_finset : ∀ s : finset ι, is_noetherian R (Π i : s, M i),
  { let coe_e := equiv.subtype_univ_equiv finset.mem_univ,
    letI : is_noetherian R (Π i : finset.univ, M (coe_e i)) := on_finset finset.univ,
    exact is_noetherian_of_linear_equiv (linear_equiv.Pi_congr_left R M coe_e), },
  intro s,
  induction s using finset.induction with a s has ih,
  { split, intro s, convert submodule.fg_bot, apply eq_bot_iff.2,
    intros x hx, refine (submodule.mem_bot R).2 _, ext i, cases i.2 },
  refine @is_noetherian_of_linear_equiv _ _ _ _ _ _ _ _
    _ (@is_noetherian_prod _ (M a) _ _ _ _ _ _ _ ih),
  fconstructor,
  { exact λ f i, or.by_cases (finset.mem_insert.1 i.2)
      (λ h : i.1 = a, show M i.1, from (eq.rec_on h.symm f.1))
      (λ h : i.1 ∈ s, show M i.1, from f.2 ⟨i.1, h⟩) },
  { intros f g, ext i, unfold or.by_cases, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { change _ = _ + _, simp only [dif_pos], refl },
    { change _ = _ + _, have : ¬i = a, { rintro rfl, exact has h },
      simp only [dif_neg this, dif_pos h], refl } },
  { intros c f, ext i, unfold or.by_cases, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { change _ = c • _, simp only [dif_pos], refl },
    { change _ = c • _, have : ¬i = a, { rintro rfl, exact has h },
      simp only [dif_neg this, dif_pos h], refl } },
  { exact λ f, (f ⟨a, finset.mem_insert_self _ _⟩, λ i, f ⟨i.1, finset.mem_insert_of_mem i.2⟩) },
  { intro f, apply prod.ext,
    { simp only [or.by_cases, dif_pos] },
    { ext ⟨i, his⟩,
      have : ¬i = a, { rintro rfl, exact has his },
      dsimp only [or.by_cases], change i ∈ s at his,
      rw [dif_neg this, dif_pos his] } },
  { intro f, ext ⟨i, hi⟩,
    rcases finset.mem_insert.1 hi with rfl | h,
    { simp only [or.by_cases, dif_pos], },
    { have : ¬i = a, { rintro rfl, exact has h },
      simp only [or.by_cases, dif_neg this, dif_pos h], } }
end

/-- A version of `is_noetherian_pi` for non-dependent functions. We need this instance because
sometimes Lean fails to apply the dependent version in non-dependent settings (e.g., it fails to
prove that `ι → ℝ` is finite dimensional over `ℝ`). -/
instance is_noetherian_pi' {R ι M : Type*} [ring R] [add_comm_group M] [module R M] [fintype ι]
  [is_noetherian R M] : is_noetherian R (ι → M) :=
is_noetherian_pi

end

open is_noetherian submodule function

section
universe w
variables {R M P : Type*} {N : Type w} [semiring R] [add_comm_monoid M] [module R M]
  [add_comm_monoid N] [module R N] [add_comm_monoid P] [module R P]

theorem is_noetherian_iff_well_founded :
  is_noetherian R M ↔ well_founded ((>) : submodule R M → submodule R M → Prop) :=
begin
  rw (complete_lattice.well_founded_characterisations $ submodule R M).out 0 3,
  exact ⟨λ ⟨h⟩, λ k, (fg_iff_compact k).mp (h k), λ h, ⟨λ k, (fg_iff_compact k).mpr (h k)⟩⟩,
end

variables (R M)

lemma well_founded_submodule_gt (R M) [semiring R] [add_comm_monoid M] [module R M] :
  ∀ [is_noetherian R M], well_founded ((>) : submodule R M → submodule R M → Prop) :=
is_noetherian_iff_well_founded.mp

variables {R M}

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
theorem set_has_maximal_iff_noetherian :
  (∀ a : set $ submodule R M, a.nonempty → ∃ M' ∈ a, ∀ I ∈ a, M' ≤ I → I = M') ↔
  is_noetherian R M :=
by rw [is_noetherian_iff_well_founded, well_founded.well_founded_iff_has_max']

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
theorem monotone_stabilizes_iff_noetherian :
  (∀ (f : ℕ →o submodule R M), ∃ n, ∀ m, n ≤ m → f n = f m)
    ↔ is_noetherian R M :=
by rw [is_noetherian_iff_well_founded, well_founded.monotone_chain_condition]

/-- If `∀ I > J, P I` implies `P J`, then `P` holds for all submodules. -/
lemma is_noetherian.induction [is_noetherian R M] {P : submodule R M → Prop}
  (hgt : ∀ I, (∀ J > I, P J) → P I) (I : submodule R M) : P I :=
well_founded.recursion (well_founded_submodule_gt R M) I hgt

end


section
universe w
variables {R M P : Type*} {N : Type w} [ring R] [add_comm_group M] [module R M]
  [add_comm_group N] [module R N] [add_comm_group P] [module R P]

lemma finite_of_linear_independent [nontrivial R] [is_noetherian R M]
  {s : set M} (hs : linear_independent R (coe : s → M)) : s.finite :=
begin
  refine classical.by_contradiction (λ hf, (rel_embedding.well_founded_iff_no_descending_seq.1
    (well_founded_submodule_gt R M)).elim' _),
  have f : ℕ ↪ s, from @infinite.nat_embedding s ⟨λ f, hf ⟨f⟩⟩,
  have : ∀ n, (coe ∘ f) '' {m | m ≤ n} ⊆ s,
  { rintros n x ⟨y, hy₁, hy₂⟩, subst hy₂, exact (f y).2 },
  have : ∀ a b : ℕ, a ≤ b ↔
    span R ((coe ∘ f) '' {m | m ≤ a}) ≤ span R ((coe ∘ f) '' {m | m ≤ b}),
  { assume a b,
    rw [span_le_span_iff hs (this a) (this b),
      set.image_subset_image_iff (subtype.coe_injective.comp f.injective),
      set.subset_def],
    exact ⟨λ hab x (hxa : x ≤ a), le_trans hxa hab, λ hx, hx a (le_refl a)⟩ },
  exact ⟨⟨λ n, span R ((coe ∘ f) '' {m | m ≤ n}),
      λ x y, by simp [le_antisymm_iff, (this _ _).symm] {contextual := tt}⟩,
    by dsimp [gt]; simp only [lt_iff_le_not_le, (this _ _).symm]; tauto⟩
end

/-- If the first and final modules in a short exact sequence are noetherian,
  then the middle module is also noetherian. -/
theorem is_noetherian_of_range_eq_ker
  [is_noetherian R M] [is_noetherian R P]
  (f : M →ₗ[R] N) (g : N →ₗ[R] P)
  (hf : function.injective f)
  (hg : function.surjective g)
  (h : f.range = g.ker) :
  is_noetherian R N :=
is_noetherian_iff_well_founded.2 $
well_founded_gt_exact_sequence
  (well_founded_submodule_gt R M)
  (well_founded_submodule_gt R P)
  f.range
  (submodule.map f)
  (submodule.comap f)
  (submodule.comap g)
  (submodule.map g)
  (submodule.gci_map_comap hf)
  (submodule.gi_map_comap hg)
  (by simp [submodule.map_comap_eq, inf_comm])
  (by simp [submodule.comap_map_eq, h])

/--
For any endomorphism of a Noetherian module, there is some nontrivial iterate
with disjoint kernel and range.
-/
theorem is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot
  [I : is_noetherian R M] (f : M →ₗ[R] M) : ∃ n : ℕ, n ≠ 0 ∧ (f ^ n).ker ⊓ (f ^ n).range = ⊥ :=
begin
  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I
    (f.iterate_ker.comp ⟨λ n, n+1, λ n m w, by linarith⟩),
  specialize w (2 * n + 1) (by linarith),
  dsimp at w,
  refine ⟨n+1, nat.succ_ne_zero _, _⟩,
  rw eq_bot_iff,
  rintros - ⟨h, ⟨y, rfl⟩⟩,
  rw [mem_bot, ←linear_map.mem_ker, w],
  erw linear_map.mem_ker at h ⊢,
  change ((f ^ (n + 1)) * (f ^ (n + 1))) y = 0 at h,
  rw ←pow_add at h,
  convert h using 3,
  linarith,
end

/-- Any surjective endomorphism of a Noetherian module is injective. -/
theorem is_noetherian.injective_of_surjective_endomorphism [is_noetherian R M]
  (f : M →ₗ[R] M) (s : surjective f) : injective f :=
begin
  obtain ⟨n, ne, w⟩ := is_noetherian.exists_endomorphism_iterate_ker_inf_range_eq_bot f,
  rw [linear_map.range_eq_top.mpr (linear_map.iterate_surjective s n), inf_top_eq,
    linear_map.ker_eq_bot] at w,
  exact linear_map.injective_of_iterate_injective ne w,
end

/-- Any surjective endomorphism of a Noetherian module is bijective. -/
theorem is_noetherian.bijective_of_surjective_endomorphism [is_noetherian R M]
  (f : M →ₗ[R] M) (s : surjective f) : bijective f :=
⟨is_noetherian.injective_of_surjective_endomorphism f s, s⟩

/--
A sequence `f` of submodules of a noetherian module,
with `f (n+1)` disjoint from the supremum of `f 0`, ..., `f n`,
is eventually zero.
-/
lemma is_noetherian.disjoint_partial_sups_eventually_bot [I : is_noetherian R M]
  (f : ℕ → submodule R M) (h : ∀ n, disjoint (partial_sups f n) (f (n+1))) :
  ∃ n : ℕ, ∀ m, n ≤ m → f m = ⊥ :=
begin
  -- A little off-by-one cleanup first:
  suffices t : ∃ n : ℕ, ∀ m, n ≤ m → f (m+1) = ⊥,
  { obtain ⟨n, w⟩ := t,
    use n+1,
    rintros (_|m) p,
    { cases p, },
    { apply w,
      exact nat.succ_le_succ_iff.mp p }, },

  obtain ⟨n, w⟩ := monotone_stabilizes_iff_noetherian.mpr I (partial_sups f),
  exact ⟨n, (λ m p,
    eq_bot_of_disjoint_absorbs (h m) ((eq.symm (w (m + 1) (le_add_right p))).trans (w m p)))⟩
end

/--
If `M ⊕ N` embeds into `M`, for `M` noetherian over `R`, then `N` is trivial.
-/
noncomputable def is_noetherian.equiv_punit_of_prod_injective [is_noetherian R M]
  (f : M × N →ₗ[R] M) (i : injective f) : N ≃ₗ[R] punit.{w+1} :=
begin
  apply nonempty.some,
  obtain ⟨n, w⟩ := is_noetherian.disjoint_partial_sups_eventually_bot (f.tailing i)
    (f.tailings_disjoint_tailing i),
  specialize w n (le_refl n),
  apply nonempty.intro,
  refine (f.tailing_linear_equiv i n).symm ≪≫ₗ _,
  rw w,
  exact submodule.bot_equiv_punit,
end

end

/--
A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
class is_noetherian_ring (R) [semiring R] extends is_noetherian R R : Prop

theorem is_noetherian_ring_iff {R} [semiring R] : is_noetherian_ring R ↔ is_noetherian R R :=
⟨λ h, h.1, @is_noetherian_ring.mk _ _⟩

/-- A commutative ring is Noetherian if and only if all its ideals are finitely-generated. -/
lemma is_noetherian_ring_iff_ideal_fg (R : Type*) [comm_semiring R] :
  is_noetherian_ring R ↔ ∀ I : ideal R, I.fg :=
is_noetherian_ring_iff.trans is_noetherian_def

@[priority 80] -- see Note [lower instance priority]
instance ring.is_noetherian_of_fintype (R M) [fintype M] [semiring R] [add_comm_monoid M]
  [module R M] :
  is_noetherian R M :=
by letI := classical.dec; exact
⟨assume s, ⟨to_finset s, by rw [set.coe_to_finset, submodule.span_eq]⟩⟩

theorem ring.is_noetherian_of_zero_eq_one {R} [semiring R] (h01 : (0 : R) = 1) :
  is_noetherian_ring R :=
by haveI := subsingleton_of_zero_eq_one h01;
   haveI := fintype.of_subsingleton (0:R);
   exact is_noetherian_ring_iff.2 (ring.is_noetherian_of_fintype R R)

theorem is_noetherian_of_submodule_of_noetherian (R M) [semiring R] [add_comm_monoid M] [module R M]
  (N : submodule R M) (h : is_noetherian R M) : is_noetherian R N :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  exact order_embedding.well_founded (submodule.map_subtype.order_embedding N).dual h,
end

instance submodule.quotient.is_noetherian {R} [ring R] {M} [add_comm_group M] [module R M]
  (N : submodule R M) [h : is_noetherian R M] : is_noetherian R (M ⧸ N) :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  exact order_embedding.well_founded (submodule.comap_mkq.order_embedding N).dual h,
end

/-- If `M / S / R` is a scalar tower, and `M / R` is Noetherian, then `M / S` is
also noetherian. -/
theorem is_noetherian_of_tower (R) {S M} [semiring R] [semiring S]
  [add_comm_monoid M] [has_scalar R S] [module S M] [module R M] [is_scalar_tower R S M]
  (h : is_noetherian R M) : is_noetherian S M :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  refine (submodule.restrict_scalars_embedding R S M).dual.well_founded h
end

instance ideal.quotient.is_noetherian_ring {R : Type*} [comm_ring R] [h : is_noetherian_ring R]
  (I : ideal R) : is_noetherian_ring (R ⧸ I) :=
is_noetherian_ring_iff.mpr $ is_noetherian_of_tower R $ submodule.quotient.is_noetherian _

theorem is_noetherian_of_fg_of_noetherian {R M} [ring R] [add_comm_group M] [module R M]
  (N : submodule R M) [is_noetherian_ring R] (hN : N.fg) : is_noetherian R N :=
let ⟨s, hs⟩ := hN in
begin
  haveI := classical.dec_eq M,
  haveI := classical.dec_eq R,
  letI : is_noetherian R R := by apply_instance,
  have : ∀ x ∈ s, x ∈ N, from λ x hx, hs ▸ submodule.subset_span hx,
  refine @@is_noetherian_of_surjective ((↑s : set M) → R) _ _ _ (pi.module _ _ _)
    _ _ _ is_noetherian_pi,
  { fapply linear_map.mk,
    { exact λ f, ⟨∑ i in s.attach, f i • i.1, N.sum_mem (λ c _, N.smul_mem _ $ this _ c.2)⟩ },
    { intros f g, apply subtype.eq,
      change ∑ i in s.attach, (f i + g i) • _ = _,
      simp only [add_smul, finset.sum_add_distrib], refl },
    { intros c f, apply subtype.eq,
      change ∑ i in s.attach, (c • f i) • _ = _,
      simp only [smul_eq_mul, mul_smul],
      exact finset.smul_sum.symm } },
  rw linear_map.range_eq_top,
  rintro ⟨n, hn⟩, change n ∈ N at hn,
  rw [← hs, ← set.image_id ↑s, finsupp.mem_span_image_iff_total] at hn,
  rcases hn with ⟨l, hl1, hl2⟩,
  refine ⟨λ x, l x, subtype.ext _⟩,
  change ∑ i in s.attach, l i • (i : M) = n,
  rw [@finset.sum_attach M M s _ (λ i, l i • i), ← hl2,
      finsupp.total_apply, finsupp.sum, eq_comm],
  refine finset.sum_subset hl1 (λ x _ hx, _),
  rw [finsupp.not_mem_support_iff.1 hx, zero_smul]
end

lemma is_noetherian_of_fg_of_noetherian' {R M} [ring R] [add_comm_group M] [module R M]
  [is_noetherian_ring R] (h : (⊤ : submodule R M).fg) : is_noetherian R M :=
have is_noetherian R (⊤ : submodule R M), from is_noetherian_of_fg_of_noetherian _ h,
by exactI is_noetherian_of_linear_equiv (linear_equiv.of_top (⊤ : submodule R M) rfl)

/-- In a module over a noetherian ring, the submodule generated by finitely many vectors is
noetherian. -/
theorem is_noetherian_span_of_finite (R) {M} [ring R] [add_comm_group M] [module R M]
  [is_noetherian_ring R] {A : set M} (hA : finite A) : is_noetherian R (submodule.span R A) :=
is_noetherian_of_fg_of_noetherian _ (submodule.fg_def.mpr ⟨A, hA, rfl⟩)

theorem is_noetherian_ring_of_surjective (R) [comm_ring R] (S) [comm_ring S]
  (f : R →+* S) (hf : function.surjective f)
  [H : is_noetherian_ring R] : is_noetherian_ring S :=
begin
  rw [is_noetherian_ring_iff, is_noetherian_iff_well_founded] at H ⊢,
  exact order_embedding.well_founded (ideal.order_embedding_of_surjective f hf).dual H,
end

instance is_noetherian_ring_range {R} [comm_ring R] {S} [comm_ring S] (f : R →+* S)
  [is_noetherian_ring R] : is_noetherian_ring f.range :=
is_noetherian_ring_of_surjective R f.range f.range_restrict
  f.range_restrict_surjective

theorem is_noetherian_ring_of_ring_equiv (R) [comm_ring R] {S} [comm_ring S]
  (f : R ≃+* S) [is_noetherian_ring R] : is_noetherian_ring S :=
is_noetherian_ring_of_surjective R S f.to_ring_hom f.to_equiv.surjective

namespace submodule
variables {R : Type*} {A : Type*} [comm_semiring R] [semiring A] [algebra R A]
variables (M N : submodule R A)

theorem fg_mul (hm : M.fg) (hn : N.fg) : (M * N).fg :=
let ⟨m, hfm, hm⟩ := fg_def.1 hm, ⟨n, hfn, hn⟩ := fg_def.1 hn in
fg_def.2 ⟨m * n, hfm.mul hfn, span_mul_span R m n ▸ hm ▸ hn ▸ rfl⟩

lemma fg_pow (h : M.fg) (n : ℕ) : (M ^ n).fg :=
nat.rec_on n
(⟨{1}, by simp [one_eq_span]⟩)
(λ n ih, by simpa [pow_succ] using fg_mul _ _ h ih)

end submodule
