/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.principal_ideal_domain
import order.conditionally_complete_lattice
import ring_theory.ideal.local_ring
import ring_theory.multiplicity
import ring_theory.valuation.basic
import linear_algebra.adic_completion

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `discrete_valuation_ring R` : a predicate expressing that R is a DVR

### Definitions

* `add_val R : add_valuation R enat` : the additive valuation on a DVR.

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `uniformizer` at all, because we can use `irreducible` instead.

## Tags

discrete valuation ring
-/

open_locale classical

universe u

open ideal local_ring

/-- An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which
  is not a field. -/
class discrete_valuation_ring (R : Type u) [comm_ring R] [is_domain R]
  extends is_principal_ideal_ring R, local_ring R : Prop :=
(not_a_field' : maximal_ideal R ≠ ⊥)

namespace discrete_valuation_ring

variables (R : Type u) [comm_ring R] [is_domain R] [discrete_valuation_ring R]

lemma not_a_field : maximal_ideal R ≠ ⊥ := not_a_field'

variable {R}

open principal_ideal_ring

/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of R -/
theorem irreducible_iff_uniformizer (ϖ : R) :
  irreducible ϖ ↔ maximal_ideal R = ideal.span {ϖ} :=
⟨λ hϖ, (eq_maximal_ideal (is_maximal_of_irreducible hϖ)).symm,
begin
  intro h,
  have h2 : ¬(is_unit ϖ) := show ϖ ∈ maximal_ideal R,
    from h.symm ▸ submodule.mem_span_singleton_self ϖ,
  refine ⟨h2, _⟩,
  intros a b hab,
  by_contra' h,
  obtain ⟨ha : a ∈ maximal_ideal R, hb : b ∈ maximal_ideal R⟩ := h,
  rw [h, mem_span_singleton'] at ha hb,
  rcases ha with ⟨a, rfl⟩,
  rcases hb with ⟨b, rfl⟩,
  rw (show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)), by ring) at hab,
  have h3 := eq_zero_of_mul_eq_self_right _ hab.symm,
  { apply not_a_field R,
    simp [h, h3] },
  { exact λ hh, h2 (is_unit_of_dvd_one ϖ ⟨_, hh.symm⟩) }
end⟩

lemma _root_.irreducible.maximal_ideal_eq {ϖ : R} (h : irreducible ϖ) :
  maximal_ideal R = ideal.span {ϖ} :=
(irreducible_iff_uniformizer _).mp h

variable (R)

/-- Uniformisers exist in a DVR -/
theorem exists_irreducible : ∃ ϖ : R, irreducible ϖ :=
by {simp_rw [irreducible_iff_uniformizer],
    exact (is_principal_ideal_ring.principal $ maximal_ideal R).principal}

/-- Uniformisers exist in a DVR -/
theorem exists_prime : ∃ ϖ : R, prime ϖ :=
(exists_irreducible R).imp (λ _, principal_ideal_ring.irreducible_iff_prime.1)

/-- an integral domain is a DVR iff it's a PID with a unique non-zero prime ideal -/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [comm_ring R] [is_domain R] :
  discrete_valuation_ring R ↔ is_principal_ideal_ring R ∧ ∃! P : ideal R, P ≠ ⊥ ∧ is_prime P :=
begin
  split,
  { intro RDVR,
    rcases id RDVR with ⟨RPID, Rlocal, Rnotafield⟩,
    split, assumption,
    resetI,
    use local_ring.maximal_ideal R,
    split, split,
    { assumption },
    { apply_instance } ,
    { rintro Q ⟨hQ1, hQ2⟩,
      obtain ⟨q, rfl⟩ := (is_principal_ideal_ring.principal Q).1,
      have hq : q ≠ 0,
      { rintro rfl,
        apply hQ1,
        simp },
      erw span_singleton_prime hq at hQ2,
      replace hQ2 := hQ2.irreducible,
      rw irreducible_iff_uniformizer at hQ2,
      exact hQ2.symm } },
  { rintro ⟨RPID, Punique⟩,
    haveI : local_ring R := local_of_unique_nonzero_prime R Punique,
    refine {not_a_field' := _},
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, hP3⟩,
    have hPM : P ≤ maximal_ideal R := le_maximal_ideal (hP2.1),
    intro h, rw [h, le_bot_iff] at hPM, exact hP1 hPM }
end

lemma associated_of_irreducible {a b : R} (ha : irreducible a) (hb : irreducible b) :
  associated a b :=
begin
  rw irreducible_iff_uniformizer at ha hb,
  rw [←span_singleton_eq_span_singleton, ←ha, hb],
end

end discrete_valuation_ring

namespace discrete_valuation_ring

variable (R : Type*)

/-- Alternative characterisation of discrete valuation rings. -/
def has_unit_mul_pow_irreducible_factorization [comm_ring R] : Prop :=
∃ p : R, irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ (n : ℕ), associated (p ^ n) x

namespace has_unit_mul_pow_irreducible_factorization

variables {R} [comm_ring R] (hR : has_unit_mul_pow_irreducible_factorization R)
include hR

lemma unique_irreducible ⦃p q : R⦄ (hp : irreducible p) (hq : irreducible q) :
  associated p q :=
begin
  rcases hR with ⟨ϖ, hϖ, hR⟩,
  suffices : ∀ {p : R} (hp : irreducible p), associated p ϖ,
  { apply associated.trans (this hp) (this hq).symm, },
  clear hp hq p q,
  intros p hp,
  obtain ⟨n, hn⟩ := hR hp.ne_zero,
  have : irreducible (ϖ ^ n) := hn.symm.irreducible hp,
  rcases lt_trichotomy n 1 with (H|rfl|H),
  { obtain rfl : n = 0, { clear hn this, revert H n, exact dec_trivial },
    simpa only [not_irreducible_one, pow_zero] using this, },
  { simpa only [pow_one] using hn.symm, },
  { obtain ⟨n, rfl⟩ : ∃ k, n = 1 + k + 1 := nat.exists_eq_add_of_lt H,
    rw pow_succ at this,
    rcases this.is_unit_or_is_unit rfl with H0|H0,
    { exact (hϖ.not_unit H0).elim, },
    { rw [add_comm, pow_succ] at H0,
      exact (hϖ.not_unit (is_unit_of_mul_is_unit_left H0)).elim } }
end

variables [is_domain R]

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique factorization domain.
See `discrete_valuation_ring.of_has_unit_mul_pow_irreducible_factorization`. -/
theorem to_unique_factorization_monoid : unique_factorization_monoid R :=
let p := classical.some hR in
let spec := classical.some_spec hR in
unique_factorization_monoid.of_exists_prime_factors $ λ x hx,
begin
  use multiset.repeat p (classical.some (spec.2 hx)),
  split,
  { intros q hq,
    have hpq := multiset.eq_of_mem_repeat hq,
    rw hpq,
    refine ⟨spec.1.ne_zero, spec.1.not_unit, _⟩,
    intros a b h,
    by_cases ha : a = 0,
    { rw ha, simp only [true_or, dvd_zero], },
    obtain ⟨m, u, rfl⟩ := spec.2 ha,
    rw [mul_assoc, mul_left_comm, is_unit.dvd_mul_left _ _ _ (units.is_unit _)] at h,
    rw is_unit.dvd_mul_right (units.is_unit _),
    by_cases hm : m = 0,
    { simp only [hm, one_mul, pow_zero] at h ⊢, right, exact h },
    left,
    obtain ⟨m, rfl⟩ := nat.exists_eq_succ_of_ne_zero hm,
    rw pow_succ,
    apply dvd_mul_of_dvd_left dvd_rfl _ },
  { rw [multiset.prod_repeat], exact (classical.some_spec (spec.2 hx)), }
end

omit hR

lemma of_ufd_of_unique_irreducible [unique_factorization_monoid R]
  (h₁ : ∃ p : R, irreducible p)
  (h₂ : ∀ ⦃p q : R⦄, irreducible p → irreducible q → associated p q) :
  has_unit_mul_pow_irreducible_factorization R :=
begin
  obtain ⟨p, hp⟩ := h₁,
  refine ⟨p, hp, _⟩,
  intros x hx,
  cases wf_dvd_monoid.exists_factors x hx with fx hfx,
  refine ⟨fx.card, _⟩,
  have H := hfx.2,
  rw ← associates.mk_eq_mk_iff_associated at H ⊢,
  rw [← H, ← associates.prod_mk, associates.mk_pow, ← multiset.prod_repeat],
  congr' 1,
  symmetry,
  rw multiset.eq_repeat,
  simp only [true_and, and_imp, multiset.card_map, eq_self_iff_true,
    multiset.mem_map, exists_imp_distrib],
  rintros _ q hq rfl,
  rw associates.mk_eq_mk_iff_associated,
  apply h₂ (hfx.1 _ hq) hp,
end

end has_unit_mul_pow_irreducible_factorization

lemma aux_pid_of_ufd_of_unique_irreducible
  (R : Type u) [comm_ring R] [is_domain R] [unique_factorization_monoid R]
  (h₁ : ∃ p : R, irreducible p)
  (h₂ : ∀ ⦃p q : R⦄, irreducible p → irreducible q → associated p q) :
  is_principal_ideal_ring R :=
begin
  constructor,
  intro I,
  by_cases I0 : I = ⊥, { rw I0, use 0, simp only [set.singleton_zero, submodule.span_zero], },
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ (0:R) := I.ne_bot_iff.mp I0,
  obtain ⟨p, hp, H⟩ :=
    has_unit_mul_pow_irreducible_factorization.of_ufd_of_unique_irreducible h₁ h₂,
  have ex : ∃ n : ℕ, p ^ n ∈ I,
  { obtain ⟨n, u, rfl⟩ := H hx0,
    refine ⟨n, _⟩,
    simpa only [units.mul_inv_cancel_right] using I.mul_mem_right ↑u⁻¹ hxI, },
  constructor,
  use p ^ (nat.find ex),
  show I = ideal.span _,
  apply le_antisymm,
  { intros r hr,
    by_cases hr0 : r = 0,
    { simp only [hr0, submodule.zero_mem], },
    obtain ⟨n, u, rfl⟩ := H hr0,
    simp only [mem_span_singleton, units.is_unit, is_unit.dvd_mul_right],
    apply pow_dvd_pow,
    apply nat.find_min',
    simpa only [units.mul_inv_cancel_right] using I.mul_mem_right ↑u⁻¹ hr, },
  { erw submodule.span_singleton_le_iff_mem,
    exact nat.find_spec ex, },
end

/--
A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
lemma of_ufd_of_unique_irreducible
  {R : Type u} [comm_ring R] [is_domain R] [unique_factorization_monoid R]
  (h₁ : ∃ p : R, irreducible p)
  (h₂ : ∀ ⦃p q : R⦄, irreducible p → irreducible q → associated p q) :
  discrete_valuation_ring R :=
begin
  rw iff_pid_with_one_nonzero_prime,
  haveI PID : is_principal_ideal_ring R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂,
  obtain ⟨p, hp⟩ := h₁,
  refine ⟨PID, ⟨ideal.span {p}, ⟨_, _⟩, _⟩⟩,
  { rw submodule.ne_bot_iff,
    refine ⟨p, ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩, },
  { rwa [ideal.span_singleton_prime hp.ne_zero,
        ← unique_factorization_monoid.irreducible_iff_prime], },
  { intro I,
    rw ← submodule.is_principal.span_singleton_generator I,
    rintro ⟨I0, hI⟩,
    apply span_singleton_eq_span_singleton.mpr,
    apply h₂ _ hp,
    erw [ne.def, span_singleton_eq_bot] at I0,
    rwa [unique_factorization_monoid.irreducible_iff_prime, ← ideal.span_singleton_prime I0],
    apply_instance, },
end

/--
An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
lemma of_has_unit_mul_pow_irreducible_factorization {R : Type u} [comm_ring R] [is_domain R]
  (hR : has_unit_mul_pow_irreducible_factorization R) :
  discrete_valuation_ring R :=
begin
  letI : unique_factorization_monoid R := hR.to_unique_factorization_monoid,
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible,
  unfreezingI { obtain ⟨p, hp, H⟩ := hR, exact ⟨p, hp⟩, },
end

section

variables [comm_ring R] [is_domain R] [discrete_valuation_ring R]

variable {R}

lemma associated_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : irreducible ϖ) :
  ∃ (n : ℕ), associated x (ϖ ^ n) :=
begin
  have : wf_dvd_monoid R := is_noetherian_ring.wf_dvd_monoid,
  cases wf_dvd_monoid.exists_factors x hx with fx hfx,
  unfreezingI { use fx.card },
  have H := hfx.2,
  rw ← associates.mk_eq_mk_iff_associated at H ⊢,
  rw [← H, ← associates.prod_mk, associates.mk_pow, ← multiset.prod_repeat],
  congr' 1,
  rw multiset.eq_repeat,
  simp only [true_and, and_imp, multiset.card_map, eq_self_iff_true,
             multiset.mem_map, exists_imp_distrib],
  rintros _ _ _ rfl,
  rw associates.mk_eq_mk_iff_associated,
  refine associated_of_irreducible _ _ hirr,
  apply hfx.1,
  assumption
end

lemma eq_unit_mul_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : irreducible ϖ) :
  ∃ (n : ℕ) (u : Rˣ), x = u * ϖ ^ n :=
begin
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr,
  obtain ⟨u, rfl⟩ := hn.symm,
  use [n, u],
  apply mul_comm,
end

open submodule.is_principal

lemma ideal_eq_span_pow_irreducible {s : ideal R} (hs : s ≠ ⊥) {ϖ : R} (hirr : irreducible ϖ) :
  ∃ n : ℕ, s = ideal.span {ϖ ^ n} :=
begin
  have gen_ne_zero : generator s ≠ 0,
  { rw [ne.def, ← eq_bot_iff_generator_eq_zero], assumption },
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩,
  use n,
  have : span _ = _ := span_singleton_generator s,
  rw [← this, ← hnu, span_singleton_eq_span_singleton],
  use u
end

lemma unit_mul_pow_congr_pow {p q : R} (hp : irreducible p) (hq : irreducible q)
  (u v : Rˣ) (m n : ℕ) (h : ↑u * p ^ m = v * q ^ n) :
  m = n :=
begin
  have key : associated (multiset.repeat p m).prod (multiset.repeat q n).prod,
  { rw [multiset.prod_repeat, multiset.prod_repeat, associated],
    refine ⟨u * v⁻¹, _⟩,
    simp only [units.coe_mul],
    rw [mul_left_comm, ← mul_assoc, h, mul_right_comm, units.mul_inv, one_mul], },
  have := multiset.card_eq_card_of_rel (unique_factorization_monoid.factors_unique _ _ key),
  { simpa only [multiset.card_repeat] },
  all_goals
  { intros x hx, replace hx := multiset.eq_of_mem_repeat hx,
    unfreezingI { subst hx, assumption } },
end

lemma unit_mul_pow_congr_unit {ϖ : R} (hirr : irreducible ϖ) (u v : Rˣ) (m n : ℕ)
  (h : ↑u * ϖ ^ m = v * ϖ ^ n) :
  u = v :=
begin
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h,
  rw ← sub_eq_zero at h,
  rw [← sub_mul, mul_eq_zero] at h,
  cases h,
  { rw sub_eq_zero at h, exact_mod_cast h },
  { apply (hirr.ne_zero (pow_eq_zero h)).elim, }
end

/-!
## The additive valuation on a DVR
-/

open multiplicity

/-- The `enat`-valued additive valuation on a DVR -/
noncomputable def add_val
  (R : Type u) [comm_ring R] [is_domain R] [discrete_valuation_ring R] :
  add_valuation R enat :=
add_valuation (classical.some_spec (exists_prime R))

lemma add_val_def (r : R) (u : Rˣ) {ϖ : R} (hϖ : irreducible ϖ) (n : ℕ) (hr : r = u * ϖ ^ n) :
  add_val R r = n :=
by rw [add_val, add_valuation_apply, hr,
    eq_of_associated_left (associated_of_irreducible R hϖ
      (classical.some_spec (exists_prime R)).irreducible),
    eq_of_associated_right (associated.symm ⟨u, mul_comm _ _⟩),
    multiplicity_pow_self_of_prime (principal_ideal_ring.irreducible_iff_prime.1 hϖ)]

lemma add_val_def' (u : Rˣ) {ϖ : R} (hϖ : irreducible ϖ) (n : ℕ) :
  add_val R ((u : R) * ϖ ^ n) = n :=
add_val_def _ u hϖ n rfl

@[simp] lemma add_val_zero : add_val R 0 = ⊤ :=
(add_val R).map_zero

@[simp] lemma add_val_one : add_val R 1 = 0 :=
(add_val R).map_one

@[simp] lemma add_val_uniformizer {ϖ : R} (hϖ : irreducible ϖ) : add_val R ϖ = 1 :=
by simpa only [one_mul, eq_self_iff_true, units.coe_one, pow_one, forall_true_left, nat.cast_one]
  using add_val_def ϖ 1 hϖ 1

@[simp] lemma add_val_mul {a b : R} :
  add_val R (a * b) = add_val R a + add_val R b :=
(add_val R).map_mul _ _

lemma add_val_pow (a : R) (n : ℕ) : add_val R (a ^ n) = n • add_val R a :=
(add_val R).map_pow _ _

lemma _root_.irreducible.add_val_pow {ϖ : R} (h : irreducible ϖ) (n : ℕ) :
  add_val R (ϖ ^ n) = n :=
by rw [add_val_pow, add_val_uniformizer h, nsmul_one]

lemma add_val_eq_top_iff {a : R} : add_val R a = ⊤ ↔ a = 0 :=
begin
  have hi := (classical.some_spec (exists_prime R)).irreducible,
  split,
  { contrapose,
    intro h,
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi,
    obtain ⟨u, rfl⟩ := ha.symm,
    rw [mul_comm, add_val_def' u hi n],
    exact enat.coe_ne_top _ },
  { rintro rfl,
    exact add_val_zero }
end

lemma add_val_le_iff_dvd {a b : R} : add_val R a ≤ add_val R b ↔ a ∣ b :=
begin
  have hp := classical.some_spec (exists_prime R),
  split; intro h,
  { by_cases ha0 : a = 0,
    { rw [ha0, add_val_zero, top_le_iff, add_val_eq_top_iff] at h,
      rw h,
      apply dvd_zero },
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible,
    rw [add_val, add_valuation_apply, add_valuation_apply,
      multiplicity_le_multiplicity_iff] at h,
    exact ha.dvd.trans (h n ha.symm.dvd), },
  { rw [add_val, add_valuation_apply, add_valuation_apply],
    exact multiplicity_le_multiplicity_of_dvd_right h }
end

lemma add_val_add {a b : R} :
  min (add_val R a) (add_val R b) ≤ add_val R (a + b) :=
(add_val R).map_add _ _

end

instance (R : Type*) [comm_ring R] [is_domain R] [discrete_valuation_ring R] :
  is_Hausdorff (maximal_ideal R) R :=
{ haus' := λ x hx,
  begin
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R,
    simp only [← ideal.one_eq_top, smul_eq_mul, mul_one, smodeq.zero,
      hϖ.maximal_ideal_eq, ideal.span_singleton_pow, ideal.mem_span_singleton,
      ← add_val_le_iff_dvd, hϖ.add_val_pow] at hx,
    rwa [← add_val_eq_top_iff, enat.eq_top_iff_forall_le],
  end }

end discrete_valuation_ring
