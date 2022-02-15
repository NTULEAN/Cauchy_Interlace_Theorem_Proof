/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.algebra.operations
import ring_theory.non_zero_divisors
import data.nat.choose.sum
import ring_theory.coprime.lemmas
import data.equiv.ring
import ring_theory.ideal.quotient
/-!
# More operations on modules and ideals
-/
universes u v w x

open_locale big_operators pointwise

namespace submodule

variables {R : Type u} {M : Type v}

section comm_semiring
variables [comm_semiring R] [add_comm_monoid M] [module R M]

open_locale pointwise

instance has_scalar' : has_scalar (ideal R) (submodule R M) :=
⟨λ I N, ⨆ r : I, (r : R) • N⟩

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
def annihilator (N : submodule R M) : ideal R :=
(linear_map.lsmul R N).ker

variables {I J : ideal R} {N P : submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0:M) :=
⟨λ hr n hn, congr_arg subtype.val (linear_map.ext_iff.1 (linear_map.mem_ker.1 hr) ⟨n, hn⟩),
λ h, linear_map.mem_ker.2 $ linear_map.ext $ λ n, subtype.eq $ h n.1 n.2⟩

theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • linear_map.id) ⊥ :=
mem_annihilator.trans ⟨λ H n hn, (mem_bot R).2 $ H n hn, λ H n hn, (mem_bot R).1 $ H hn⟩

lemma mem_annihilator_span (s : set M) (r : R) :
  r ∈ (submodule.span R s).annihilator ↔ ∀ n : s, r • (n : M) = 0 :=
begin
  rw submodule.mem_annihilator,
  split,
  { intros h n, exact h _ (submodule.subset_span n.prop) },
  { intros h n hn,
    apply submodule.span_induction hn,
    { intros x hx, exact h ⟨x, hx⟩ },
    { exact smul_zero _ },
    { intros x y hx hy, rw [smul_add, hx, hy, zero_add] },
    { intros a x hx, rw [smul_comm, hx, smul_zero] } }
end

lemma mem_annihilator_span_singleton (g : M) (r : R) :
  r ∈ (submodule.span R ({g} : set M)).annihilator ↔ r • g = 0 :=
by simp [mem_annihilator_span]

theorem annihilator_bot : (⊥ : submodule R M).annihilator = ⊤ :=
(ideal.eq_top_iff_one _).2 $ mem_annihilator'.2 bot_le

theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ :=
⟨λ H, eq_bot_iff.2 $ λ (n:M) hn, (mem_bot R).2 $
  one_smul R n ▸ mem_annihilator.1 ((ideal.eq_top_iff_one _).1 H) n hn,
  λ H, H.symm ▸ annihilator_bot⟩

theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator :=
λ r hrp, mem_annihilator.2 $ λ n hn, mem_annihilator.1 hrp n $ h hn

theorem annihilator_supr (ι : Sort w) (f : ι → submodule R M) :
  (annihilator ⨆ i, f i) = ⨅ i, annihilator (f i) :=
le_antisymm (le_infi $ λ i, annihilator_mono $ le_supr _ _)
(λ r H, mem_annihilator'.2 $ supr_le $ λ i,
  have _ := (mem_infi _).1 H i, mem_annihilator'.1 this)

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
(le_supr _ ⟨r, hr⟩ : _ ≤ I • N) ⟨n, hn, rfl⟩

theorem smul_le {P : submodule R M} : I • N ≤ P ↔ ∀ (r ∈ I) (n ∈ N), r • n ∈ P :=
⟨λ H r hr n hn, H $ smul_mem_smul hr hn,
λ H, supr_le $ λ r, map_le_iff_le_comap.2 $ λ n hn, H r.1 r.2 n hn⟩

@[elab_as_eliminator]
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N)
  (Hb : ∀ (r ∈ I) (n ∈ N), p (r • n)) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (c:R) n, p n → p (c • n)) : p x :=
(@smul_le _ _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hb H

theorem mem_smul_span_singleton {I : ideal R} {m : M} {x : M} :
  x ∈ I • span R ({m} : set M) ↔ ∃ y ∈ I, y • m = x :=
⟨λ hx, smul_induction_on hx
  (λ r hri n hnm,
    let ⟨s, hs⟩ := mem_span_singleton.1 hnm in ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
  ⟨0, I.zero_mem, by rw [zero_smul]⟩
  (λ m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩,
    ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩)
  (λ c r ⟨y, hyi, hy⟩, ⟨c * y, I.mul_mem_left _ hyi, by rw [mul_smul, hy]⟩),
λ ⟨y, hyi, hy⟩, hy ▸ smul_mem_smul hyi (subset_span $ set.mem_singleton m)⟩

theorem smul_le_right : I • N ≤ N :=
smul_le.2 $ λ r hr n, N.smul_mem r

theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
smul_le.2 $ λ r hr n hn, smul_mem_smul (hij hr) (hnp hn)

theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
smul_mono h (le_refl N)

theorem smul_mono_right (h : N ≤ P) : I • N ≤ I • P :=
smul_mono (le_refl I) h

@[simp] theorem annihilator_smul (N : submodule R M) : annihilator N • N = ⊥ :=
eq_bot_iff.2 (smul_le.2 (λ r, mem_annihilator.1))

@[simp] theorem annihilator_mul (I : ideal R) : annihilator I * I = ⊥ :=
annihilator_smul I

@[simp] theorem mul_annihilator (I : ideal R) : I * annihilator I = ⊥ :=
by rw [mul_comm, annihilator_mul]

variables (I J N P)
@[simp] theorem smul_bot : I • (⊥ : submodule R M) = ⊥ :=
eq_bot_iff.2 $ smul_le.2 $ λ r hri s hsb,
(submodule.mem_bot R).2 $ ((submodule.mem_bot R).1 hsb).symm ▸ smul_zero r

@[simp] theorem bot_smul : (⊥ : ideal R) • N = ⊥ :=
eq_bot_iff.2 $ smul_le.2 $ λ r hrb s hsi,
(submodule.mem_bot R).2 $ ((submodule.mem_bot R).1 hrb).symm ▸ zero_smul _ s

@[simp] theorem top_smul : (⊤ : ideal R) • N = N :=
le_antisymm smul_le_right $ λ r hri, one_smul R r ▸ smul_mem_smul mem_top hri

theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
le_antisymm (smul_le.2 $ λ r hri m hmnp, let ⟨n, hn, p, hp, hnpm⟩ := mem_sup.1 hmnp in
  mem_sup.2 ⟨_, smul_mem_smul hri hn, _, smul_mem_smul hri hp, hnpm ▸ (smul_add _ _ _).symm⟩)
(sup_le (smul_mono_right le_sup_left)
  (smul_mono_right le_sup_right))

theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
le_antisymm (smul_le.2 $ λ r hrij n hn, let ⟨ri, hri, rj, hrj, hrijr⟩ := mem_sup.1 hrij in
  mem_sup.2 ⟨_, smul_mem_smul hri hn, _, smul_mem_smul hrj hn, hrijr ▸ (add_smul _ _ _).symm⟩)
(sup_le (smul_mono_left le_sup_left)
  (smul_mono_left le_sup_right))

protected theorem smul_assoc : (I • J) • N = I • (J • N) :=
le_antisymm (smul_le.2 $ λ rs hrsij t htn,
  smul_induction_on hrsij
  (λ r hr s hs,
    (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
  ((zero_smul R t).symm ▸ submodule.zero_mem _)
  (λ x y, (add_smul x y t).symm ▸ submodule.add_mem _)
  (λ r s h, (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ submodule.smul_mem _ _ h))
(smul_le.2 $ λ r hr sn hsn, suffices J • N ≤ submodule.comap (r • linear_map.id) ((I • J) • N),
  from this hsn,
smul_le.2 $ λ s hs n hn, show r • (s • n) ∈ (I • J) • N,
  from mul_smul r s n ▸ smul_mem_smul (smul_mem_smul hr hs) hn)

variables (S : set R) (T : set M)

theorem span_smul_span : (ideal.span S) • (span R T) =
  span R (⋃ (s ∈ S) (t ∈ T), {s • t}) :=
le_antisymm (smul_le.2 $ λ r hrS n hnT, span_induction hrS
  (λ r hrS, span_induction hnT
    (λ n hnT, subset_span $ set.mem_bUnion hrS $
      set.mem_bUnion hnT $ set.mem_singleton _)
    ((smul_zero r : r • 0 = (0:M)).symm ▸ submodule.zero_mem _)
    (λ x y, (smul_add r x y).symm ▸ submodule.add_mem _)
    (λ c m, by rw [smul_smul, mul_comm, mul_smul]; exact submodule.smul_mem _ _))
  ((zero_smul R n).symm ▸ submodule.zero_mem _)
  (λ r s, (add_smul r s n).symm ▸ submodule.add_mem _)
  (λ c r, by rw [smul_eq_mul, mul_smul]; exact submodule.smul_mem _ _)) $
span_le.2 $ set.Union₂_subset $ λ r hrS, set.Union₂_subset $ λ n hnT, set.singleton_subset_iff.2 $
smul_mem_smul (subset_span hrS) (subset_span hnT)

lemma union_eq_smul_set (r : R) (T : set M) :
  (⋃ (t : M) (x : t ∈ T), {r • t}) = r • T := by tidy

lemma ideal_span_singleton_smul (r : R) (N : submodule R M) :
  (ideal.span {r} : ideal R) • N = r • N :=
begin
  have : span R (⋃ (t : M) (x : t ∈ N), {r • t}) = r • N,
  { convert span_eq _, exact union_eq_smul_set r (N : set M) },
  conv_lhs { rw [← span_eq N, span_smul_span] },
  simpa
end

lemma span_smul_eq (r : R) (s : set M) :
  span R (r • s) = r • span R s :=
begin
  rw [← ideal_span_singleton_smul, span_smul_span],
  congr,
  simpa using (union_eq_smul_set r s).symm
end

lemma mem_of_span_top_of_smul_mem (M' : submodule R M)
  (s : set R) (hs : ideal.span s = ⊤) (x : M) (H : ∀ r : s, (r : R) • x ∈ M') : x ∈ M' :=
begin
  suffices : (⊤ : ideal R) • (span R ({x} : set M)) ≤ M',
  { rw top_smul at this, exact this (subset_span (set.mem_singleton x)) },
  rw [← hs, span_smul_span, span_le],
  simpa using H
end

/-- Given `s`, a generating set of `R`, to check that an `x : M` falls in a
submodule `M'` of `x`, we only need to show that `r ^ n • x ∈ M'` for some `n` for each `r : s`. -/
lemma mem_of_span_eq_top_of_smul_pow_mem (M' : submodule R M)
  (s : set R) (hs : ideal.span s = ⊤) (x : M)
  (H : ∀ r : s, ∃ (n : ℕ), (r ^ n : R) • x ∈ M') : x ∈ M' :=
begin
  obtain ⟨s', hs₁, hs₂⟩ := (ideal.span_eq_top_iff_finite _).mp hs,
  replace H : ∀ r : s', ∃ (n : ℕ), (r ^ n : R) • x ∈ M' := λ r, H ⟨_, hs₁ r.prop⟩,
  choose n₁ n₂ using H,
  let N := s'.attach.sup n₁,
  have hs' := ideal.span_pow_eq_top (s' : set R) hs₂ N,
  apply M'.mem_of_span_top_of_smul_mem _ hs',
  rintro ⟨_, r, hr, rfl⟩,
  convert M'.smul_mem (r ^ (N - n₁ ⟨r, hr⟩)) (n₂ ⟨r, hr⟩) using 1,
  simp only [subtype.coe_mk, smul_smul, ← pow_add],
  rw tsub_add_cancel_of_le (finset.le_sup (s'.mem_attach _) : n₁ ⟨r, hr⟩ ≤ N),
end

variables {M' : Type w} [add_comm_monoid M'] [module R M']

theorem map_smul'' (f : M →ₗ[R] M') : (I • N).map f = I • N.map f :=
le_antisymm (map_le_iff_le_comap.2 $ smul_le.2 $ λ r hr n hn, show f (r • n) ∈ I • N.map f,
    from (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) $
smul_le.2 $ λ r hr n hn, let ⟨p, hp, hfp⟩ := mem_map.1 hn in
hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)

end comm_semiring

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M]
variables {N N₁ N₂ P P₁ P₂ : submodule R M}

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon (N P : submodule R M) : ideal R :=
annihilator (P.map N.mkq)

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀ p ∈ P, r • p ∈ N :=
mem_annihilator.trans ⟨λ H p hp, (quotient.mk_eq_zero N).1 (H (quotient.mk p) (mem_map_of_mem hp)),
λ H m ⟨p, hp, hpm⟩, hpm ▸ (N.mkq).map_smul r p ▸ (quotient.mk_eq_zero N).2 $ H p hp⟩

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • linear_map.id) N :=
mem_colon

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ :=
λ r hrnp, mem_colon.2 $ λ p₁ hp₁, hn $ mem_colon.1 hrnp p₁ $ hp hp₁

theorem infi_colon_supr (ι₁ : Sort w) (f : ι₁ → submodule R M)
  (ι₂ : Sort x) (g : ι₂ → submodule R M) :
  (⨅ i, f i).colon (⨆ j, g j) = ⨅ i j, (f i).colon (g j) :=
le_antisymm (le_infi $ λ i, le_infi $ λ j, colon_mono (infi_le _ _) (le_supr _ _))
(λ r H, mem_colon'.2 $ supr_le $ λ j, map_le_iff_le_comap.1 $ le_infi $ λ i,
  map_le_iff_le_comap.2 $ mem_colon'.1 $ have _ := ((mem_infi _).1 H i),
  have _ := ((mem_infi _).1 this j), this)

end comm_ring

end submodule

namespace ideal

section mul_and_radical
variables {R : Type u} {ι : Type*} [comm_semiring R]
variables {I J K L : ideal R}

instance : has_mul (ideal R) := ⟨(•)⟩

@[simp] lemma add_eq_sup : I + J = I ⊔ J := rfl
@[simp] lemma zero_eq_bot : (0 : ideal R) = ⊥ := rfl
@[simp] lemma one_eq_top : (1 : ideal R) = ⊤ :=
by erw [submodule.one_eq_range, linear_map.range_id]

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
submodule.smul_mem_smul hr hs

theorem mul_mem_mul_rev {r s} (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
mul_comm r s ▸ mul_mem_mul hr hs

lemma pow_mem_pow {x : R} (hx : x ∈ I) (n : ℕ) : x ^ n ∈ I ^ n :=
begin
  induction n with n ih, { simp only [pow_zero, ideal.one_eq_top], },
  simpa only [pow_succ] using mul_mem_mul hx ih,
end

theorem mul_le : I * J ≤ K ↔ ∀ (r ∈ I) (s ∈ J), r * s ∈ K :=
submodule.smul_le

lemma mul_le_left : I * J ≤ J :=
ideal.mul_le.2 (λ r hr s, J.mul_mem_left _)

lemma mul_le_right : I * J ≤ I :=
ideal.mul_le.2 (λ r hr s hs, I.mul_mem_right _ hr)

@[simp] lemma sup_mul_right_self : I ⊔ (I * J) = I :=
sup_eq_left.2 ideal.mul_le_right

@[simp] lemma sup_mul_left_self : I ⊔ (J * I) = I :=
sup_eq_left.2 ideal.mul_le_left

@[simp] lemma mul_right_self_sup : (I * J) ⊔ I = I :=
sup_eq_right.2 ideal.mul_le_right

@[simp] lemma mul_left_self_sup : (J * I) ⊔ I = I :=
sup_eq_right.2 ideal.mul_le_left

variables (I J K)
protected theorem mul_comm : I * J = J * I :=
le_antisymm (mul_le.2 $ λ r hrI s hsJ, mul_mem_mul_rev hsJ hrI)
  (mul_le.2 $ λ r hrJ s hsI, mul_mem_mul_rev hsI hrJ)

protected theorem mul_assoc : (I * J) * K = I * (J * K) :=
submodule.smul_assoc I J K

theorem span_mul_span (S T : set R) : span S * span T =
  span ⋃ (s ∈ S) (t ∈ T), {s * t} :=
submodule.span_smul_span S T
variables {I J K}

lemma span_mul_span' (S T : set R) : span S * span T = span (S*T) :=
by { unfold span, rw submodule.span_mul_span, }

lemma span_singleton_mul_span_singleton (r s : R) :
  span {r} * span {s} = (span {r * s} : ideal R) :=
by { unfold span, rw [submodule.span_mul_span, set.singleton_mul_singleton], }

lemma span_singleton_pow (s : R) (n : ℕ):
  span {s} ^ n = (span {s ^ n} : ideal R) :=
begin
  induction n with n ih, { simp [set.singleton_one], },
  simp only [pow_succ, ih, span_singleton_mul_span_singleton],
end

lemma mem_mul_span_singleton {x y : R} {I : ideal R} :
  x ∈ I * span {y} ↔ ∃ z ∈ I, z * y = x :=
submodule.mem_smul_span_singleton

lemma mem_span_singleton_mul {x y : R} {I : ideal R} :
  x ∈ span {y} * I ↔ ∃ z ∈ I, y * z = x :=
by simp only [mul_comm, mem_mul_span_singleton]

lemma le_span_singleton_mul_iff {x : R} {I J : ideal R} :
  I ≤ span {x} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI :=
show (∀ {zI} (hzI : zI ∈ I), zI ∈ span {x} * J) ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI,
by simp only [mem_span_singleton_mul]

lemma span_singleton_mul_le_iff {x : R} {I J : ideal R} :
  span {x} * I ≤ J ↔ ∀ z ∈ I, x * z ∈ J :=
begin
  simp only [mul_le, mem_span_singleton_mul, mem_span_singleton],
  split,
  { intros h zI hzI,
    exact h x (dvd_refl x) zI hzI },
  { rintros h _ ⟨z, rfl⟩ zI hzI,
    rw [mul_comm x z, mul_assoc],
    exact J.mul_mem_left _ (h zI hzI) },
end

lemma span_singleton_mul_le_span_singleton_mul {x y : R} {I J : ideal R} :
  span {x} * I ≤ span {y} * J ↔ ∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ :=
by simp only [span_singleton_mul_le_iff, mem_span_singleton_mul, eq_comm]

lemma eq_span_singleton_mul {x : R} (I J : ideal R) :
  I = span {x} * J ↔ ((∀ zI ∈ I, ∃ zJ ∈ J, x * zJ = zI) ∧ (∀ z ∈ J, x * z ∈ I)) :=
by simp only [le_antisymm_iff, le_span_singleton_mul_iff, span_singleton_mul_le_iff]

lemma span_singleton_mul_eq_span_singleton_mul {x y : R} (I J : ideal R) :
  span {x} * I = span {y} * J ↔
    ((∀ zI ∈ I, ∃ zJ ∈ J, x * zI = y * zJ) ∧
     (∀ zJ ∈ J, ∃ zI ∈ I, x * zI = y * zJ)) :=
by simp only [le_antisymm_iff, span_singleton_mul_le_span_singleton_mul, eq_comm]

lemma prod_span {ι : Type*} (s : finset ι) (I : ι → set R) :
  (∏ i in s, ideal.span (I i)) = ideal.span (∏ i in s, I i) :=
submodule.prod_span s I

lemma prod_span_singleton {ι : Type*} (s : finset ι) (I : ι → R) :
  (∏ i in s, ideal.span ({I i} : set R)) = ideal.span {∏ i in s, I i} :=
submodule.prod_span_singleton s I

lemma finset_inf_span_singleton {ι : Type*} (s : finset ι) (I : ι → R)
  (hI : set.pairwise ↑s (is_coprime on I)) :
  (s.inf $ λ i, ideal.span ({I i} : set R)) = ideal.span {∏ i in s, I i} :=
begin
  ext x,
  simp only [submodule.mem_finset_inf, ideal.mem_span_singleton],
  exact ⟨finset.prod_dvd_of_coprime hI,
    λ h i hi, (finset.dvd_prod_of_mem _ hi).trans h⟩
end

lemma infi_span_singleton {ι : Type*} [fintype ι] (I : ι → R)
  (hI : ∀ i j (hij : i ≠ j), is_coprime (I i) (I j)):
  (⨅ i, ideal.span ({I i} : set R)) = ideal.span {∏ i, I i} :=
begin
  rw [← finset.inf_univ_eq_infi, finset_inf_span_singleton],
  rwa [finset.coe_univ, set.pairwise_univ]
end

theorem mul_le_inf : I * J ≤ I ⊓ J :=
mul_le.2 $ λ r hri s hsj, ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

theorem multiset_prod_le_inf {s : multiset (ideal R)} :
  s.prod ≤ s.inf :=
begin
  classical, refine s.induction_on _ _,
  { rw [multiset.inf_zero], exact le_top },
  intros a s ih,
  rw [multiset.prod_cons, multiset.inf_cons],
  exact le_trans mul_le_inf (inf_le_inf le_rfl ih)
end

theorem prod_le_inf {s : finset ι} {f : ι → ideal R} : s.prod f ≤ s.inf f :=
multiset_prod_le_inf

theorem mul_eq_inf_of_coprime (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
le_antisymm mul_le_inf $ λ r ⟨hri, hrj⟩,
let ⟨s, hsi, t, htj, hst⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 h) in
mul_one r ▸ hst ▸ (mul_add r s t).symm ▸ ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj)
  (mul_mem_mul hri htj)

variables (I)
@[simp] theorem mul_bot : I * ⊥ = ⊥ :=
submodule.smul_bot I

@[simp] theorem bot_mul : ⊥ * I = ⊥ :=
submodule.bot_smul I

@[simp] theorem mul_top : I * ⊤ = I :=
ideal.mul_comm ⊤ I ▸ submodule.top_smul I

@[simp] theorem top_mul : ⊤ * I = I :=
submodule.top_smul I
variables {I}

theorem mul_mono (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
submodule.smul_mono hik hjl

theorem mul_mono_left (h : I ≤ J) : I * K ≤ J * K :=
submodule.smul_mono_left h

theorem mul_mono_right (h : J ≤ K) : I * J ≤ I * K :=
submodule.smul_mono_right h

variables (I J K)
theorem mul_sup : I * (J ⊔ K) = I * J ⊔ I * K :=
submodule.smul_sup I J K

theorem sup_mul : (I ⊔ J) * K = I * K ⊔ J * K :=
submodule.sup_smul I J K
variables {I J K}

lemma pow_le_pow {m n : ℕ} (h : m ≤ n) :
  I^n ≤ I^m :=
begin
  cases nat.exists_eq_add_of_le h with k hk,
  rw [hk, pow_add],
  exact le_trans (mul_le_inf) (inf_le_left)
end

lemma mul_eq_bot {R : Type*} [comm_ring R] [is_domain R] {I J : ideal R} :
  I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
⟨λ hij, or_iff_not_imp_left.mpr (λ I_ne_bot, J.eq_bot_iff.mpr (λ j hj,
  let ⟨i, hi, ne0⟩ := I.ne_bot_iff.mp I_ne_bot in
    or.resolve_left (mul_eq_zero.mp ((I * J).eq_bot_iff.mp hij _ (mul_mem_mul hi hj))) ne0)),
 λ h, by cases h; rw [← ideal.mul_bot, h, ideal.mul_comm]⟩

instance {R : Type*} [comm_ring R] [is_domain R] : no_zero_divisors (ideal R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ I J, mul_eq_bot.1 }

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
lemma prod_eq_bot {R : Type*} [comm_ring R] [is_domain R]
  {s : multiset (ideal R)} : s.prod = ⊥ ↔ ∃ I ∈ s, I = ⊥ :=
prod_zero_iff_exists_zero

/-- The radical of an ideal `I` consists of the elements `r` such that `r^n ∈ I` for some `n`. -/
def radical (I : ideal R) : ideal R :=
{ carrier := { r | ∃ n : ℕ, r ^ n ∈ I },
  zero_mem' := ⟨1, (pow_one (0:R)).symm ▸ I.zero_mem⟩,
  add_mem' := λ x y ⟨m, hxmi⟩ ⟨n, hyni⟩, ⟨m + n,
    (add_pow x y (m + n)).symm ▸ I.sum_mem $
    show ∀ c ∈ finset.range (nat.succ (m + n)),
      x ^ c * y ^ (m + n - c) * (nat.choose (m + n) c) ∈ I,
    from λ c hc, or.cases_on (le_total c m)
      (λ hcm, I.mul_mem_right _ $ I.mul_mem_left _ $ nat.add_comm n m ▸
        (add_tsub_assoc_of_le hcm n).symm ▸
        (pow_add y n (m-c)).symm ▸ I.mul_mem_right _ hyni)
      (λ hmc, I.mul_mem_right _ $ I.mul_mem_right _ $ add_tsub_cancel_of_le hmc ▸
        (pow_add x m (c-m)).symm ▸ I.mul_mem_right _ hxmi)⟩,
  smul_mem' := λ r s ⟨n, hsni⟩, ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r^n) hsni⟩ }

theorem le_radical : I ≤ radical I :=
λ r hri, ⟨1, (pow_one r).symm ▸ hri⟩

variables (R)
theorem radical_top : (radical ⊤ : ideal R) = ⊤ :=
(eq_top_iff_one _).2 ⟨0, submodule.mem_top⟩
variables {R}

theorem radical_mono (H : I ≤ J) : radical I ≤ radical J :=
λ r ⟨n, hrni⟩, ⟨n, H hrni⟩

variables (I)
@[simp] theorem radical_idem : radical (radical I) = radical I :=
le_antisymm (λ r ⟨n, k, hrnki⟩, ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩) le_radical
variables {I}

theorem radical_le_radical_iff : radical I ≤ radical J ↔ I ≤ radical J :=
⟨λ h, le_trans le_radical h, λ h, radical_idem J ▸ radical_mono h⟩

theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
⟨λ h, (eq_top_iff_one _).2 $ let ⟨n, hn⟩ := (eq_top_iff_one _).1 h in
  @one_pow R _ n ▸ hn, λ h, h.symm ▸ radical_top R⟩

theorem is_prime.radical (H : is_prime I) : radical I = I :=
le_antisymm (λ r ⟨n, hrni⟩, H.mem_of_pow_mem n hrni) le_radical

variables (I J)
theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
le_antisymm (radical_mono $ sup_le_sup le_radical le_radical) $
λ r ⟨n, hrnij⟩, let ⟨s, hs, t, ht, hst⟩ := submodule.mem_sup.1 hrnij in
@radical_idem _ _ (I ⊔ J) ▸ ⟨n, hst ▸ ideal.add_mem _
  (radical_mono le_sup_left hs) (radical_mono le_sup_right ht)⟩

theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
(λ r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩, ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
(pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩)

theorem radical_mul : radical (I * J) = radical I ⊓ radical J :=
le_antisymm (radical_inf I J ▸ radical_mono $ @mul_le_inf _ _ I J)
(λ r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩, ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩)
variables {I J}

theorem is_prime.radical_le_iff (hj : is_prime J) :
  radical I ≤ J ↔ I ≤ J :=
⟨le_trans le_radical, λ hij r ⟨n, hrni⟩, hj.mem_of_pow_mem n $ hij hrni⟩

theorem radical_eq_Inf (I : ideal R) :
  radical I = Inf { J : ideal R | I ≤ J ∧ is_prime J } :=
le_antisymm (le_Inf $ λ J hJ, hJ.2.radical_le_iff.2 hJ.1) $
λ r hr, classical.by_contradiction $ λ hri,
let ⟨m, (hrm : r ∉ radical m), him, hm⟩ := zorn.zorn_nonempty_partial_order₀
  {K : ideal R | r ∉ radical K}
  (λ c hc hcc y hyc, ⟨Sup c, λ ⟨n, hrnc⟩, let ⟨y, hyc, hrny⟩ :=
      (submodule.mem_Sup_of_directed ⟨y, hyc⟩ hcc.directed_on).1 hrnc in hc hyc ⟨n, hrny⟩,
    λ z, le_Sup⟩) I hri in
have ∀ x ∉ m, r ∈ radical (m ⊔ span {x}) := λ x hxm, classical.by_contradiction $ λ hrmx, hxm $
  hm (m ⊔ span {x}) hrmx le_sup_left ▸ (le_sup_right : _ ≤ m ⊔ span {x})
    (subset_span $ set.mem_singleton _),
have is_prime m, from ⟨by rintro rfl; rw radical_top at hrm; exact hrm trivial,
  λ x y hxym, or_iff_not_imp_left.2 $ λ hxm, classical.by_contradiction $ λ hym,
  let ⟨n, hrn⟩ := this _ hxm,
      ⟨p, hpm, q, hq, hpqrn⟩ := submodule.mem_sup.1 hrn,
      ⟨c, hcxq⟩ := mem_span_singleton'.1 hq in
  let ⟨k, hrk⟩ := this _ hym,
      ⟨f, hfm, g, hg, hfgrk⟩ := submodule.mem_sup.1 hrk,
      ⟨d, hdyg⟩ := mem_span_singleton'.1 hg in
  hrm ⟨n + k, by rw [pow_add, ← hpqrn, ← hcxq, ← hfgrk, ← hdyg, add_mul, mul_add (c*x),
                     mul_assoc c x (d*y), mul_left_comm x, ← mul_assoc];
    refine m.add_mem (m.mul_mem_right _ hpm) (m.add_mem (m.mul_mem_left _ hfm)
      (m.mul_mem_left _ hxym))⟩⟩,
hrm $ this.radical.symm ▸ (Inf_le ⟨him, this⟩ : Inf {J : ideal R | I ≤ J ∧ is_prime J} ≤ m) hr

@[simp] lemma radical_bot_of_is_domain {R : Type u} [comm_ring R] [is_domain R] :
  radical (⊥ : ideal R) = ⊥ :=
eq_bot_iff.2 (λ x hx, hx.rec_on (λ n hn, pow_eq_zero hn))

instance : comm_semiring (ideal R) := submodule.comm_semiring

variables (R)
theorem top_pow (n : ℕ) : (⊤ ^ n : ideal R) = ⊤ :=
nat.rec_on n one_eq_top $ λ n ih, by rw [pow_succ, ih, top_mul]
variables {R}

variables (I)
theorem radical_pow (n : ℕ) (H : n > 0) : radical (I^n) = radical I :=
nat.rec_on n (not.elim dec_trivial) (λ n ih H,
or.cases_on (lt_or_eq_of_le $ nat.le_of_lt_succ H)
  (λ H, calc radical (I^(n+1))
           = radical I ⊓ radical (I^n) : by { rw pow_succ, exact radical_mul _ _ }
       ... = radical I ⊓ radical I : by rw ih H
       ... = radical I : inf_idem)
  (λ H, H ▸ (pow_one I).symm ▸ rfl)) H

theorem is_prime.mul_le {I J P : ideal R} (hp : is_prime P) :
  I * J ≤ P ↔ I ≤ P ∨ J ≤ P :=
⟨λ h, or_iff_not_imp_left.2 $ λ hip j hj, let ⟨i, hi, hip⟩ := set.not_subset.1 hip in
  (hp.mem_or_mem $ h $ mul_mem_mul hi hj).resolve_left hip,
λ h, or.cases_on h (le_trans $ le_trans mul_le_inf inf_le_left)
  (le_trans $ le_trans mul_le_inf inf_le_right)⟩

theorem is_prime.inf_le {I J P : ideal R} (hp : is_prime P) :
  I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P :=
⟨λ h, hp.mul_le.1 $ le_trans mul_le_inf h,
λ h, or.cases_on h (le_trans inf_le_left) (le_trans inf_le_right)⟩

theorem is_prime.multiset_prod_le {s : multiset (ideal R)} {P : ideal R}
  (hp : is_prime P) (hne : s ≠ 0) :
  s.prod ≤ P ↔ ∃ I ∈ s, I ≤ P :=
suffices s.prod ≤ P → ∃ I ∈ s, I ≤ P,
  from ⟨this, λ ⟨i, his, hip⟩, le_trans multiset_prod_le_inf $
    le_trans (multiset.inf_le his) hip⟩,
begin
  classical,
  obtain ⟨b, hb⟩ : ∃ b, b ∈ s := multiset.exists_mem_of_ne_zero hne,
  obtain ⟨t, rfl⟩ : ∃ t, s = b ::ₘ t,
  from ⟨s.erase b, (multiset.cons_erase hb).symm⟩,
  refine t.induction_on _ _,
  { simp only [exists_prop, ←multiset.singleton_eq_cons, multiset.prod_singleton,
      multiset.mem_singleton, exists_eq_left, imp_self] },
  intros a s ih h,
  rw [multiset.cons_swap, multiset.prod_cons, hp.mul_le] at h,
  rw multiset.cons_swap,
  cases h,
  { exact ⟨a, multiset.mem_cons_self a _, h⟩ },
  obtain ⟨I, hI, ih⟩ : ∃ I ∈ b ::ₘ s, I ≤ P := ih h,
  exact ⟨I, multiset.mem_cons_of_mem hI, ih⟩
end

theorem is_prime.multiset_prod_map_le {s : multiset ι} (f : ι → ideal R) {P : ideal R}
  (hp : is_prime P) (hne : s ≠ 0) :
  (s.map f).prod ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
begin
  rw hp.multiset_prod_le (mt multiset.map_eq_zero.mp hne),
  simp_rw [exists_prop, multiset.mem_map, exists_exists_and_eq_and],
end

theorem is_prime.prod_le {s : finset ι} {f : ι → ideal R} {P : ideal R}
  (hp : is_prime P) (hne : s.nonempty) :
  s.prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
hp.multiset_prod_map_le f (mt finset.val_eq_zero.mp hne.ne_empty)

theorem is_prime.inf_le' {s : finset ι} {f : ι → ideal R} {P : ideal R} (hp : is_prime P)
  (hsne: s.nonempty) :
  s.inf f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
⟨λ h, (hp.prod_le hsne).1 $ le_trans prod_le_inf h,
  λ ⟨i, his, hip⟩, le_trans (finset.inf_le his) hip⟩

theorem subset_union {R : Type u} [comm_ring R] {I J K : ideal R} :
  (I : set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K :=
⟨λ h, or_iff_not_imp_left.2 $ λ hij s hsi,
  let ⟨r, hri, hrj⟩ := set.not_subset.1 hij in classical.by_contradiction $ λ hsk,
  or.cases_on (h $ I.add_mem hri hsi)
    (λ hj, hrj $ add_sub_cancel r s ▸ J.sub_mem hj ((h hsi).resolve_right hsk))
    (λ hk, hsk $ add_sub_cancel' r s ▸ K.sub_mem hk ((h hri).resolve_left hrj)),
λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset_union_left J K)
  (λ h, set.subset.trans h $ set.subset_union_right J K)⟩

theorem subset_union_prime' {R : Type u} [comm_ring R] {s : finset ι} {f : ι → ideal R} {a b : ι}
  (hp : ∀ i ∈ s, is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ f a ∪ f b ∪ (⋃ i ∈ (↑s : set ι), f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i :=
suffices (I : set R) ⊆ f a ∪ f b ∪ (⋃ i ∈ (↑s : set ι), f i) →
  I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i,
  from ⟨this, λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset.trans
      (set.subset_union_left _ _) (set.subset_union_left _ _)) $
    λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset.trans
      (set.subset_union_right _ _) (set.subset_union_left _ _)) $
    λ ⟨i, his, hi⟩, by refine (set.subset.trans hi $ set.subset.trans _ $
        set.subset_union_right _ _);
      exact set.subset_bUnion_of_mem (finset.mem_coe.2 his)⟩,
begin
  generalize hn : s.card = n, intros h,
  unfreezingI { induction n with n ih generalizing a b s },
  { clear hp,
    rw finset.card_eq_zero at hn, subst hn,
    rw [finset.coe_empty, set.bUnion_empty, set.union_empty, subset_union] at h,
    simpa only [exists_prop, finset.not_mem_empty, false_and, exists_false, or_false] },
  classical,
  replace hn : ∃ (i : ι) (t : finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n :=
  finset.card_eq_succ.1 hn,
  unfreezingI { rcases hn with ⟨i, t, hit, rfl, hn⟩ },
  replace hp : is_prime (f i) ∧ ∀ x ∈ t, is_prime (f x) := (t.forall_mem_insert _ _).1 hp,
  by_cases Ht : ∃ j ∈ t, f j ≤ f i,
  { obtain ⟨j, hjt, hfji⟩ : ∃ j ∈ t, f j ≤ f i := Ht,
    obtain ⟨u, hju, rfl⟩ : ∃ u, j ∉ u ∧ insert j u = t,
    { exact ⟨t.erase j, t.not_mem_erase j, finset.insert_erase hjt⟩ },
    have hp' : ∀ k ∈ insert i u, is_prime (f k),
    { rw finset.forall_mem_insert at hp ⊢, exact ⟨hp.1, hp.2.2⟩ },
    have hiu : i ∉ u := mt finset.mem_insert_of_mem hit,
    have hn' : (insert i u).card = n,
    { rwa finset.card_insert_of_not_mem at hn ⊢, exacts [hiu, hju] },
    have h' : (I : set R) ⊆ f a ∪ f b ∪ (⋃ k ∈ (↑(insert i u) : set ι), f k),
    { rw finset.coe_insert at h ⊢, rw finset.coe_insert at h,
      simp only [set.bUnion_insert] at h ⊢,
      rw [← set.union_assoc ↑(f i)] at h,
      erw [set.union_eq_self_of_subset_right hfji] at h,
      exact h },
    specialize @ih a b (insert i u) hp' hn' h',
    refine ih.imp id (or.imp id (exists_imp_exists $ λ k, _)), simp only [exists_prop],
    exact and.imp (λ hk, finset.insert_subset_insert i (finset.subset_insert j u) hk) id },
  by_cases Ha : f a ≤ f i,
  { have h' : (I : set R) ⊆ f i ∪ f b ∪ (⋃ j ∈ (↑t : set ι), f j),
    { rw [finset.coe_insert, set.bUnion_insert, ← set.union_assoc,
          set.union_right_comm ↑(f a)] at h,
      erw [set.union_eq_self_of_subset_left Ha] at h,
      exact h },
    specialize @ih i b t hp.2 hn h', right,
    rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { exact or.inr ⟨i, finset.mem_insert_self i t, ih⟩ },
    { exact or.inl ih },
    { exact or.inr ⟨k, finset.mem_insert_of_mem hkt, ih⟩ } },
  by_cases Hb : f b ≤ f i,
  { have h' : (I : set R) ⊆ f a ∪ f i ∪ (⋃ j ∈ (↑t : set ι), f j),
    { rw [finset.coe_insert, set.bUnion_insert, ← set.union_assoc, set.union_assoc ↑(f a)] at h,
      erw [set.union_eq_self_of_subset_left Hb] at h,
      exact h },
    specialize @ih a i t hp.2 hn h',
    rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { exact or.inl ih },
    { exact or.inr (or.inr ⟨i, finset.mem_insert_self i t, ih⟩) },
    { exact or.inr (or.inr ⟨k, finset.mem_insert_of_mem hkt, ih⟩) } },
  by_cases Hi : I ≤ f i,
  { exact or.inr (or.inr ⟨i, finset.mem_insert_self i t, Hi⟩) },
  have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f ≤ f i,
  { rcases t.eq_empty_or_nonempty with (rfl | hsne),
    { rw [finset.inf_empty, inf_top_eq, hp.1.inf_le, hp.1.inf_le, not_or_distrib, not_or_distrib],
      exact ⟨⟨Hi, Ha⟩, Hb⟩ },
    simp only [hp.1.inf_le, hp.1.inf_le' hsne, not_or_distrib],
    exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩ },
  rcases set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩,
  by_cases HI : (I : set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ (↑t : set ι), f j,
  { specialize ih hp.2 hn HI, rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { left, exact ih }, { right, left, exact ih },
    { right, right, exact ⟨k, finset.mem_insert_of_mem hkt, ih⟩ } },
  exfalso, rcases set.not_subset.1 HI with ⟨s, hsI, hs⟩,
  rw [finset.coe_insert, set.bUnion_insert] at h,
  have hsi : s ∈ f i := ((h hsI).resolve_left (mt or.inl hs)).resolve_right (mt or.inr hs),
  rcases h (I.add_mem hrI hsI) with ⟨ha | hb⟩ | hi | ht,
  { exact hs (or.inl $ or.inl $ add_sub_cancel' r s ▸ (f a).sub_mem ha hra) },
  { exact hs (or.inl $ or.inr $ add_sub_cancel' r s ▸ (f b).sub_mem hb hrb) },
  { exact hri (add_sub_cancel r s ▸ (f i).sub_mem hi hsi) },
  { rw set.mem_Union₂ at ht, rcases ht with ⟨j, hjt, hj⟩,
    simp only [finset.inf_eq_infi, set_like.mem_coe, submodule.mem_infi] at hr,
    exact hs (or.inr $ set.mem_bUnion hjt $ add_sub_cancel' r s ▸ (f j).sub_mem hj $ hr j hjt) }
end

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 00DS, Matsumura Ex.1.6. -/
theorem subset_union_prime {R : Type u} [comm_ring R] {s : finset ι} {f : ι → ideal R} (a b : ι)
  (hp : ∀ i ∈ s, i ≠ a → i ≠ b → is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
suffices (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) → ∃ i, i ∈ s ∧ I ≤ f i,
  from ⟨λ h, bex_def.2 $ this h, λ ⟨i, his, hi⟩, set.subset.trans hi $ set.subset_bUnion_of_mem $
    show i ∈ (↑s : set ι), from his⟩,
assume h : (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i),
begin
  classical,
  by_cases has : a ∈ s,
  { unfreezingI { obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s :=
      ⟨s.erase a, finset.not_mem_erase a s, finset.insert_erase has⟩ },
    by_cases hbt : b ∈ t,
    { unfreezingI { obtain ⟨u, hbu, rfl⟩ : ∃ u, b ∉ u ∧ insert b u = t :=
        ⟨t.erase b, finset.not_mem_erase b t, finset.insert_erase hbt⟩ },
      have hp' : ∀ i ∈ u, is_prime (f i),
      { intros i hiu, refine hp i (finset.mem_insert_of_mem (finset.mem_insert_of_mem hiu)) _ _;
        unfreezingI { rintro rfl }; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, finset.coe_insert, set.bUnion_insert, set.bUnion_insert,
          ← set.union_assoc, subset_union_prime' hp', bex_def] at h,
      rwa [finset.exists_mem_insert, finset.exists_mem_insert] },
    { have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hj, refine hp j (finset.mem_insert_of_mem hj) _ _;
        unfreezingI { rintro rfl }; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f a : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert } },
  { by_cases hbs : b ∈ s,
    { unfreezingI { obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ insert b t = s :=
        ⟨s.erase b, finset.not_mem_erase b s, finset.insert_erase hbs⟩ },
      have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hj, refine hp j (finset.mem_insert_of_mem hj) _ _;
        unfreezingI { rintro rfl }; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f b : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert },
    cases s.eq_empty_or_nonempty with hse hsne,
    { substI hse, rw [finset.coe_empty, set.bUnion_empty, set.subset_empty_iff] at h,
      have : (I : set R) ≠ ∅ := set.nonempty.ne_empty (set.nonempty_of_mem I.zero_mem),
      exact absurd h this },
    { cases hsne.bex with i his,
      unfreezingI { obtain ⟨t, hit, rfl⟩ : ∃ t, i ∉ t ∧ insert i t = s :=
        ⟨s.erase i, finset.not_mem_erase i s, finset.insert_erase his⟩ },
      have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hj, refine hp j (finset.mem_insert_of_mem hj) _ _;
        unfreezingI { rintro rfl }; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f i : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert } }
end

section dvd

/-- If `I` divides `J`, then `I` contains `J`.

In a Dedekind domain, to divide and contain are equivalent, see `ideal.dvd_iff_le`.
-/
lemma le_of_dvd {I J : ideal R} : I ∣ J → J ≤ I
| ⟨K, h⟩ := h.symm ▸ le_trans mul_le_inf inf_le_left

lemma is_unit_iff {I : ideal R} :
  is_unit I ↔ I = ⊤ :=
is_unit_iff_dvd_one.trans ((@one_eq_top R _).symm ▸
 ⟨λ h, eq_top_iff.mpr (ideal.le_of_dvd h), λ h, ⟨⊤, by rw [mul_top, h]⟩⟩)

instance unique_units : unique ((ideal R)ˣ) :=
{ default := 1,
  uniq := λ u, units.ext
    (show (u : ideal R) = 1, by rw [is_unit_iff.mp u.is_unit, one_eq_top]) }

end dvd

end mul_and_radical

section map_and_comap

variables {R : Type u} {S : Type v}

section semiring
variables [semiring R] [semiring S]
variables (f : R →+* S)
variables {I J : ideal R} {K L : ideal S}

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map (I : ideal R) : ideal S :=
span (f '' I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap (I : ideal S) : ideal R :=
{ carrier := f ⁻¹' I,
  .. I.comap f.to_semilinear_map }

variables {f}
theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
span_mono $ set.image_subset _ h

theorem mem_map_of_mem (f : R →+* S) {I : ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
subset_span ⟨x, h, rfl⟩

lemma apply_coe_mem_map (f : R →+* S) (I : ideal R) (x : I) : f x ∈ I.map f :=
mem_map_of_mem f x.prop

theorem map_le_iff_le_comap :
  map f I ≤ K ↔ I ≤ comap f K :=
span_le.trans set.image_subset_iff

@[simp] theorem mem_comap {x} : x ∈ comap f K ↔ f x ∈ K := iff.rfl

theorem comap_mono (h : K ≤ L) : comap f K ≤ comap f L :=
set.preimage_mono (λ x hx, h hx)
variables (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
(ne_top_iff_one _).2 $ by rw [mem_comap, f.map_one];
  exact (ne_top_iff_one _).1 hK

lemma map_le_comap_of_inv_on (g : S →+* R) (I : ideal R) (hf : set.left_inv_on g f I) :
  I.map f ≤ I.comap g :=
begin
  refine ideal.span_le.2 _,
  rintros x ⟨x, hx, rfl⟩,
  rw [set_like.mem_coe, mem_comap, hf hx],
  exact hx,
end

lemma comap_le_map_of_inv_on (g : S →+* R) (I : ideal S) (hf : set.left_inv_on g f (f ⁻¹' I)) :
  I.comap f ≤ I.map g :=
λ x (hx : f x ∈ I), hf hx ▸ ideal.mem_map_of_mem g hx

/-- The `ideal` version of `set.image_subset_preimage_of_inverse`. -/
lemma map_le_comap_of_inverse (g : S →+* R) (I : ideal R) (h : function.left_inverse g f) :
  I.map f ≤ I.comap g :=
map_le_comap_of_inv_on _ _ _ $ h.left_inv_on _

/-- The `ideal` version of `set.preimage_subset_image_of_inverse`. -/
lemma comap_le_map_of_inverse (g : S →+* R) (I : ideal S) (h : function.left_inverse g f) :
  I.comap f ≤ I.map g :=
comap_le_map_of_inv_on _ _ _ $ h.left_inv_on _

instance is_prime.comap [hK : K.is_prime] : (comap f K).is_prime :=
⟨comap_ne_top _ hK.1, λ x y,
  by simp only [mem_comap, f.map_mul]; apply hK.2⟩

variables (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
(eq_top_iff_one _).2 $ subset_span ⟨1, trivial, f.map_one⟩

variable (f)
lemma gc_map_comap : galois_connection (ideal.map f) (ideal.comap f) :=
λ I J, ideal.map_le_iff_le_comap

@[simp] lemma comap_id : I.comap (ring_hom.id R) = I :=
ideal.ext $ λ _, iff.rfl

@[simp] lemma map_id : I.map (ring_hom.id R) = I :=
(gc_map_comap (ring_hom.id R)).l_unique galois_connection.id comap_id

lemma comap_comap {T : Type*} [semiring T] {I : ideal T} (f : R →+* S)
  (g : S →+* T) : (I.comap g).comap f = I.comap (g.comp f) := rfl

lemma map_map {T : Type*} [semiring T] {I : ideal R} (f : R →+* S)
  (g : S →+* T) : (I.map f).map g = I.map (g.comp f) :=
((gc_map_comap f).compose (gc_map_comap g)).l_unique
  (gc_map_comap (g.comp f)) (λ _, comap_comap _ _)

lemma map_span (f : R →+* S) (s : set R) :
  map f (span s) = span (f '' s) :=
symm $ submodule.span_eq_of_le _
  (λ y ⟨x, hy, x_eq⟩, x_eq ▸ mem_map_of_mem f (subset_span hy))
  (map_le_iff_le_comap.2 $ span_le.2 $ set.image_subset_iff.1 subset_span)

variables {f I J K L}

lemma map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
(gc_map_comap f).l_le

lemma le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
(gc_map_comap f).le_u

lemma le_comap_map : I ≤ (I.map f).comap f :=
(gc_map_comap f).le_u_l _

lemma map_comap_le : (K.comap f).map f ≤ K :=
(gc_map_comap f).l_u_le _

@[simp] lemma comap_top : (⊤ : ideal S).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp] lemma comap_eq_top_iff {I : ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
⟨ λ h, I.eq_top_iff_one.mpr (f.map_one ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
  λ h, by rw [h, comap_top] ⟩

@[simp] lemma map_bot : (⊥ : ideal R).map f = ⊥ :=
(gc_map_comap f).l_bot

variables (f I J K L)

@[simp] lemma map_comap_map : ((I.map f).comap f).map f = I.map f :=
(gc_map_comap f).l_u_l_eq_l I

@[simp] lemma comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
(gc_map_comap f).u_l_u_eq_u K

lemma map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
(gc_map_comap f).l_sup

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L := rfl

variables {ι : Sort*}

lemma map_supr (K : ι → ideal R) : (supr K).map f = ⨆ i, (K i).map f :=
(gc_map_comap f).l_supr

lemma comap_infi (K : ι → ideal S) : (infi K).comap f = ⨅ i, (K i).comap f :=
(gc_map_comap f).u_infi

lemma map_Sup (s : set (ideal R)): (Sup s).map f = ⨆ I ∈ s, (I : ideal R).map f :=
(gc_map_comap f).l_Sup

lemma comap_Inf (s : set (ideal S)): (Inf s).comap f = ⨅ I ∈ s, (I : ideal S).comap f :=
(gc_map_comap f).u_Inf

lemma comap_Inf' (s : set (ideal S)) : (Inf s).comap f = ⨅ I ∈ (comap f '' s), I :=
trans (comap_Inf f s) (by rw infi_image)

theorem comap_is_prime [H : is_prime K] : is_prime (comap f K) :=
⟨comap_ne_top f H.ne_top,
  λ x y h, H.mem_or_mem $ by rwa [mem_comap, ring_hom.map_mul] at h⟩

variables {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
(gc_map_comap f).monotone_l.map_inf_le _ _

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
(gc_map_comap f).monotone_u.le_map_sup _ _

section surjective
variables (hf : function.surjective f)
include hf

open function

theorem map_comap_of_surjective (I : ideal S) :
  map f (comap f I) = I :=
le_antisymm (map_le_iff_le_comap.2 le_rfl)
(λ s hsi, let ⟨r, hfrs⟩ := hf s in
  hfrs ▸ (mem_map_of_mem f $ show f r ∈ I, from hfrs.symm ▸ hsi))

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
galois_insertion.monotone_intro
  ((gc_map_comap f).monotone_u)
  ((gc_map_comap f).monotone_l)
  (λ _, le_comap_map)
  (map_comap_of_surjective _ hf)

lemma map_surjective_of_surjective : surjective (map f) :=
(gi_map_comap f hf).l_surjective

lemma comap_injective_of_surjective : injective (comap f) :=
(gi_map_comap f hf).u_injective

lemma map_sup_comap_of_surjective (I J : ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
(gi_map_comap f hf).l_sup_u _ _

lemma map_supr_comap_of_surjective (K : ι → ideal S) : (⨆i, (K i).comap f).map f = supr K :=
(gi_map_comap f hf).l_supr_u _

lemma map_inf_comap_of_surjective (I J : ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
(gi_map_comap f hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (K : ι → ideal S) : (⨅i, (K i).comap f).map f = infi K :=
(gi_map_comap f hf).l_infi_u _

theorem mem_image_of_mem_map_of_surjective {I : ideal R} {y}
  (H : y ∈ map f I) : y ∈ f '' I :=
submodule.span_induction H (λ _, id) ⟨0, I.zero_mem, f.map_zero⟩
(λ y1 y2 ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩,
  ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ f.map_add _ _⟩)
(λ c y ⟨x, hxi, hxy⟩, let ⟨d, hdc⟩ := hf c in ⟨d • x, I.smul_mem _ hxi, hdc ▸ hxy ▸ f.map_mul _ _⟩)

lemma mem_map_iff_of_surjective {I : ideal R} {y} :
  y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
⟨λ h, (set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h),
  λ ⟨x, hx⟩, hx.right ▸ (mem_map_of_mem f hx.left)⟩

lemma le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I :=
λ h, (map_comap_of_surjective f hf K) ▸ map_mono h

end surjective

section injective
variables (hf : function.injective f)
include hf

lemma comap_bot_le_of_injective : comap f ⊥ ≤ I :=
begin
  refine le_trans (λ x hx, _) bot_le,
  rw [mem_comap, submodule.mem_bot, ← ring_hom.map_zero f] at hx,
  exact eq.symm (hf hx) ▸ (submodule.zero_mem ⊥)
end

end injective

end semiring

section ring
variables [ring R] [ring S] (f : R →+* S) {I : ideal R}

section surjective

variables (hf : function.surjective f)
include hf

theorem comap_map_of_surjective (I : ideal R) : comap f (map f I) = I ⊔ comap f ⊥ :=
le_antisymm (assume r h, let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h in
  submodule.mem_sup.2 ⟨s, hsi, r - s, (submodule.mem_bot S).2 $ by rw [f.map_sub, hfsr, sub_self],
  add_sub_cancel'_right s r⟩)
(sup_le (map_le_iff_le_comap.1 le_rfl) (comap_mono bot_le))


/-- Correspondence theorem -/
def rel_iso_of_surjective : ideal S ≃o { p : ideal R // comap f ⊥ ≤ p } :=
{ to_fun := λ J, ⟨comap f J, comap_mono bot_le⟩,
  inv_fun := λ I, map f I.1,
  left_inv := λ J, map_comap_of_surjective f hf J,
  right_inv := λ I, subtype.eq $ show comap f (map f I.1) = I.1,
    from (comap_map_of_surjective f hf I).symm ▸ le_antisymm
      (sup_le le_rfl I.2) le_sup_left,
  map_rel_iff' := λ I1 I2, ⟨λ H, map_comap_of_surjective f hf I1 ▸
    map_comap_of_surjective f hf I2 ▸ map_mono H, comap_mono⟩ }

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def order_embedding_of_surjective : ideal S ↪o ideal R :=
(rel_iso_of_surjective f hf).to_rel_embedding.trans (subtype.rel_embedding _ _)

theorem map_eq_top_or_is_maximal_of_surjective {I : ideal R} (H : is_maximal I) :
  (map f I) = ⊤ ∨ is_maximal (map f I) :=
begin
  refine or_iff_not_imp_left.2 (λ ne_top, ⟨⟨λ h, ne_top h, λ J hJ, _⟩⟩),
  { refine (rel_iso_of_surjective f hf).injective
      (subtype.ext_iff.2 (eq.trans (H.1.2 (comap f J) (lt_of_le_of_ne _ _)) comap_top.symm)),
    { exact (map_le_iff_le_comap).1 (le_of_lt hJ) },
    { exact λ h, hJ.right (le_map_of_comap_le_of_surjective f hf (le_of_eq h.symm)) } }
end

theorem comap_is_maximal_of_surjective {K : ideal S} [H : is_maximal K] : is_maximal (comap f K) :=
begin
  refine ⟨⟨comap_ne_top _ H.1.1, λ J hJ, _⟩⟩,
  suffices : map f J = ⊤,
  { replace this := congr_arg (comap f) this,
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this,
    rw eq_top_iff,
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono (bot_le)) (le_of_lt hJ))) },
  refine H.1.2 (map f J) (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ))
    (λ h, ne_of_lt hJ (trans (congr_arg (comap f) h) _))),
  rw [comap_map_of_surjective _ hf, sup_eq_left],
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)
end

end surjective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `map f (map f.symm) = I`. -/
@[simp]
lemma map_of_equiv (I : ideal R) (f : R ≃+* S) : (I.map (f : R →+* S)).map (f.symm : S →+* R) = I :=
by simp [← ring_equiv.to_ring_hom_eq_coe, map_map]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `comap f.symm (comap f) = I`. -/
@[simp]
lemma comap_of_equiv (I : ideal R) (f : R ≃+* S) :
  (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I :=
by simp [← ring_equiv.to_ring_hom_eq_coe, comap_comap]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `map f I = comap f.symm I`. -/
lemma map_comap_of_equiv (I : ideal R) (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
le_antisymm (le_comap_of_map_le (map_of_equiv I f).le)
  (le_map_of_comap_le_of_surjective _ f.surjective (comap_of_equiv I f).le)

section bijective
variables (hf : function.bijective f)
include hf

/-- Special case of the correspondence theorem for isomorphic rings -/
def rel_iso_of_bijective : ideal S ≃o ideal R :=
{ to_fun := comap f,
  inv_fun := map f,
  left_inv := (rel_iso_of_surjective f hf.right).left_inv,
  right_inv := λ J, subtype.ext_iff.1
    ((rel_iso_of_surjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩),
  map_rel_iff' := (rel_iso_of_surjective f hf.right).map_rel_iff' }

lemma comap_le_iff_le_map {I : ideal R} {K : ideal S} : comap f K ≤ I ↔ K ≤ map f I :=
⟨λ h, le_map_of_comap_le_of_surjective f hf.right h,
 λ h, ((rel_iso_of_bijective f hf).right_inv I) ▸ comap_mono h⟩

theorem map.is_maximal {I : ideal R} (H : is_maximal I) : is_maximal (map f I) :=
by refine or_iff_not_imp_left.1
  (map_eq_top_or_is_maximal_of_surjective f hf.right H) (λ h, H.1.1 _);
calc I = comap f (map f I) : ((rel_iso_of_bijective f hf).right_inv I).symm
   ... = comap f ⊤ : by rw h
   ... = ⊤ : by rw comap_top

end bijective

lemma ring_equiv.bot_maximal_iff (e : R ≃+* S) :
  (⊥ : ideal R).is_maximal ↔ (⊥ : ideal S).is_maximal :=
⟨λ h, (@map_bot _ _ _ _ e.to_ring_hom) ▸ map.is_maximal e.to_ring_hom e.bijective h,
  λ h, (@map_bot _ _ _ _ e.symm.to_ring_hom) ▸ map.is_maximal e.symm.to_ring_hom e.symm.bijective h⟩

end ring

section comm_ring

variables [comm_ring R] [comm_ring S]
variables (f : R →+* S)
variables {I J : ideal R} {K L : ideal S}

lemma mem_quotient_iff_mem (hIJ : I ≤ J) {x : R} :
  quotient.mk I x ∈ J.map (quotient.mk I) ↔ x ∈ J :=
begin
  refine iff.trans (mem_map_iff_of_surjective _ quotient.mk_surjective) _,
  split,
  { rintros ⟨x, x_mem, x_eq⟩,
    simpa using J.add_mem (hIJ (quotient.eq.mp x_eq.symm)) x_mem },
  { intro x_mem,
    exact ⟨x, x_mem, rfl⟩ }
end

variables (I J K L)

theorem map_mul : map f (I * J) = map f I * map f J :=
le_antisymm (map_le_iff_le_comap.2 $ mul_le.2 $ λ r hri s hsj,
  show f (r * s) ∈ _, by rw f.map_mul;
  exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
(trans_rel_right _ (span_mul_span _ _) $ span_le.2 $
  set.Union₂_subset $ λ i ⟨r, hri, hfri⟩,
  set.Union₂_subset $ λ j ⟨s, hsj, hfsj⟩,
  set.singleton_subset_iff.2 $ hfri ▸ hfsj ▸
  by rw [← f.map_mul];
  exact mem_map_of_mem f (mul_mem_mul hri hsj))

theorem comap_radical : comap f (radical K) = radical (comap f K) :=
le_antisymm (λ r ⟨n, hfrnk⟩, ⟨n, show f (r ^ n) ∈ K,
  from (f.map_pow r n).symm ▸ hfrnk⟩)
(λ r ⟨n, hfrnk⟩, ⟨n, f.map_pow r n ▸ hfrnk⟩)

@[simp] lemma map_quotient_self :
  map (quotient.mk I) I = ⊥ :=
eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $ λ x hx,
(submodule.mem_bot (R ⧸ I)).2 $ ideal.quotient.eq_zero_iff_mem.2 hx

variables {I J K L}

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
map_le_iff_le_comap.2 $ λ r ⟨n, hrni⟩, ⟨n, f.map_pow r n ▸ mem_map_of_mem f hrni⟩

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
map_le_iff_le_comap.1 $ (map_mul f (comap f K) (comap f L)).symm ▸
mul_mono (map_le_iff_le_comap.2 $ le_rfl) (map_le_iff_le_comap.2 $ le_rfl)

end comm_ring

end map_and_comap

section is_primary
variables {R : Type u} [comm_semiring R]

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def is_primary (I : ideal R) : Prop :=
I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I

theorem is_primary.to_is_prime (I : ideal R) (hi : is_prime I) : is_primary I :=
⟨hi.1, λ x y hxy, (hi.mem_or_mem hxy).imp id $ λ hyi, le_radical hyi⟩

theorem mem_radical_of_pow_mem {I : ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) :
  x ∈ radical I :=
radical_idem I ▸ ⟨m, hx⟩

theorem is_prime_radical {I : ideal R} (hi : is_primary I) : is_prime (radical I) :=
⟨mt radical_eq_top.1 hi.1, λ x y ⟨m, hxy⟩, begin
  rw mul_pow at hxy, cases hi.2 hxy,
  { exact or.inl ⟨m, h⟩ },
  { exact or.inr (mem_radical_of_pow_mem h) }
end⟩

theorem is_primary_inf {I J : ideal R} (hi : is_primary I) (hj : is_primary J)
  (hij : radical I = radical J) : is_primary (I ⊓ J) :=
⟨ne_of_lt $ lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.2 hi.1), λ x y ⟨hxyi, hxyj⟩,
begin
  rw [radical_inf, hij, inf_idem],
  cases hi.2 hxyi with hxi hyi, cases hj.2 hxyj with hxj hyj,
  { exact or.inl ⟨hxi, hxj⟩ },
  { exact or.inr hyj },
  { rw hij at hyi, exact or.inr hyi }
end⟩

end is_primary

end ideal

namespace ring_hom

variables {R : Type u} {S : Type v} {T : Type v}

section semiring
variables [semiring R] [semiring S] [semiring T] (f : R →+* S) (g : T →+* S)

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker : ideal R := ideal.comap f ⊥

/-- An element is in the kernel if and only if it maps to zero.-/
lemma mem_ker {r} : r ∈ ker f ↔ f r = 0 :=
by rw [ker, ideal.mem_comap, submodule.mem_bot]

lemma ker_eq : ((ker f) : set R) = set.preimage f {0} := rfl

lemma ker_eq_comap_bot (f : R →+* S) : f.ker = ideal.comap f ⊥ := rfl

lemma comap_ker (f : S →+* R) : f.ker.comap g = (f.comp g).ker :=
by rw [ring_hom.ker_eq_comap_bot, ideal.comap_comap, ring_hom.ker_eq_comap_bot]

/-- If the target is not the zero ring, then one is not in the kernel.-/
lemma not_one_mem_ker [nontrivial S] (f : R →+* S) : (1:R) ∉ ker f :=
by { rw [mem_ker, f.map_one], exact one_ne_zero }

lemma ker_ne_top [nontrivial S] (f : R →+* S) : f.ker ≠ ⊤ :=
(ideal.ne_top_iff_one _).mpr $ not_one_mem_ker f

end semiring

section ring
variables [ring R] [semiring S] (f : R →+* S)

lemma injective_iff_ker_eq_bot : function.injective f ↔ ker f = ⊥ :=
by { rw [set_like.ext'_iff, ker_eq, set.ext_iff], exact f.injective_iff' }

lemma ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 :=
by { rw [← f.injective_iff, injective_iff_ker_eq_bot] }

@[simp] lemma ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ :=
by simpa only [←injective_iff_ker_eq_bot] using f.injective

end ring

section comm_ring
variables [comm_ring R] [comm_ring S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def ker_lift (f : R →+* S) : R ⧸ f.ker →+* S :=
ideal.quotient.lift _ f $ λ r, f.mem_ker.mp

@[simp]
lemma ker_lift_mk (f : R →+* S) (r : R) : ker_lift f (ideal.quotient.mk f.ker r) = f r :=
ideal.quotient.lift_mk _ _ _

/-- The induced map from the quotient by the kernel is injective. -/
lemma ker_lift_injective (f : R →+* S) : function.injective (ker_lift f) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : f a = f b), quotient.sound' $
show a - b ∈ ker f, by rw [mem_ker, map_sub, h, sub_self]

variable {f}

/-- The **first isomorphism theorem** for commutative rings, computable version. -/
def quotient_ker_equiv_of_right_inverse
  {g : S → R} (hf : function.right_inverse g f) :
  R ⧸ f.ker ≃+* S :=
{ to_fun := ker_lift f,
  inv_fun := (ideal.quotient.mk f.ker) ∘ g,
  left_inv := begin
    rintro ⟨x⟩,
    apply ker_lift_injective,
    simp [hf (f x)],
  end,
  right_inv := hf,
  ..ker_lift f}

@[simp]
lemma quotient_ker_equiv_of_right_inverse.apply {g : S → R} (hf : function.right_inverse g f)
  (x : R ⧸ f.ker) : quotient_ker_equiv_of_right_inverse hf x = ker_lift f x := rfl

@[simp]
lemma quotient_ker_equiv_of_right_inverse.symm.apply {g : S → R} (hf : function.right_inverse g f)
  (x : S) : (quotient_ker_equiv_of_right_inverse hf).symm x = ideal.quotient.mk f.ker (g x) := rfl

/-- The **first isomorphism theorem** for commutative rings. -/
noncomputable def quotient_ker_equiv_of_surjective (hf : function.surjective f) :
  R ⧸ f.ker ≃+* S :=
quotient_ker_equiv_of_right_inverse (classical.some_spec hf.has_right_inverse)

end comm_ring

/-- The kernel of a homomorphism to a domain is a prime ideal. -/
lemma ker_is_prime [ring R] [ring S] [is_domain S] (f : R →+* S) :
  (ker f).is_prime :=
⟨by { rw [ne.def, ideal.eq_top_iff_one], exact not_one_mem_ker f },
λ x y, by simpa only [mem_ker, f.map_mul] using @eq_zero_or_eq_zero_of_mul_eq_zero S _ _ _ _ _⟩

/-- The kernel of a homomorphism to a field is a maximal ideal. -/
lemma ker_is_maximal_of_surjective {R K : Type*} [ring R] [field K]
  (f : R →+* K) (hf : function.surjective f) :
  f.ker.is_maximal :=
begin
  refine ideal.is_maximal_iff.mpr
    ⟨λ h1, @one_ne_zero K _ _ $ f.map_one ▸ f.mem_ker.mp h1,
    λ J x hJ hxf hxJ, _⟩,
  obtain ⟨y, hy⟩ := hf (f x)⁻¹,
  have H : 1 = y * x - (y * x - 1) := (sub_sub_cancel _ _).symm,
  rw H,
  refine J.sub_mem (J.mul_mem_left _ hxJ) (hJ _),
  rw f.mem_ker,
  simp only [hy, ring_hom.map_sub, ring_hom.map_one, ring_hom.map_mul,
    inv_mul_cancel (mt f.mem_ker.mpr hxf), sub_self],
end

end ring_hom

namespace ideal

variables {R : Type*} {S : Type*}

section semiring
variables [semiring R] [semiring S]

lemma map_eq_bot_iff_le_ker {I : ideal R} (f : R →+* S) : I.map f = ⊥ ↔ I ≤ f.ker :=
by rw [ring_hom.ker, eq_bot_iff, map_le_iff_le_comap]

lemma ker_le_comap {K : ideal S} (f : R →+* S) : f.ker ≤ comap f K :=
λ x hx, mem_comap.2 (((ring_hom.mem_ker f).1 hx).symm ▸ K.zero_mem)

end semiring

section ring
variables [ring R] [ring S]

lemma map_Inf {A : set (ideal R)} {f : R →+* S} (hf : function.surjective f) :
  (∀ J ∈ A, ring_hom.ker f ≤ J) → map f (Inf A) = Inf (map f '' A) :=
begin
  refine λ h, le_antisymm (le_Inf _) _,
  { intros j hj y hy,
    cases (mem_map_iff_of_surjective f hf).1 hy with x hx,
    cases (set.mem_image _ _ _).mp hj with J hJ,
    rw [← hJ.right, ← hx.right],
    exact mem_map_of_mem f (Inf_le_of_le hJ.left (le_of_eq rfl) hx.left) },
  { intros y hy,
    cases hf y with x hx,
    refine hx ▸ (mem_map_of_mem f _),
    have : ∀ I ∈ A, y ∈ map f I, by simpa using hy,
    rw [submodule.mem_Inf],
    intros J hJ,
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩,
    have : x - x' ∈ J,
    { apply h J hJ,
      rw [ring_hom.mem_ker, ring_hom.map_sub, hx, sub_self] },
    simpa only [sub_add_cancel] using J.add_mem this hx' }
end

theorem map_is_prime_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R}
  [H : is_prime I] (hk : ring_hom.ker f ≤ I) : is_prime (map f I) :=
begin
  refine ⟨λ h, H.ne_top (eq_top_iff.2 _), λ x y, _⟩,
  { replace h := congr_arg (comap f) h,
    rw [comap_map_of_surjective _ hf, comap_top] at h,
    exact h ▸ sup_le (le_of_eq rfl) hk },
  { refine λ hxy, (hf x).rec_on (λ a ha, (hf y).rec_on (λ b hb, _)),
    rw [← ha, ← hb, ← ring_hom.map_mul, mem_map_iff_of_surjective _ hf] at hxy,
    rcases hxy with ⟨c, hc, hc'⟩,
    rw [← sub_eq_zero, ← ring_hom.map_sub] at hc',
    have : a * b ∈ I,
    { convert I.sub_mem hc (hk (hc' : c - a * b ∈ f.ker)),
      abel },
    exact (H.mem_or_mem this).imp (λ h, ha ▸ mem_map_of_mem f h) (λ h, hb ▸ mem_map_of_mem f h) }
end

theorem map_is_prime_of_equiv (f : R ≃+* S) {I : ideal R} [is_prime I] :
  is_prime (map (f : R →+* S) I) :=
map_is_prime_of_surjective f.surjective $ by simp

end ring

section comm_ring
variables [comm_ring R] [comm_ring S]

@[simp] lemma mk_ker {I : ideal R} : (quotient.mk I).ker = I :=
by ext; rw [ring_hom.ker, mem_comap, submodule.mem_bot, quotient.eq_zero_iff_mem]

lemma map_mk_eq_bot_of_le {I J : ideal R} (h : I ≤ J) : I.map (J^.quotient.mk) = ⊥ :=
by { rw [map_eq_bot_iff_le_ker, mk_ker], exact h }

lemma ker_quotient_lift {S : Type v} [comm_ring S] {I : ideal R} (f : R →+* S) (H : I ≤ f.ker) :
  (ideal.quotient.lift I f H).ker = (f.ker).map I^.quotient.mk :=
begin
  ext x,
  split,
  { intro hx,
    obtain ⟨y, hy⟩ := quotient.mk_surjective x,
    rw [ring_hom.mem_ker, ← hy, ideal.quotient.lift_mk, ← ring_hom.mem_ker] at hx,
    rw [← hy, mem_map_iff_of_surjective I^.quotient.mk quotient.mk_surjective],
    exact ⟨y, hx, rfl⟩ },
  { intro hx,
    rw mem_map_iff_of_surjective I^.quotient.mk quotient.mk_surjective at hx,
    obtain ⟨y, hy⟩ := hx,
    rw [ring_hom.mem_ker, ← hy.right, ideal.quotient.lift_mk, ← (ring_hom.mem_ker f)],
    exact hy.left },
end

theorem map_eq_iff_sup_ker_eq_of_surjective {I J : ideal R} (f : R →+* S)
  (hf : function.surjective f) : map f I = map f J ↔ I ⊔ f.ker = J ⊔ f.ker :=
by rw [← (comap_injective_of_surjective f hf).eq_iff, comap_map_of_surjective f hf,
  comap_map_of_surjective f hf, ring_hom.ker_eq_comap_bot]

theorem map_radical_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R}
  (h : ring_hom.ker f ≤ I) : map f (I.radical) = (map f I).radical :=
begin
  rw [radical_eq_Inf, radical_eq_Inf],
  have : ∀ J ∈ {J : ideal R | I ≤ J ∧ J.is_prime}, f.ker ≤ J := λ J hJ, le_trans h hJ.left,
  convert map_Inf hf this,
  refine funext (λ j, propext ⟨_, _⟩),
  { rintros ⟨hj, hj'⟩,
    haveI : j.is_prime := hj',
    exact ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_is_prime f j⟩,
      map_comap_of_surjective f hf j⟩⟩ },
  { rintro ⟨J, ⟨hJ, hJ'⟩⟩,
    haveI : J.is_prime := hJ.right,
    refine ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_is_prime_of_surjective hf (le_trans h hJ.left)⟩ },
end

@[simp] lemma bot_quotient_is_maximal_iff (I : ideal R) :
  (⊥ : ideal (R ⧸ I)).is_maximal ↔ I.is_maximal :=
⟨λ hI, (@mk_ker _ _ I) ▸
  @comap_is_maximal_of_surjective _ _ _ _ (quotient.mk I) quotient.mk_surjective ⊥ hI,
 λ hI, @bot_is_maximal _ (@field.to_division_ring _ (@quotient.field _ _ I hI)) ⟩

section quotient_algebra

variables (R₁ R₂ : Type*) {A B : Type*}
variables [comm_semiring R₁] [comm_semiring R₂] [comm_ring A] [comm_ring B]
variables [algebra R₁ A] [algebra R₂ A] [algebra R₁ B]

/-- The `R₁`-algebra structure on `A/I` for an `R₁`-algebra `A` -/
instance quotient.algebra {I : ideal A} : algebra R₁ (A ⧸ I) :=
{ to_fun := λ x, ideal.quotient.mk I (algebra_map R₁ A x),
  smul := (•),
  smul_def' := λ r x, quotient.induction_on' x $ λ x,
      ((quotient.mk I).congr_arg $ algebra.smul_def _ _).trans (ring_hom.map_mul _ _ _),
  commutes' := λ _ _, mul_comm _ _,
  .. ring_hom.comp (ideal.quotient.mk I) (algebra_map R₁ A) }

-- Lean can struggle to find this instance later if we don't provide this shortcut
instance quotient.is_scalar_tower [has_scalar R₁ R₂] [is_scalar_tower R₁ R₂ A] (I : ideal A) :
  is_scalar_tower R₁ R₂ (A ⧸ I) :=
by apply_instance

/-- The canonical morphism `A →ₐ[R₁] A ⧸ I` as morphism of `R₁`-algebras, for `I` an ideal of
`A`, where `A` is an `R₁`-algebra. -/
def quotient.mkₐ (I : ideal A) : A →ₐ[R₁] A ⧸ I :=
⟨λ a, submodule.quotient.mk a, rfl, λ _ _, rfl, rfl, λ _ _, rfl, λ _, rfl⟩

lemma quotient.alg_map_eq (I : ideal A) :
  algebra_map R₁ (A ⧸ I) = (algebra_map A (A ⧸ I)).comp (algebra_map R₁ A) :=
rfl

lemma quotient.mkₐ_to_ring_hom (I : ideal A) :
  (quotient.mkₐ R₁ I).to_ring_hom = ideal.quotient.mk I := rfl

@[simp] lemma quotient.mkₐ_eq_mk (I : ideal A) :
  ⇑(quotient.mkₐ R₁ I) = ideal.quotient.mk I := rfl

@[simp] lemma quotient.algebra_map_eq (I : ideal R) :
  algebra_map R (R ⧸ I) = I^.quotient.mk :=
rfl

@[simp] lemma quotient.mk_comp_algebra_map (I : ideal A) :
  (quotient.mk I).comp (algebra_map R₁ A) = algebra_map R₁ (A ⧸ I) :=
rfl

@[simp] lemma quotient.mk_algebra_map (I : ideal A) (x : R₁) :
  quotient.mk I (algebra_map R₁ A x) = algebra_map R₁ (A ⧸ I) x :=
rfl

/-- The canonical morphism `A →ₐ[R₁] I.quotient` is surjective. -/
lemma quotient.mkₐ_surjective (I : ideal A) : function.surjective (quotient.mkₐ R₁ I) :=
surjective_quot_mk _

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
lemma quotient.mkₐ_ker (I : ideal A) : (quotient.mkₐ R₁ I : A →+* A ⧸ I).ker = I :=
ideal.mk_ker

variables {R₁}

lemma ker_lift.map_smul (f : A →ₐ[R₁] B) (r : R₁) (x : A ⧸ f.to_ring_hom.ker) :
  f.to_ring_hom.ker_lift (r • x) = r • f.to_ring_hom.ker_lift x :=
begin
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R₁ _ x,
  rw [← alg_hom.map_smul, quotient.mkₐ_eq_mk, ring_hom.ker_lift_mk],
  exact f.map_smul _ _
end

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def ker_lift_alg (f : A →ₐ[R₁] B) : (A ⧸ f.to_ring_hom.ker) →ₐ[R₁] B :=
alg_hom.mk' f.to_ring_hom.ker_lift (λ _ _, ker_lift.map_smul f _ _)

@[simp]
lemma ker_lift_alg_mk (f : A →ₐ[R₁] B) (a : A) :
  ker_lift_alg f (quotient.mk f.to_ring_hom.ker a) = f a := rfl

@[simp]
lemma ker_lift_alg_to_ring_hom (f : A →ₐ[R₁] B) :
  (ker_lift_alg f).to_ring_hom = ring_hom.ker_lift f := rfl

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
lemma ker_lift_alg_injective (f : A →ₐ[R₁] B) : function.injective (ker_lift_alg f) :=
ring_hom.ker_lift_injective f

/-- The **first isomorphism** theorem for algebras, computable version. -/
def quotient_ker_alg_equiv_of_right_inverse
  {f : A →ₐ[R₁] B} {g : B → A} (hf : function.right_inverse g f) :
  (A ⧸ f.to_ring_hom.ker) ≃ₐ[R₁] B :=
{ ..ring_hom.quotient_ker_equiv_of_right_inverse (λ x, show f.to_ring_hom (g x) = x, from hf x),
  ..ker_lift_alg f}

@[simp]
lemma quotient_ker_alg_equiv_of_right_inverse.apply {f : A →ₐ[R₁] B} {g : B → A}
  (hf : function.right_inverse g f) (x : A ⧸ f.to_ring_hom.ker) :
  quotient_ker_alg_equiv_of_right_inverse hf x = ker_lift_alg f x := rfl

@[simp]
lemma quotient_ker_alg_equiv_of_right_inverse_symm.apply {f : A →ₐ[R₁] B} {g : B → A}
  (hf : function.right_inverse g f) (x : B) :
  (quotient_ker_alg_equiv_of_right_inverse hf).symm x = quotient.mkₐ R₁ f.to_ring_hom.ker (g x) :=
  rfl

/-- The **first isomorphism theorem** for algebras. -/
noncomputable def quotient_ker_alg_equiv_of_surjective
  {f : A →ₐ[R₁] B} (hf : function.surjective f) : (A ⧸ f.to_ring_hom.ker) ≃ₐ[R₁] B :=
quotient_ker_alg_equiv_of_right_inverse (classical.some_spec hf.has_right_inverse)

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotient_map {I : ideal R} (J : ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) :
  R ⧸ I →+* S ⧸ J :=
(quotient.lift I ((quotient.mk J).comp f) (λ _ ha,
  by simpa [function.comp_app, ring_hom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha))

@[simp]
lemma quotient_map_mk {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  {x : R} : quotient_map I f H (quotient.mk J x) = quotient.mk I (f x) :=
quotient.lift_mk J _ _

@[simp]
lemma quotient_map_algebra_map {J : ideal A} {I : ideal S} {f : A →+* S} {H : J ≤ I.comap f}
  {x : R₁} :
  quotient_map I f H (algebra_map R₁ (A ⧸ J) x) = quotient.mk I (f (algebra_map _ _ x)) :=
quotient.lift_mk J _ _

lemma quotient_map_comp_mk {J : ideal R} {I : ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
  (quotient_map I f H).comp (quotient.mk J) = (quotient.mk I).comp f :=
ring_hom.ext (λ x, by simp only [function.comp_app, ring_hom.coe_comp, ideal.quotient_map_mk])

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotient_equiv (I : ideal R) (J : ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
  R ⧸ I ≃+* S ⧸ J :=
{ inv_fun := quotient_map I ↑f.symm (by {rw hIJ, exact le_of_eq (map_comap_of_equiv I f)}),
  left_inv := by {rintro ⟨r⟩, simp },
  right_inv := by {rintro ⟨s⟩, simp },
  ..quotient_map J ↑f (by {rw hIJ, exact @le_comap_map _ S _ _ _ _}) }

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
lemma quotient_map_injective' {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  (h : I.comap f ≤ J) : function.injective (quotient_map I f H) :=
begin
  refine (quotient_map I f H).injective_iff.2 (λ a ha, _),
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha,
  exact (quotient.eq_zero_iff_mem).mpr (h ha),
end

/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
lemma quotient_map_injective {I : ideal S} {f : R →+* S} :
  function.injective (quotient_map I f le_rfl) :=
quotient_map_injective' le_rfl

lemma quotient_map_surjective {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  (hf : function.surjective f) : function.surjective (quotient_map I f H) :=
λ x, let ⟨x, hx⟩ := quotient.mk_surjective x in
  let ⟨y, hy⟩ := hf x in ⟨(quotient.mk J) y, by simp [hx, hy]⟩

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
lemma comp_quotient_map_eq_of_comp_eq {R' S' : Type*} [comm_ring R'] [comm_ring S']
  {f : R →+* S} {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f)
  (I : ideal S') : (quotient_map I g' le_rfl).comp (quotient_map (I.comap g') f le_rfl) =
    (quotient_map I f' le_rfl).comp (quotient_map (I.comap f') g
      (le_of_eq (trans (comap_comap f g') (hfg ▸ (comap_comap g f'))))) :=
begin
  refine ring_hom.ext (λ a, _),
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  simp only [ring_hom.comp_apply, quotient_map_mk],
  exact congr_arg (quotient.mk I) (trans (g'.comp_apply f r).symm (hfg ▸ (f'.comp_apply g r))),
end

/-- The algebra hom `A/I →+* B/J` induced by an algebra hom `f : A →ₐ[R₁] B` with `I ≤ f⁻¹(J)`. -/
def quotient_mapₐ {I : ideal A} (J : ideal B) (f : A →ₐ[R₁] B) (hIJ : I ≤ J.comap f) :
  A ⧸ I →ₐ[R₁] B ⧸ J :=
{ commutes' := λ r, by simp,
  ..quotient_map J ↑f hIJ }

@[simp]
lemma quotient_map_mkₐ {I : ideal A} (J : ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f)
  {x : A} : quotient_mapₐ J f H (quotient.mk I x) = quotient.mkₐ R₁ J (f x) := rfl

lemma quotient_map_comp_mkₐ {I : ideal A} (J : ideal B) (f : A →ₐ[R₁] B) (H : I ≤ J.comap f) :
  (quotient_mapₐ J f H).comp (quotient.mkₐ R₁ I) = (quotient.mkₐ R₁ J).comp f :=
alg_hom.ext (λ x, by simp only [quotient_map_mkₐ, quotient.mkₐ_eq_mk, alg_hom.comp_apply])

/-- The algebra equiv `A/I ≃ₐ[R] B/J` induced by an algebra equiv `f : A ≃ₐ[R] B`,
where`J = f(I)`. -/
def quotient_equiv_alg (I : ideal A) (J : ideal B) (f : A ≃ₐ[R₁] B)
  (hIJ : J = I.map (f : A →+* B)) :
  (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
{ commutes' := λ r, by simp,
  ..quotient_equiv I J (f : A ≃+* B) hIJ }

@[priority 100]
instance quotient_algebra {I : ideal A} [algebra R A] :
  algebra (R ⧸ I.comap (algebra_map R A)) (A ⧸ I) :=
(quotient_map I (algebra_map R A) (le_of_eq rfl)).to_algebra

lemma algebra_map_quotient_injective {I : ideal A} [algebra R A]:
  function.injective (algebra_map (R ⧸ I.comap (algebra_map R A)) (A ⧸ I)) :=
begin
  rintros ⟨a⟩ ⟨b⟩ hab,
  replace hab := quotient.eq.mp hab,
  rw ← ring_hom.map_sub at hab,
  exact quotient.eq.mpr hab
end

end quotient_algebra

end comm_ring

end ideal

namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_semiring R] [add_comm_monoid M] [module R M]

-- TODO: show `[algebra R A] : algebra (ideal R) A` too

instance module_submodule : module (ideal R) (submodule R M) :=
{ smul_add := smul_sup,
  add_smul := sup_smul,
  mul_smul := submodule.smul_assoc,
  one_smul := by simp,
  zero_smul := bot_smul,
  smul_zero := smul_bot }

end submodule

namespace ring_hom
variables {A B C : Type*} [ring A] [ring B] [ring C]
variables (f : A →+* B) (f_inv : B → A)

/-- Auxiliary definition used to define `lift_of_right_inverse` -/
def lift_of_right_inverse_aux
  (hf : function.right_inverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker) :
  B →+* C :=
{ to_fun := λ b, g (f_inv b),
  map_one' :=
  begin
    rw [← g.map_one, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker],
    apply hg,
    rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_one],
    exact hf 1
  end,
  map_mul' :=
  begin
    intros x y,
    rw [← g.map_mul, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker],
    apply hg,
    rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_mul],
    simp only [hf _],
  end,
  .. add_monoid_hom.lift_of_right_inverse f.to_add_monoid_hom f_inv hf ⟨g.to_add_monoid_hom, hg⟩ }

@[simp] lemma lift_of_right_inverse_aux_comp_apply
  (hf : function.right_inverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker) (a : A) :
  (f.lift_of_right_inverse_aux f_inv hf g hg) (f a) = g a :=
f.to_add_monoid_hom.lift_of_right_inverse_comp_apply f_inv hf ⟨g.to_add_monoid_hom, hg⟩ a

/-- `lift_of_right_inverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`ring_hom.lift_of_right_inverse_comp`),
* where `f : A →+* B` is has a right_inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `ring_hom.eq_lift_of_right_inverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def lift_of_right_inverse
  (hf : function.right_inverse f_inv f) : {g : A →+* C // f.ker ≤ g.ker} ≃ (B →+* C) :=
{ to_fun := λ g, f.lift_of_right_inverse_aux f_inv hf g.1 g.2,
  inv_fun := λ φ, ⟨φ.comp f, λ x hx, (mem_ker _).mpr $ by simp [(mem_ker _).mp hx]⟩,
  left_inv := λ g, by
  { ext,
    simp only [comp_apply, lift_of_right_inverse_aux_comp_apply, subtype.coe_mk,
      subtype.val_eq_coe], },
  right_inv := λ φ, by
  { ext b,
    simp [lift_of_right_inverse_aux, hf b], } }

/-- A non-computable version of `ring_hom.lift_of_right_inverse` for when no computable right
inverse is available, that uses `function.surj_inv`. -/
@[simp]
noncomputable abbreviation lift_of_surjective
  (hf : function.surjective f) : {g : A →+* C // f.ker ≤ g.ker} ≃ (B →+* C) :=
f.lift_of_right_inverse (function.surj_inv hf) (function.right_inverse_surj_inv hf)

lemma lift_of_right_inverse_comp_apply
  (hf : function.right_inverse f_inv f) (g : {g : A →+* C // f.ker ≤ g.ker}) (x : A) :
  (f.lift_of_right_inverse f_inv hf g) (f x) = g x :=
f.lift_of_right_inverse_aux_comp_apply f_inv hf g.1 g.2 x

lemma lift_of_right_inverse_comp (hf : function.right_inverse f_inv f)
  (g : {g : A →+* C // f.ker ≤ g.ker}) :
  (f.lift_of_right_inverse f_inv hf g).comp f = g :=
ring_hom.ext $ f.lift_of_right_inverse_comp_apply f_inv hf g

lemma eq_lift_of_right_inverse (hf : function.right_inverse f_inv f) (g : A →+* C)
  (hg : f.ker ≤ g.ker) (h : B →+* C) (hh : h.comp f = g) :
  h = (f.lift_of_right_inverse f_inv hf ⟨g, hg⟩) :=
begin
  simp_rw ←hh,
  exact ((f.lift_of_right_inverse f_inv hf).apply_symm_apply _).symm,
end

end ring_hom

namespace double_quot
open ideal
variables {R : Type u} [comm_ring R] (I J : ideal R)

/-- The obvious ring hom `R/I → R/(I ⊔ J)` -/
def quot_left_to_quot_sup : R ⧸ I →+* R ⧸ (I ⊔ J) :=
ideal.quotient.factor I (I ⊔ J) le_sup_left

/-- The kernel of `quot_left_to_quot_sup` -/
lemma ker_quot_left_to_quot_sup :
  (quot_left_to_quot_sup I J).ker = J.map (ideal.quotient.mk I) :=
by simp only [mk_ker, sup_idem, sup_comm, quot_left_to_quot_sup, quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective I^.quotient.mk quotient.mk_surjective, ← sup_assoc]

/-- The ring homomorphism `(R/I)/J' -> R/(I ⊔ J)` induced by `quot_left_to_quot_sup` where `J'`
  is the image of `J` in `R/I`-/
def quot_quot_to_quot_sup : (R ⧸ I) ⧸ J.map (ideal.quotient.mk I) →+* R ⧸ I ⊔ J :=
ideal.quotient.lift (ideal.map (ideal.quotient.mk I) J) (quot_left_to_quot_sup I J)
  (ker_quot_left_to_quot_sup I J).symm.le

/-- The composite of the maps `R → (R/I)` and `(R/I) → (R/I)/J'` -/
def quot_quot_mk : R →+* ((R ⧸ I) ⧸ J.map I^.quotient.mk) :=
((J.map I^.quotient.mk)^.quotient.mk).comp I^.quotient.mk

/-- The kernel of `quot_quot_mk` -/
lemma ker_quot_quot_mk : (quot_quot_mk I J).ker = I ⊔ J :=
by rw [ring_hom.ker_eq_comap_bot, quot_quot_mk, ← comap_comap, ← ring_hom.ker, mk_ker,
  comap_map_of_surjective (ideal.quotient.mk I) (quotient.mk_surjective), ← ring_hom.ker, mk_ker,
  sup_comm]

/-- The ring homomorphism `R/(I ⊔ J) → (R/I)/J' `induced by `quot_quot_mk` -/
def lift_sup_quot_quot_mk (I J : ideal R) :
  R ⧸ (I ⊔ J) →+* (R ⧸ I) ⧸ J.map (ideal.quotient.mk I) :=
ideal.quotient.lift (I ⊔ J) (quot_quot_mk I J) (ker_quot_quot_mk I J).symm.le

/-- `quot_quot_to_quot_add` and `lift_sup_double_qot_mk` are inverse isomorphisms -/
def quot_quot_equiv_quot_sup : (R ⧸ I) ⧸ J.map (ideal.quotient.mk I) ≃+* R ⧸ I ⊔ J :=
ring_equiv.of_hom_inv (quot_quot_to_quot_sup I J) (lift_sup_quot_quot_mk I J)
  (by { ext z, refl }) (by { ext z, refl })

@[simp]
lemma quot_quot_equiv_quot_sup_quot_quot_mk (x : R) :
  quot_quot_equiv_quot_sup I J (quot_quot_mk I J x) = ideal.quotient.mk (I ⊔ J) x :=
rfl

@[simp]
lemma quot_quot_equiv_quot_sup_symm_quot_quot_mk (x : R) :
  (quot_quot_equiv_quot_sup I J).symm (ideal.quotient.mk (I ⊔ J) x) = quot_quot_mk I J x :=
rfl

/-- The obvious isomorphism `(R/I)/J' → (R/J)/I' `   -/
def quot_quot_equiv_comm :
  (R ⧸ I) ⧸ J.map I^.quotient.mk ≃+* (R ⧸ J) ⧸ I.map J^.quotient.mk :=
((quot_quot_equiv_quot_sup I J).trans (quot_equiv_of_eq sup_comm)).trans
  (quot_quot_equiv_quot_sup J I).symm

@[simp]
lemma quot_quot_equiv_comm_quot_quot_mk (x : R) :
  quot_quot_equiv_comm I J (quot_quot_mk I J x) = quot_quot_mk J I x :=
rfl

@[simp]
lemma quot_quot_equiv_comm_comp_quot_quot_mk :
  ring_hom.comp ↑(quot_quot_equiv_comm I J) (quot_quot_mk I J) = quot_quot_mk J I :=
ring_hom.ext $ quot_quot_equiv_comm_quot_quot_mk I J

@[simp]
lemma quot_quot_equiv_comm_symm :
  (quot_quot_equiv_comm I J).symm = quot_quot_equiv_comm J I :=
rfl

end double_quot
