/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
import group_theory.submonoid.operations
import algebra.big_operators.basic
import algebra.free_monoid

/-!
# Submonoids: membership criteria

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;
* `pow_mem`, `nsmul_mem`: if `x ∈ S` where `S` is a multiplicative (resp., additive) submonoid and
  `n` is a natural number, then `x^n` (resp., `n • x`) belongs to `S`;
* `mem_supr_of_directed`, `coe_supr_of_directed`, `mem_Sup_of_directed_on`,
  `coe_Sup_of_directed_on`: the supremum of a directed collection of submonoid is their union.
* `sup_eq_range`, `mem_sup`: supremum of two submonoids `S`, `T` of a commutative monoid is the set
  of products;
* `closure_singleton_eq`, `mem_closure_singleton`: the multiplicative (resp., additive) closure
  of `{x}` consists of powers (resp., natural multiples) of `x`.

## Tags
submonoid, submonoids
-/

open_locale big_operators

variables {M : Type*}
variables {A : Type*}

namespace submonoid

section assoc
variables [monoid M] (S : submonoid M)

@[simp, norm_cast, to_additive coe_nsmul] theorem coe_pow (x : S) (n : ℕ) :
  ↑(x ^ n) = (x ^ n : M) :=
S.subtype.map_pow x n

@[simp, norm_cast, to_additive] theorem coe_list_prod (l : list S) :
  (l.prod : M) = (l.map coe).prod :=
S.subtype.map_list_prod l

@[simp, norm_cast, to_additive] theorem coe_multiset_prod {M} [comm_monoid M] (S : submonoid M)
  (m : multiset S) : (m.prod : M) = (m.map coe).prod :=
S.subtype.map_multiset_prod m

@[simp, norm_cast, to_additive] theorem coe_finset_prod {ι M} [comm_monoid M] (S : submonoid M)
  (f : ι → S) (s : finset ι) :
  ↑(∏ i in s, f i) = (∏ i in s, f i : M) :=
S.subtype.map_prod f s

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive "Sum of a list of elements in an `add_submonoid` is in the `add_submonoid`."]
lemma list_prod_mem {l : list M} (hl : ∀ x ∈ l, x ∈ S) : l.prod ∈ S :=
by { lift l to list S using hl, rw ← coe_list_prod, exact l.prod.coe_prop }

/-- Product of a multiset of elements in a submonoid of a `comm_monoid` is in the submonoid. -/
@[to_additive "Sum of a multiset of elements in an `add_submonoid` of an `add_comm_monoid` is
in the `add_submonoid`."]
lemma multiset_prod_mem {M} [comm_monoid M] (S : submonoid M) (m : multiset M)
  (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S :=
by { lift m to multiset S using hm, rw ← coe_multiset_prod, exact m.prod.coe_prop }

/-- Product of elements of a submonoid of a `comm_monoid` indexed by a `finset` is in the
    submonoid. -/
@[to_additive "Sum of elements in an `add_submonoid` of an `add_comm_monoid` indexed by a `finset`
is in the `add_submonoid`."]
lemma prod_mem {M : Type*} [comm_monoid M] (S : submonoid M)
  {ι : Type*} {t : finset ι} {f : ι → M} (h : ∀c ∈ t, f c ∈ S) :
  ∏ c in t, f c ∈ S :=
S.multiset_prod_mem (t.1.map f) $ λ x hx, let ⟨i, hi, hix⟩ := multiset.mem_map.1 hx in hix ▸ h i hi

@[to_additive nsmul_mem] lemma pow_mem {x : M} (hx : x ∈ S) (n : ℕ) : x ^ n ∈ S :=
by simpa only [coe_pow] using ((⟨x, hx⟩ : S) ^ n).coe_prop

end assoc

section non_assoc
variables [mul_one_class M] (S : submonoid M)

open set

@[to_additive]
lemma mem_supr_of_directed {ι} [hι : nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S)
  {x : M} :
  x ∈ (⨆ i, S i) ↔ ∃ i, x ∈ S i :=
begin
  refine ⟨_, λ ⟨i, hi⟩, (set_like.le_def.1 $ le_supr S i) hi⟩,
  suffices : x ∈ closure (⋃ i, (S i : set M)) → ∃ i, x ∈ S i,
    by simpa only [closure_Union, closure_eq (S _)] using this,
  refine (λ hx, closure_induction hx (λ _, mem_Union.1) _ _),
  { exact hι.elim (λ i, ⟨i, (S i).one_mem⟩) },
  { rintros x y ⟨i, hi⟩ ⟨j, hj⟩,
    rcases hS i j with ⟨k, hki, hkj⟩,
    exact ⟨k, (S k).mul_mem (hki hi) (hkj hj)⟩ }
end

@[to_additive]
lemma coe_supr_of_directed {ι} [nonempty ι] {S : ι → submonoid M} (hS : directed (≤) S) :
  ((⨆ i, S i : submonoid M) : set M) = ⋃ i, ↑(S i) :=
set.ext $ λ x, by simp [mem_supr_of_directed hS]

@[to_additive]
lemma mem_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty)
  (hS : directed_on (≤) S) {x : M} :
  x ∈ Sup S ↔ ∃ s ∈ S, x ∈ s :=
begin
  haveI : nonempty S := Sne.to_subtype,
  simp only [Sup_eq_supr', mem_supr_of_directed hS.directed_coe, set_coe.exists, subtype.coe_mk]
end

@[to_additive]
lemma coe_Sup_of_directed_on {S : set (submonoid M)} (Sne : S.nonempty) (hS : directed_on (≤) S) :
  (↑(Sup S) : set M) = ⋃ s ∈ S, ↑s :=
set.ext $ λ x, by simp [mem_Sup_of_directed_on Sne hS]

@[to_additive]
lemma mem_sup_left {S T : submonoid M} : ∀ {x : M}, x ∈ S → x ∈ S ⊔ T :=
show S ≤ S ⊔ T, from le_sup_left

@[to_additive]
lemma mem_sup_right {S T : submonoid M} : ∀ {x : M}, x ∈ T → x ∈ S ⊔ T :=
show T ≤ S ⊔ T, from le_sup_right

@[to_additive]
lemma mul_mem_sup {S T : submonoid M} {x y : M} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
(S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)

@[to_additive]
lemma mem_supr_of_mem {ι : Sort*} {S : ι → submonoid M} (i : ι) :
  ∀ {x : M}, x ∈ S i → x ∈ supr S :=
show S i ≤ supr S, from le_supr _ _

@[to_additive]
lemma mem_Sup_of_mem {S : set (submonoid M)} {s : submonoid M}
  (hs : s ∈ S) : ∀ {x : M}, x ∈ s → x ∈ Sup S :=
show s ≤ Sup S, from le_Sup hs

/-- An induction principle for elements of `⨆ i, S i`.
If `C` holds for `1` and all elements of `S i` for all `i`, and is preserved under multiplication,
then it holds for all elements of the supremum of `S`. -/
@[elab_as_eliminator, to_additive /-" An induction principle for elements of `⨆ i, S i`.
If `C` holds for `0` and all elements of `S i` for all `i`, and is preserved under addition,
then it holds for all elements of the supremum of `S`. "-/]
lemma supr_induction {ι : Sort*} (S : ι → submonoid M) {C : M → Prop} {x : M} (hx : x ∈ ⨆ i, S i)
  (hp : ∀ i (x ∈ S i), C x)
  (h1 : C 1)
  (hmul : ∀ x y, C x → C y → C (x * y)) : C x :=
begin
  rw supr_eq_closure at hx,
  refine closure_induction hx (λ x hx, _) h1 hmul,
  obtain ⟨i, hi⟩ := set.mem_Union.mp hx,
  exact hp _ _ hi,
end

/-- A dependent version of `submonoid.supr_induction`. -/
@[elab_as_eliminator, to_additive /-"A dependent version of `add_submonoid.supr_induction`. "-/]
lemma supr_induction' {ι : Sort*} (S : ι → submonoid M) {C : Π x, (x ∈ ⨆ i, S i) → Prop}
  (hp : ∀ i (x ∈ S i), C x (mem_supr_of_mem i ‹_›))
  (h1 : C 1 (one_mem _))
  (hmul : ∀ x y hx hy, C x hx → C y hy → C (x * y) (mul_mem _ ‹_› ‹_›))
  {x : M} (hx : x ∈ ⨆ i, S i) : C x hx :=
begin
  refine exists.elim _ (λ (hx : x ∈ ⨆ i, S i) (hc : C x hx), hc),
  refine supr_induction S hx (λ i x hx, _) _ (λ x y, _),
  { exact ⟨_, hp _ _ hx⟩ },
  { exact ⟨_, h1⟩ },
  { rintro ⟨_, Cx⟩ ⟨_, Cy⟩,
    refine ⟨_, hmul _ _ _ _ Cx Cy⟩ },
end

end non_assoc

end submonoid

namespace free_monoid

variables {α : Type*}

open submonoid

@[to_additive]
theorem closure_range_of : closure (set.range $ @of α) = ⊤ :=
eq_top_iff.2 $ λ x hx, free_monoid.rec_on x (one_mem _) $ λ x xs hxs,
  mul_mem _ (subset_closure $ set.mem_range_self _) hxs

end free_monoid

namespace submonoid

variables [monoid M]

open monoid_hom

lemma closure_singleton_eq (x : M) : closure ({x} : set M) = (powers_hom M x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨multiplicative.of_add 1, pow_one x⟩) $
  λ x ⟨n, hn⟩, hn ▸ pow_mem _ (subset_closure $ set.mem_singleton _) _

/-- The submonoid generated by an element of a monoid equals the set of natural number powers of
    the element. -/
lemma mem_closure_singleton {x y : M} : y ∈ closure ({x} : set M) ↔ ∃ n:ℕ, x^n=y :=
by rw [closure_singleton_eq, mem_mrange]; refl

lemma mem_closure_singleton_self {y : M} : y ∈ closure ({y} : set M) :=
mem_closure_singleton.2 ⟨1, pow_one y⟩

lemma closure_singleton_one : closure ({1} : set M) = ⊥ :=
by simp [eq_bot_iff_forall, mem_closure_singleton]

@[to_additive]
lemma closure_eq_mrange (s : set M) : closure s = (free_monoid.lift (coe : s → M)).mrange :=
by rw [mrange_eq_map, ← free_monoid.closure_range_of, map_mclosure, ← set.range_comp,
  free_monoid.lift_comp_of, subtype.range_coe]

@[to_additive]
lemma exists_list_of_mem_closure {s : set M} {x : M} (hx : x ∈ closure s) :
  ∃ (l : list M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  rw [closure_eq_mrange, mem_mrange] at hx,
  rcases hx with ⟨l, hx⟩,
  exact ⟨list.map coe l, λ y hy, let ⟨z, hz, hy⟩ := list.mem_map.1 hy in hy ▸ z.2, hx⟩
end

@[to_additive]
lemma exists_multiset_of_mem_closure {M : Type*} [comm_monoid M] {s : set M}
  {x : M} (hx : x ∈ closure s) : ∃ (l : multiset M) (hl : ∀ y ∈ l, y ∈ s), l.prod = x :=
begin
  obtain ⟨l, h1, h2⟩ := exists_list_of_mem_closure hx,
  exact ⟨l, h1, (multiset.coe_prod l).trans h2⟩,
end

/-- The submonoid generated by an element. -/
def powers (n : M) : submonoid M :=
submonoid.copy (powers_hom M n).mrange (set.range ((^) n : ℕ → M)) $
set.ext (λ n, exists_congr $ λ i, by simp; refl)

@[simp] lemma mem_powers (n : M) : n ∈ powers n := ⟨1, pow_one _⟩

lemma mem_powers_iff (x z : M) : x ∈ powers z ↔ ∃ n : ℕ, z ^ n = x := iff.rfl

lemma powers_eq_closure (n : M) : powers n = closure {n} :=
by { ext, exact mem_closure_singleton.symm }

lemma powers_subset {n : M} {P : submonoid M} (h : n ∈ P) : powers n ≤ P :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := P.pow_mem h i end

/-- Exponentiation map from natural numbers to powers. -/
@[simps] def pow (n : M) (m : ℕ) : powers n :=
(powers_hom M n).mrange_restrict (multiplicative.of_add m)

lemma pow_apply (n : M) (m : ℕ) : submonoid.pow n m = ⟨n ^ m, m, rfl⟩ := rfl

/-- Logarithms from powers to natural numbers. -/
def log [decidable_eq M] {n : M} (p : powers n) : ℕ :=
nat.find $ (mem_powers_iff p.val n).mp p.prop

@[simp] theorem pow_log_eq_self [decidable_eq M] {n : M} (p : powers n) : pow n (log p) = p :=
subtype.ext $ nat.find_spec p.prop

lemma pow_right_injective_iff_pow_injective {n : M} :
  function.injective (λ m : ℕ, n ^ m) ↔ function.injective (pow n) :=
subtype.coe_injective.of_comp_iff (pow n)

@[simp] theorem log_pow_eq_self [decidable_eq M] {n : M} (h : function.injective (λ m : ℕ, n ^ m))
  (m : ℕ) : log (pow n m) = m :=
pow_right_injective_iff_pow_injective.mp h $ pow_log_eq_self _

/-- The exponentiation map is an isomorphism from the additive monoid on natural numbers to powers
when it is injective. The inverse is given by the logarithms. -/
@[simps]
def pow_log_equiv [decidable_eq M] {n : M} (h : function.injective (λ m : ℕ, n ^ m)) :
  multiplicative ℕ ≃* powers n :=
{ to_fun := λ m, pow n m.to_add,
  inv_fun := λ m, multiplicative.of_add (log m),
  left_inv := log_pow_eq_self h,
  right_inv := pow_log_eq_self,
  map_mul' := λ _ _, by { simp only [pow, map_mul, of_add_add, to_add_mul] } }

lemma log_mul [decidable_eq M] {n : M} (h : function.injective (λ m : ℕ, n ^ m))
  (x y : powers (n : M)) : log (x * y) = log x + log y := (pow_log_equiv h).symm.map_mul x y

theorem log_pow_int_eq_self {x : ℤ} (h : 1 < x.nat_abs) (m : ℕ) : log (pow x m) = m :=
(pow_log_equiv (int.pow_right_injective h)).symm_apply_apply _

@[simp] lemma map_powers {N : Type*} [monoid N] (f : M →* N) (m : M) :
  (powers m).map f = powers (f m) :=
by simp only [powers_eq_closure, f.map_mclosure, set.image_singleton]

end submonoid

namespace submonoid

variables {N : Type*} [comm_monoid N]

open monoid_hom

@[to_additive]
lemma sup_eq_range (s t : submonoid N) : s ⊔ t = (s.subtype.coprod t.subtype).mrange :=
by rw [mrange_eq_map, ← mrange_inl_sup_mrange_inr, map_sup, map_mrange, coprod_comp_inl,
  map_mrange, coprod_comp_inr, range_subtype, range_subtype]

@[to_additive]
lemma mem_sup {s t : submonoid N} {x : N} :
  x ∈ s ⊔ t ↔ ∃ (y ∈ s) (z ∈ t), y * z = x :=
by simp only [sup_eq_range, mem_mrange, coprod_apply, prod.exists, set_like.exists,
  coe_subtype, subtype.coe_mk]

end submonoid

namespace add_submonoid

variables [add_monoid A]

open set

lemma closure_singleton_eq (x : A) : closure ({x} : set A) = (multiples_hom A x).mrange :=
closure_eq_of_le (set.singleton_subset_iff.2 ⟨1, one_nsmul x⟩) $
  λ x ⟨n, hn⟩, hn ▸ nsmul_mem _ (subset_closure $ set.mem_singleton _) _

/-- The `add_submonoid` generated by an element of an `add_monoid` equals the set of
natural number multiples of the element. -/
lemma mem_closure_singleton {x y : A} :
  y ∈ closure ({x} : set A) ↔ ∃ n:ℕ, n • x = y :=
by rw [closure_singleton_eq, add_monoid_hom.mem_mrange]; refl

lemma closure_singleton_zero : closure ({0} : set A) = ⊥ :=
by simp [eq_bot_iff_forall, mem_closure_singleton, nsmul_zero]

/-- The additive submonoid generated by an element. -/
def multiples (x : A) : add_submonoid A :=
add_submonoid.copy (multiples_hom A x).mrange (set.range (λ i, i • x : ℕ → A)) $
set.ext (λ n, exists_congr $ λ i, by simp; refl)

@[simp] lemma mem_multiples (x : A) : x ∈ multiples x := ⟨1, one_nsmul _⟩

lemma mem_multiples_iff (x z : A) : x ∈ multiples z ↔ ∃ n : ℕ, n • z = x := iff.rfl

lemma multiples_eq_closure (x : A) : multiples x = closure {x} :=
by { ext, exact mem_closure_singleton.symm }

lemma multiples_subset {x : A} {P : add_submonoid A} (h : x ∈ P) : multiples x ≤ P :=
λ x hx, match x, hx with _, ⟨i, rfl⟩ := P.nsmul_mem h i end

attribute [to_additive add_submonoid.multiples] submonoid.powers
attribute [to_additive add_submonoid.mem_multiples] submonoid.mem_powers
attribute [to_additive add_submonoid.mem_multiples_iff] submonoid.mem_powers_iff
attribute [to_additive add_submonoid.multiples_eq_closure] submonoid.powers_eq_closure
attribute [to_additive add_submonoid.multiples_subset] submonoid.powers_subset

end add_submonoid

/-! Lemmas about additive closures of `submonoid`. -/
namespace submonoid

variables {R : Type*} [non_assoc_semiring R] (S : submonoid R) {a b : R}

/-- The product of an element of the additive closure of a multiplicative submonoid `M`
and an element of `M` is contained in the additive closure of `M`. -/
lemma mul_right_mem_add_closure
  (ha : a ∈ add_submonoid.closure (S : set R)) (hb : b ∈ S) :
  a * b ∈ add_submonoid.closure (S : set R) :=
begin
  revert b,
  refine add_submonoid.closure_induction ha _ _ _; clear ha a,
  { exact λ r hr b hb, add_submonoid.mem_closure.mpr (λ y hy, hy (S.mul_mem hr hb)) },
  { exact λ b hb, by simp only [zero_mul, (add_submonoid.closure (S : set R)).zero_mem] },
  { simp_rw add_mul,
    exact λ r s hr hs b hb, (add_submonoid.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

/-- The product of two elements of the additive closure of a submonoid `M` is an element of the
additive closure of `M`. -/
lemma mul_mem_add_closure
  (ha : a ∈ add_submonoid.closure (S : set R)) (hb : b ∈ add_submonoid.closure (S : set R)) :
  a * b ∈ add_submonoid.closure (S : set R) :=
begin
  revert a,
  refine add_submonoid.closure_induction hb _ _ _; clear hb b,
  { exact λ r hr b hb, S.mul_right_mem_add_closure hb hr },
  { exact λ b hb, by simp only [mul_zero, (add_submonoid.closure (S : set R)).zero_mem] },
  { simp_rw mul_add,
    exact λ r s hr hs b hb, (add_submonoid.closure (S : set R)).add_mem (hr hb) (hs hb) }
end

/-- The product of an element of `S` and an element of the additive closure of a multiplicative
submonoid `S` is contained in the additive closure of `S`. -/
lemma mul_left_mem_add_closure (ha : a ∈ S) (hb : b ∈ add_submonoid.closure (S : set R)) :
  a * b ∈ add_submonoid.closure (S : set R) :=
S.mul_mem_add_closure (add_submonoid.mem_closure.mpr (λ sT hT, hT ha)) hb

end submonoid

section mul_add

lemma of_mul_image_powers_eq_multiples_of_mul [monoid M] {x : M} :
  additive.of_mul '' ((submonoid.powers x) : set M) = add_submonoid.multiples (additive.of_mul x) :=
begin
  ext,
  split,
  { rintros ⟨y, ⟨n, hy1⟩, hy2⟩,
    use n,
    simpa [← of_mul_pow, hy1] },
  { rintros ⟨n, hn⟩,
    refine ⟨x ^ n, ⟨n, rfl⟩, _⟩,
    rwa of_mul_pow }
end

lemma of_add_image_multiples_eq_powers_of_add [add_monoid A] {x : A} :
  multiplicative.of_add '' ((add_submonoid.multiples x) : set A) =
  submonoid.powers (multiplicative.of_add x) :=
begin
  symmetry,
  rw equiv.eq_image_iff_symm_image_eq,
  exact of_mul_image_powers_eq_multiples_of_mul,
end

end mul_add
