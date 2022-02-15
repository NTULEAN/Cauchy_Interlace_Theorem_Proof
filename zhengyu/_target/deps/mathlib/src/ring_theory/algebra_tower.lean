/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.invertible
import ring_theory.adjoin.fg
import linear_algebra.basis
import algebra.algebra.tower
import algebra.algebra.restrict_scalars

/-!
# Towers of algebras

We set up the basic theory of algebra towers.
An algebra tower A/S/R is expressed by having instances of `algebra A S`,
`algebra R S`, `algebra R A` and `is_scalar_tower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

In `field_theory/tower.lean` we use this to prove the tower law for finite extensions,
that if `R` and `S` are both fields, then `[A:R] = [A:S] [S:A]`.

In this file we prepare the main lemma:
if `{bi | i ∈ I}` is an `R`-basis of `S` and `{cj | j ∈ J}` is a `S`-basis
of `A`, then `{bi cj | i ∈ I, j ∈ J}` is an `R`-basis of `A`. This statement does not require the
base rings to be a field, so we also generalize the lemma to rings in this file.
-/

open_locale pointwise
universes u v w u₁

variables (R : Type u) (S : Type v) (A : Type w) (B : Type u₁)

namespace is_scalar_tower

section semiring
variables [comm_semiring R] [comm_semiring S] [semiring A] [semiring B]
variables [algebra R S] [algebra S A] [algebra S B] [algebra R A] [algebra R B]
variables [is_scalar_tower R S A] [is_scalar_tower R S B]

variables (R S A B)

/-- Suppose that `R -> S -> A` is a tower of algebras.
If an element `r : R` is invertible in `S`, then it is invertible in `A`. -/
def invertible.algebra_tower (r : R) [invertible (algebra_map R S r)] :
  invertible (algebra_map R A r) :=
invertible.copy (invertible.map (algebra_map S A : S →* A) (algebra_map R S r)) (algebra_map R A r)
  (by rw [ring_hom.coe_monoid_hom, is_scalar_tower.algebra_map_apply R S A])

/-- A natural number that is invertible when coerced to `R` is also invertible
when coerced to any `R`-algebra. -/
def invertible_algebra_coe_nat (n : ℕ) [inv : invertible (n : R)] :
  invertible (n : A) :=
by { haveI : invertible (algebra_map ℕ R n) := inv, exact invertible.algebra_tower ℕ R A n }

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [comm_semiring B]
variables [algebra R A] [algebra A B] [algebra R B] [is_scalar_tower R A B]

end comm_semiring

end is_scalar_tower

namespace algebra

theorem adjoin_algebra_map' {R : Type u} {S : Type v} {A : Type w}
  [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] (s : set S) :
  adjoin R (algebra_map S (restrict_scalars R S A) '' s) = (adjoin R s).map
  ((algebra.of_id S (restrict_scalars R S A)).restrict_scalars R) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

theorem adjoin_algebra_map (R : Type u) (S : Type v) (A : Type w)
  [comm_semiring R] [comm_semiring S] [semiring A] [algebra R S] [algebra S A] [algebra R A]
  [is_scalar_tower R S A] (s : set S) :
  adjoin R (algebra_map S A '' s) =
    subalgebra.map (adjoin R s) (is_scalar_tower.to_alg_hom R S A) :=
le_antisymm (adjoin_le $ set.image_subset_iff.2 $ λ y hy, ⟨y, subset_adjoin hy, rfl⟩)
  (subalgebra.map_le.2 $ adjoin_le $ λ y hy, subset_adjoin ⟨y, hy, rfl⟩)

lemma adjoin_restrict_scalars (C D E : Type*) [comm_semiring C] [comm_semiring D] [comm_semiring E]
  [algebra C D] [algebra C E] [algebra D E] [is_scalar_tower C D E] (S : set E) :
(algebra.adjoin D S).restrict_scalars C =
  (algebra.adjoin
    ((⊤ : subalgebra C D).map (is_scalar_tower.to_alg_hom C D E)) S).restrict_scalars C :=
begin
  suffices : set.range (algebra_map D E) =
    set.range (algebra_map ((⊤ : subalgebra C D).map (is_scalar_tower.to_alg_hom C D E)) E),
  { ext x, change x ∈ subsemiring.closure (_ ∪ S) ↔ x ∈ subsemiring.closure (_ ∪ S), rw this },
  ext x,
  split,
  { rintros ⟨y, hy⟩,
    exact ⟨⟨algebra_map D E y, ⟨y, ⟨algebra.mem_top, rfl⟩⟩⟩, hy⟩ },
  { rintros ⟨⟨y, ⟨z, ⟨h0, h1⟩⟩⟩, h2⟩,
    exact ⟨z, eq.trans h1 h2⟩ },
end

lemma adjoin_res_eq_adjoin_res (C D E F : Type*) [comm_semiring C] [comm_semiring D]
  [comm_semiring E] [comm_semiring F] [algebra C D] [algebra C E] [algebra C F] [algebra D F]
  [algebra E F] [is_scalar_tower C D F] [is_scalar_tower C E F] {S : set D} {T : set E}
  (hS : algebra.adjoin C S = ⊤) (hT : algebra.adjoin C T = ⊤) :
(algebra.adjoin E (algebra_map D F '' S)).restrict_scalars C =
  (algebra.adjoin D (algebra_map E F '' T)).restrict_scalars C :=
by rw [adjoin_restrict_scalars C E, adjoin_restrict_scalars C D, ←hS, ←hT, ←algebra.adjoin_image,
  ←algebra.adjoin_image, ←alg_hom.coe_to_ring_hom, ←alg_hom.coe_to_ring_hom,
  is_scalar_tower.coe_to_alg_hom, is_scalar_tower.coe_to_alg_hom, ←adjoin_union_eq_adjoin_adjoin,
  ←adjoin_union_eq_adjoin_adjoin, set.union_comm]

end algebra

section
open_locale classical
lemma algebra.fg_trans' {R S A : Type*} [comm_semiring R] [comm_semiring S] [comm_semiring A]
  [algebra R S] [algebra S A] [algebra R A] [is_scalar_tower R S A]
  (hRS : (⊤ : subalgebra R S).fg) (hSA : (⊤ : subalgebra S A).fg) :
  (⊤ : subalgebra R A).fg :=
let ⟨s, hs⟩ := hRS, ⟨t, ht⟩ := hSA in ⟨s.image (algebra_map S A) ∪ t,
by rw [finset.coe_union, finset.coe_image, algebra.adjoin_union_eq_adjoin_adjoin,
  algebra.adjoin_algebra_map, hs, algebra.map_top, is_scalar_tower.adjoin_range_to_alg_hom, ht,
  subalgebra.restrict_scalars_top]⟩
end

section algebra_map_coeffs

variables {R} (A) {ι M : Type*} [comm_semiring R] [semiring A] [add_comm_monoid M]
variables [algebra R A] [module A M] [module R M] [is_scalar_tower R A M]
variables (b : basis ι R M) (h : function.bijective (algebra_map R A))

/-- If `R` and `A` have a bijective `algebra_map R A` and act identically on `M`,
then a basis for `M` as `R`-module is also a basis for `M` as `R'`-module. -/
@[simps]
noncomputable def basis.algebra_map_coeffs : basis ι A M :=
b.map_coeffs (ring_equiv.of_bijective _ h) (λ c x, by simp)

lemma basis.algebra_map_coeffs_apply (i : ι) : b.algebra_map_coeffs A h i = b i :=
b.map_coeffs_apply _ _ _

@[simp] lemma basis.coe_algebra_map_coeffs : (b.algebra_map_coeffs A h : ι → M) = b :=
b.coe_map_coeffs _ _

end algebra_map_coeffs

section semiring

open finsupp
open_locale big_operators classical
universes v₁ w₁

variables {R S A}
variables [comm_semiring R] [semiring S] [add_comm_monoid A]
variables [algebra R S] [module S A] [module R A] [is_scalar_tower R S A]

theorem linear_independent_smul {ι : Type v₁} {b : ι → S} {ι' : Type w₁} {c : ι' → A}
  (hb : linear_independent R b) (hc : linear_independent S c) :
  linear_independent R (λ p : ι × ι', b p.1 • c p.2) :=
begin
  rw linear_independent_iff' at hb hc, rw linear_independent_iff'', rintros s g hg hsg ⟨i, k⟩,
  by_cases hik : (i, k) ∈ s,
  { have h1 : ∑ i in (s.image prod.fst).product (s.image prod.snd), g i • b i.1 • c i.2 = 0,
    { rw ← hsg, exact (finset.sum_subset finset.subset_product $ λ p _ hp,
        show g p • b p.1 • c p.2 = 0, by rw [hg p hp, zero_smul]).symm },
    rw finset.sum_product_right at h1,
    simp_rw [← smul_assoc, ← finset.sum_smul] at h1,
    exact hb _ _ (hc _ _ h1 k (finset.mem_image_of_mem _ hik)) i (finset.mem_image_of_mem _ hik) },
  exact hg _ hik
end

/-- `basis.smul (b : basis ι R S) (c : basis ι S A)` is the `R`-basis on `A`
where the `(i, j)`th basis vector is `b i • c j`. -/
noncomputable def basis.smul {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) : basis (ι × ι') R A :=
basis.of_repr ((c.repr.restrict_scalars R) ≪≫ₗ
  ((finsupp.lcongr (equiv.refl _) b.repr) ≪≫ₗ
  ((finsupp_prod_lequiv R).symm ≪≫ₗ
  ((finsupp.lcongr (equiv.prod_comm ι' ι) (linear_equiv.refl _ _))))))

@[simp] theorem basis.smul_repr {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) (x ij):
  (b.smul c).repr x ij = b.repr (c.repr x ij.2) ij.1 :=
by simp [basis.smul]

theorem basis.smul_repr_mk {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) (x i j):
  (b.smul c).repr x (i, j) = b.repr (c.repr x j) i :=
b.smul_repr c x (i, j)

@[simp] theorem basis.smul_apply {ι : Type v₁} {ι' : Type w₁}
  (b : basis ι R S) (c : basis ι' S A) (ij) :
  (b.smul c) ij = b ij.1 • c ij.2 :=
begin
  obtain ⟨i, j⟩ := ij,
  rw basis.apply_eq_iff,
  ext ⟨i', j'⟩,
  rw [basis.smul_repr, linear_equiv.map_smul, basis.repr_self, finsupp.smul_apply,
      finsupp.single_apply],
  dsimp only,
  split_ifs with hi,
  { simp [hi, finsupp.single_apply] },
  { simp [hi] },
end

end semiring

section ring

variables {R S}
variables [comm_ring R] [ring S] [algebra R S]

lemma basis.algebra_map_injective {ι : Type*} [no_zero_divisors R] [nontrivial S]
  (b : basis ι R S) :
  function.injective (algebra_map R S) :=
have no_zero_smul_divisors R S := b.no_zero_smul_divisors,
by exactI no_zero_smul_divisors.algebra_map_injective R S

end ring

section artin_tate

variables (C : Type*)

section semiring

variables [comm_semiring A] [comm_semiring B] [semiring C]
variables [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C]

open finset submodule
open_locale classical

lemma exists_subalgebra_of_fg (hAC : (⊤ : subalgebra A C).fg) (hBC : (⊤ : submodule B C).fg) :
  ∃ B₀ : subalgebra A B, B₀.fg ∧ (⊤ : submodule B₀ C).fg :=
begin
  cases hAC with x hx,
  cases hBC with y hy, have := hy,
  simp_rw [eq_top_iff', mem_span_finset] at this, choose f hf,
  let s : finset B := (finset.product (x ∪ (y * y)) y).image (function.uncurry f),
  have hsx : ∀ (xi ∈ x) (yj ∈ y), f xi yj ∈ s := λ xi hxi yj hyj,
    show function.uncurry f (xi, yj) ∈ s,
    from mem_image_of_mem _ $ mem_product.2 ⟨mem_union_left _ hxi, hyj⟩,
  have hsy : ∀ (yi yj yk ∈ y), f (yi * yj) yk ∈ s := λ yi hyi yj hyj yk hyk,
    show function.uncurry f (yi * yj, yk) ∈ s,
    from mem_image_of_mem _ $ mem_product.2 ⟨mem_union_right _ $ finset.mul_mem_mul hyi hyj, hyk⟩,
  have hxy : ∀ xi ∈ x, xi ∈ span (algebra.adjoin A (↑s : set B))
               (↑(insert 1 y : finset C) : set C) :=
    λ xi hxi, hf xi ▸ sum_mem _ (λ yj hyj, smul_mem
      (span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C))
      ⟨f xi yj, algebra.subset_adjoin $ hsx xi hxi yj hyj⟩
      (subset_span $ mem_insert_of_mem hyj)),
  have hyy : span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) *
      span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C) ≤
    span (algebra.adjoin A (↑s : set B)) (↑(insert 1 y : finset C) : set C),
  { rw [span_mul_span, span_le, coe_insert], rintros _ ⟨yi, yj, rfl | hyi, rfl | hyj, rfl⟩,
    { rw mul_one, exact subset_span (set.mem_insert _ _) },
    { rw one_mul, exact subset_span (set.mem_insert_of_mem _ hyj) },
    { rw mul_one, exact subset_span (set.mem_insert_of_mem _ hyi) },
    { rw ← hf (yi * yj), exact set_like.mem_coe.2 (sum_mem _ $ λ yk hyk, smul_mem
        (span (algebra.adjoin A (↑s : set B)) (insert 1 ↑y : set C))
        ⟨f (yi * yj) yk, algebra.subset_adjoin $ hsy yi hyi yj hyj yk hyk⟩
        (subset_span $ set.mem_insert_of_mem _ hyk : yk ∈ _)) } },
  refine ⟨algebra.adjoin A (↑s : set B), subalgebra.fg_adjoin_finset _, insert 1 y, _⟩,
  refine restrict_scalars_injective A _ _ _,
  rw [restrict_scalars_top, eq_top_iff, ← algebra.top_to_submodule, ← hx,
    algebra.adjoin_eq_span, span_le],
  refine λ r hr, submonoid.closure_induction hr (λ c hc, hxy c hc)
    (subset_span $ mem_insert_self _ _) (λ p q hp hq, hyy $ submodule.mul_mem_mul hp hq)
end

end semiring

section ring

variables [comm_ring A] [comm_ring B] [comm_ring C]
variables [algebra A B] [algebra B C] [algebra A C] [is_scalar_tower A B C]

/-- Artin--Tate lemma: if A ⊆ B ⊆ C is a chain of subrings of commutative rings, and
A is noetherian, and C is algebra-finite over A, and C is module-finite over B,
then B is algebra-finite over A.

References: Atiyah--Macdonald Proposition 7.8; Stacks 00IS; Altman--Kleiman 16.17. -/
theorem fg_of_fg_of_fg [is_noetherian_ring A]
  (hAC : (⊤ : subalgebra A C).fg) (hBC : (⊤ : submodule B C).fg)
  (hBCi : function.injective (algebra_map B C)) :
  (⊤ : subalgebra A B).fg :=
let ⟨B₀, hAB₀, hB₀C⟩ := exists_subalgebra_of_fg A B C hAC hBC in
algebra.fg_trans' (B₀.fg_top.2 hAB₀) $ subalgebra.fg_of_submodule_fg $
have is_noetherian_ring B₀, from is_noetherian_ring_of_fg hAB₀,
have is_noetherian B₀ C, by exactI is_noetherian_of_fg_of_noetherian' hB₀C,
by exactI fg_of_injective (is_scalar_tower.to_alg_hom B₀ B C).to_linear_map hBCi

end ring

end artin_tate

section alg_hom_tower

variables {A} {C D : Type*} [comm_semiring A] [comm_semiring C] [comm_semiring D]
  [algebra A C] [algebra A D]

variables (f : C →ₐ[A] D) (B) [comm_semiring B] [algebra A B] [algebra B C] [is_scalar_tower A B C]

/-- Restrict the domain of an `alg_hom`. -/
def alg_hom.restrict_domain : B →ₐ[A] D := f.comp (is_scalar_tower.to_alg_hom A B C)

/-- Extend the scalars of an `alg_hom`. -/
def alg_hom.extend_scalars : @alg_hom B C D _ _ _ _ (f.restrict_domain B).to_ring_hom.to_algebra :=
{ commutes' := λ _, rfl .. f }

variables {B}

/-- `alg_hom`s from the top of a tower are equivalent to a pair of `alg_hom`s. -/
def alg_hom_equiv_sigma :
  (C →ₐ[A] D) ≃ Σ (f : B →ₐ[A] D), @alg_hom B C D _ _ _ _ f.to_ring_hom.to_algebra :=
{ to_fun := λ f, ⟨f.restrict_domain B, f.extend_scalars B⟩,
  inv_fun := λ fg,
    let alg := fg.1.to_ring_hom.to_algebra in by exactI fg.2.restrict_scalars A,
  left_inv := λ f, by { dsimp only, ext, refl },
  right_inv :=
  begin
    rintros ⟨⟨f, _, _, _, _, _⟩, g, _, _, _, _, hg⟩,
    have : f = λ x, g (algebra_map B C x) := by { ext, exact (hg x).symm },
    subst this,
    refl,
  end }

end alg_hom_tower
