/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Joey van Langen, Casper Putz
-/
import tactic.apply_fun
import data.equiv.ring
import data.zmod.algebra
import linear_algebra.finite_dimensional
import ring_theory.integral_domain
import field_theory.separable
import field_theory.splitting_field

/-!
# Finite fields

This file contains basic results about finite fields.
Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

See `ring_theory.integral_domain` for the fact that the unit group of a finite field is a
cyclic group, as well as the fact that every finite integral domain is a field
(`field_of_is_domain`).

## Main results

1. `fintype.card_units`: The unit group of a finite field is has cardinality `q - 1`.
2. `sum_pow_units`: The sum of `x^i`, where `x` ranges over the units of `K`, is
   - `q-1` if `q-1 ∣ i`
   - `0`   otherwise
3. `finite_field.card`: The cardinality `q` is a power of the characteristic of `K`.
   See `card'` for a variant.

## Notation

Throughout most of this file, `K` denotes a finite field
and `q` is notation for the cardinality of `K`.

## Implementation notes

While `fintype Kˣ` can be inferred from `fintype K` in the presence of `decidable_eq K`,
in this file we take the `fintype Kˣ` argument directly to reduce the chance of typeclass
diamonds, as `fintype` carries data.

-/

variables {K : Type*} {R : Type*}
local notation `q` := fintype.card K

open_locale big_operators polynomial

namespace finite_field
open finset function

section polynomial

variables [comm_ring R] [is_domain R]

open polynomial

/-- The cardinality of a field is at most `n` times the cardinality of the image of a degree `n`
  polynomial -/
lemma card_image_polynomial_eval [decidable_eq R] [fintype R] {p : R[X]}
  (hp : 0 < p.degree) : fintype.card R ≤ nat_degree p * (univ.image (λ x, eval x p)).card :=
finset.card_le_mul_card_image _ _
  (λ a _, calc _ = (p - C a).roots.to_finset.card : congr_arg card
    (by simp [finset.ext_iff, mem_roots_sub_C hp])
    ... ≤ (p - C a).roots.card : multiset.to_finset_card_le _
    ... ≤ _ : card_roots_sub_C' hp)

/-- If `f` and `g` are quadratic polynomials, then the `f.eval a + g.eval b = 0` has a solution. -/
lemma exists_root_sum_quadratic [fintype R] {f g : R[X]} (hf2 : degree f = 2)
  (hg2 : degree g = 2) (hR : fintype.card R % 2 = 1) : ∃ a b, f.eval a + g.eval b = 0 :=
by letI := classical.dec_eq R; exact
suffices ¬ disjoint (univ.image (λ x : R, eval x f)) (univ.image (λ x : R, eval x (-g))),
begin
  simp only [disjoint_left, mem_image] at this,
  push_neg at this,
  rcases this with ⟨x, ⟨a, _, ha⟩, ⟨b, _, hb⟩⟩,
  exact ⟨a, b, by rw [ha, ← hb, eval_neg, neg_add_self]⟩
end,
assume hd : disjoint _ _,
lt_irrefl (2 * ((univ.image (λ x : R, eval x f)) ∪ (univ.image (λ x : R, eval x (-g)))).card) $
calc 2 * ((univ.image (λ x : R, eval x f)) ∪ (univ.image (λ x : R, eval x (-g)))).card
    ≤ 2 * fintype.card R : nat.mul_le_mul_left _ (finset.card_le_univ _)
... = fintype.card R + fintype.card R : two_mul _
... < nat_degree f * (univ.image (λ x : R, eval x f)).card +
      nat_degree (-g) * (univ.image (λ x : R, eval x (-g))).card :
    add_lt_add_of_lt_of_le
      (lt_of_le_of_ne
        (card_image_polynomial_eval (by rw hf2; exact dec_trivial))
        (mt (congr_arg (%2)) (by simp [nat_degree_eq_of_degree_eq_some hf2, hR])))
      (card_image_polynomial_eval (by rw [degree_neg, hg2]; exact dec_trivial))
... = 2 * (univ.image (λ x : R, eval x f) ∪ univ.image (λ x : R, eval x (-g))).card :
  by rw [card_disjoint_union hd]; simp [nat_degree_eq_of_degree_eq_some hf2,
    nat_degree_eq_of_degree_eq_some hg2, bit0, mul_add]

end polynomial

lemma prod_univ_units_id_eq_neg_one [comm_ring K] [is_domain K] [fintype Kˣ] :
  (∏ x : Kˣ, x) = (-1 : Kˣ) :=
begin
  classical,
  have : (∏ x in (@univ Kˣ _).erase (-1), x) = 1,
  from prod_involution (λ x _, x⁻¹) (by simp)
    (λ a, by simp [units.inv_eq_self_iff] {contextual := tt})
    (λ a, by simp [@inv_eq_iff_inv_eq _ _ a, eq_comm] {contextual := tt})
    (by simp),
  rw [← insert_erase (mem_univ (-1 : Kˣ)), prod_insert (not_mem_erase _ _),
      this, mul_one]
end

section
variables [group_with_zero K] [fintype K]

lemma pow_card_sub_one_eq_one (a : K) (ha : a ≠ 0) : a ^ (q - 1) = 1 :=
calc a ^ (fintype.card K - 1) = (units.mk0 a ha ^ (fintype.card K - 1) : Kˣ) :
    by rw [units.coe_pow, units.coe_mk0]
  ... = 1 : by { classical, rw [← fintype.card_units, pow_card_eq_one], refl }

lemma pow_card (a : K) : a ^ q = a :=
begin
  have hp : 0 < fintype.card K := lt_trans zero_lt_one fintype.one_lt_card,
  by_cases h : a = 0, { rw h, apply zero_pow hp },
  rw [← nat.succ_pred_eq_of_pos hp, pow_succ, nat.pred_eq_sub_one,
    pow_card_sub_one_eq_one a h, mul_one],
end

lemma pow_card_pow (n : ℕ) (a : K) : a ^ q ^ n = a :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, pow_mul, ih, pow_card], },
end

end

variables (K) [field K] [fintype K]

theorem card (p : ℕ) [char_p K p] : ∃ (n : ℕ+), nat.prime p ∧ q = p^(n : ℕ) :=
begin
  haveI hp : fact p.prime := ⟨char_p.char_is_prime K p⟩,
  letI : module (zmod p) K := { .. (zmod.cast_hom dvd_rfl K).to_module },
  obtain ⟨n, h⟩ := vector_space.card_fintype (zmod p) K,
  rw zmod.card at h,
  refine ⟨⟨n, _⟩, hp.1, h⟩,
  apply or.resolve_left (nat.eq_zero_or_pos n),
  rintro rfl,
  rw pow_zero at h,
  have : (0 : K) = 1, { apply fintype.card_le_one_iff.mp (le_of_eq h) },
  exact absurd this zero_ne_one,
end

-- this statement doesn't use `q` because we want `K` to be an explicit parameter
theorem card' : ∃ (p : ℕ) (n : ℕ+), nat.prime p ∧ fintype.card K = p^(n : ℕ) :=
let ⟨p, hc⟩ := char_p.exists K in ⟨p, @finite_field.card K _ _ p hc⟩

@[simp] lemma cast_card_eq_zero : (q : K) = 0 :=
begin
  rcases char_p.exists K with ⟨p, _char_p⟩, resetI,
  rcases card K p with ⟨n, hp, hn⟩,
  simp only [char_p.cast_eq_zero_iff K p, hn],
  conv { congr, rw [← pow_one p] },
  exact pow_dvd_pow _ n.2,
end

lemma forall_pow_eq_one_iff (i : ℕ) :
  (∀ x : Kˣ, x ^ i = 1) ↔ q - 1 ∣ i :=
begin
  classical,
  obtain ⟨x, hx⟩ := is_cyclic.exists_generator Kˣ,
  rw [←fintype.card_units, ←order_of_eq_card_of_forall_mem_zpowers hx, order_of_dvd_iff_pow_eq_one],
  split,
  { intro h, apply h },
  { intros h y,
    simp_rw ← mem_powers_iff_mem_zpowers at hx,
    rcases hx y with ⟨j, rfl⟩,
    rw [← pow_mul, mul_comm, pow_mul, h, one_pow], }
end

/-- The sum of `x ^ i` as `x` ranges over the units of a finite field of cardinality `q`
is equal to `0` unless `(q - 1) ∣ i`, in which case the sum is `q - 1`. -/
lemma sum_pow_units [fintype Kˣ] (i : ℕ) :
  ∑ x : Kˣ, (x ^ i : K) = if (q - 1) ∣ i then -1 else 0 :=
begin
  let φ : Kˣ →* K :=
  { to_fun   := λ x, x ^ i,
    map_one' := by rw [units.coe_one, one_pow],
    map_mul' := by { intros, rw [units.coe_mul, mul_pow] } },
  haveI : decidable (φ = 1), { classical, apply_instance },
  calc ∑ x : Kˣ, φ x = if φ = 1 then fintype.card Kˣ else 0 : sum_hom_units φ
                      ... = if (q - 1) ∣ i then -1 else 0 : _,
  suffices : (q - 1) ∣ i ↔ φ = 1,
  { simp only [this],
    split_ifs with h h, swap, refl,
    rw [fintype.card_units, nat.cast_sub, cast_card_eq_zero, nat.cast_one, zero_sub],
    show 1 ≤ q, from fintype.card_pos_iff.mpr ⟨0⟩ },
  rw [← forall_pow_eq_one_iff, monoid_hom.ext_iff],
  apply forall_congr, intro x,
  rw [units.ext_iff, units.coe_pow, units.coe_one, monoid_hom.one_apply],
  refl,
end

/-- The sum of `x ^ i` as `x` ranges over a finite field of cardinality `q`
is equal to `0` if `i < q - 1`. -/
lemma sum_pow_lt_card_sub_one (i : ℕ) (h : i < q - 1) :
  ∑ x : K, x ^ i = 0 :=
begin
  by_cases hi : i = 0,
  { simp only [hi, nsmul_one, sum_const, pow_zero, card_univ, cast_card_eq_zero], },
  classical,
  have hiq : ¬ (q - 1) ∣ i, { contrapose! h,  exact nat.le_of_dvd (nat.pos_of_ne_zero hi) h },
  let φ : Kˣ ↪ K := ⟨coe, units.ext⟩,
  have : univ.map φ = univ \ {0},
  { ext x,
    simp only [true_and, embedding.coe_fn_mk, mem_sdiff, units.exists_iff_ne_zero,
               mem_univ, mem_map, exists_prop_of_true, mem_singleton] },
  calc ∑ x : K, x ^ i = ∑ x in univ \ {(0 : K)}, x ^ i :
    by rw [← sum_sdiff ({0} : finset K).subset_univ, sum_singleton,
           zero_pow (nat.pos_of_ne_zero hi), add_zero]
    ... = ∑ x : Kˣ, x ^ i : by { rw [← this, univ.sum_map φ], refl }
    ... = 0 : by { rw [sum_pow_units K i, if_neg], exact hiq, }
end

section is_splitting_field
open polynomial

section

variables (K' : Type*) [field K'] {p n : ℕ}

lemma X_pow_card_sub_X_nat_degree_eq (hp : 1 < p) :
  (X ^ p - X : K'[X]).nat_degree = p :=
begin
  have h1 : (X : K'[X]).degree < (X ^ p : K'[X]).degree,
  { rw [degree_X_pow, degree_X],
    exact_mod_cast hp },
  rw [nat_degree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt h1), nat_degree_X_pow],
end

lemma X_pow_card_pow_sub_X_nat_degree_eq (hn : n ≠ 0) (hp : 1 < p) :
  (X ^ p ^ n - X : K'[X]).nat_degree = p ^ n :=
X_pow_card_sub_X_nat_degree_eq K' $ nat.one_lt_pow _ _ (nat.pos_of_ne_zero hn) hp

lemma X_pow_card_sub_X_ne_zero (hp : 1 < p) : (X ^ p - X : K'[X]) ≠ 0 :=
ne_zero_of_nat_degree_gt $
calc 1 < _ : hp
... = _ : (X_pow_card_sub_X_nat_degree_eq K' hp).symm

lemma X_pow_card_pow_sub_X_ne_zero (hn : n ≠ 0) (hp : 1 < p) :
  (X ^ p ^ n - X : K'[X]) ≠ 0 :=
X_pow_card_sub_X_ne_zero K' $ nat.one_lt_pow _ _ (nat.pos_of_ne_zero hn) hp

end

variables (p : ℕ) [fact p.prime] [char_p K p]
lemma roots_X_pow_card_sub_X : roots (X^q - X : K[X]) = finset.univ.val :=
begin
  classical,
  have aux : (X^q - X : K[X]) ≠ 0 := X_pow_card_sub_X_ne_zero K fintype.one_lt_card,
  have : (roots (X^q - X : K[X])).to_finset = finset.univ,
  { rw eq_univ_iff_forall,
    intro x,
    rw [multiset.mem_to_finset, mem_roots aux, is_root.def, eval_sub, eval_pow, eval_X, sub_eq_zero,
      pow_card] },
  rw [←this, multiset.to_finset_val, eq_comm, multiset.erase_dup_eq_self],
  apply nodup_roots,
  rw separable_def,
  convert is_coprime_one_right.neg_right,
  rw [derivative_sub, derivative_X, derivative_X_pow, ←C_eq_nat_cast,
    C_eq_zero.mpr (char_p.cast_card_eq_zero K), zero_mul, zero_sub],
end

instance : is_splitting_field (zmod p) K (X^q - X) :=
{ splits :=
  begin
    have h : (X^q - X : K[X]).nat_degree = q :=
      X_pow_card_sub_X_nat_degree_eq K fintype.one_lt_card,
    rw [←splits_id_iff_splits, splits_iff_card_roots, polynomial.map_sub, polynomial.map_pow,
      map_X, h, roots_X_pow_card_sub_X K, ←finset.card_def, finset.card_univ],
  end,
  adjoin_roots :=
  begin
    classical,
    transitivity algebra.adjoin (zmod p) ((roots (X^q - X : K[X])).to_finset : set K),
    { simp only [polynomial.map_pow, map_X, polynomial.map_sub], convert rfl },
    { rw [roots_X_pow_card_sub_X, val_to_finset, coe_univ, algebra.adjoin_univ], }
  end }

end is_splitting_field

variables {K}

theorem frobenius_pow {p : ℕ} [fact p.prime] [char_p K p] {n : ℕ} (hcard : q = p^n) :
  (frobenius K p) ^ n = 1 :=
begin
  ext, conv_rhs { rw [ring_hom.one_def, ring_hom.id_apply, ← pow_card x, hcard], }, clear hcard,
  induction n, {simp},
  rw [pow_succ, pow_succ', pow_mul, ring_hom.mul_def, ring_hom.comp_apply, frobenius_def, n_ih]
end

open polynomial

lemma expand_card (f : K[X]) :
  expand K q f = f ^ q :=
begin
  cases char_p.exists K with p hp,
  letI := hp,
  rcases finite_field.card K p with ⟨⟨n, npos⟩, ⟨hp, hn⟩⟩,
  haveI : fact p.prime := ⟨hp⟩,
  dsimp at hn,
  rw [hn, ← map_expand_pow_char, frobenius_pow hn, ring_hom.one_def, map_id]
end

end finite_field

namespace zmod

open finite_field polynomial

lemma sq_add_sq (p : ℕ) [hp : fact p.prime] (x : zmod p) :
  ∃ a b : zmod p, a^2 + b^2 = x :=
begin
  cases hp.1.eq_two_or_odd with hp2 hp_odd,
  { substI p, change fin 2 at x, fin_cases x, { use 0, simp }, { use [0, 1], simp } },
  let f : (zmod p)[X] := X^2,
  let g : (zmod p)[X] := X^2 - C x,
  obtain ⟨a, b, hab⟩ : ∃ a b, f.eval a + g.eval b = 0 :=
    @exists_root_sum_quadratic _ _ _ _ f g
      (degree_X_pow 2) (degree_X_pow_sub_C dec_trivial _) (by rw [zmod.card, hp_odd]),
  refine ⟨a, b, _⟩,
  rw ← sub_eq_zero,
  simpa only [eval_C, eval_X, eval_pow, eval_sub, ← add_sub_assoc] using hab,
end

end zmod

namespace char_p

lemma sq_add_sq (R : Type*) [comm_ring R] [is_domain R]
  (p : ℕ) [fact (0 < p)] [char_p R p] (x : ℤ) :
  ∃ a b : ℕ, (a^2 + b^2 : R) = x :=
begin
  haveI := char_is_prime_of_pos R p,
  obtain ⟨a, b, hab⟩ := zmod.sq_add_sq p x,
  refine ⟨a.val, b.val, _⟩,
  simpa using congr_arg (zmod.cast_hom dvd_rfl R) hab
end

end char_p

open_locale nat
open zmod

/-- The **Fermat-Euler totient theorem**. `nat.modeq.pow_totient` is an alternative statement
  of the same theorem. -/
@[simp] lemma zmod.pow_totient {n : ℕ} [fact (0 < n)] (x : (zmod n)ˣ) : x ^ φ n = 1 :=
by rw [← card_units_eq_totient, pow_card_eq_one]

/-- The **Fermat-Euler totient theorem**. `zmod.pow_totient` is an alternative statement
  of the same theorem. -/
lemma nat.modeq.pow_totient {x n : ℕ} (h : nat.coprime x n) : x ^ φ n ≡ 1 [MOD n] :=
begin
  cases n, {simp},
  rw ← zmod.eq_iff_modeq_nat,
  let x' : units (zmod (n+1)) := zmod.unit_of_coprime _ h,
  have := zmod.pow_totient x',
  apply_fun (coe : units (zmod (n+1)) → zmod (n+1)) at this,
  simpa only [-zmod.pow_totient, nat.succ_eq_add_one, nat.cast_pow, units.coe_one,
    nat.cast_one, coe_unit_of_coprime, units.coe_pow],
end

section

variables {V : Type*} [fintype K] [division_ring K] [add_comm_group V] [module K V]

-- should this go in a namespace?
-- finite_dimensional would be natural,
-- but we don't assume it...
lemma card_eq_pow_finrank [fintype V] :
  fintype.card V = q ^ (finite_dimensional.finrank K V) :=
begin
  let b := is_noetherian.finset_basis K V,
  rw [module.card_fintype b, ← finite_dimensional.finrank_eq_card_basis b],
end

end

open finite_field
namespace zmod

/-- A variation on Fermat's little theorem. See `zmod.pow_card_sub_one_eq_one` -/
@[simp] lemma pow_card {p : ℕ} [fact p.prime] (x : zmod p) : x ^ p = x :=
by { have h := finite_field.pow_card x, rwa zmod.card p at h }

@[simp] lemma pow_card_pow {n p : ℕ} [fact p.prime] (x : zmod p) : x ^ p ^ n = x :=
begin
  induction n with n ih,
  { simp, },
  { simp [pow_succ, pow_mul, ih, pow_card], },
end

@[simp] lemma frobenius_zmod (p : ℕ) [fact p.prime] :
  frobenius (zmod p) p = ring_hom.id _ :=
by { ext a, rw [frobenius_def, zmod.pow_card, ring_hom.id_apply] }

@[simp] lemma card_units (p : ℕ) [fact p.prime] : fintype.card ((zmod p)ˣ) = p - 1 :=
by rw [fintype.card_units, card]

/-- **Fermat's Little Theorem**: for every unit `a` of `zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem units_pow_card_sub_one_eq_one (p : ℕ) [fact p.prime] (a : (zmod p)ˣ) :
  a ^ (p - 1) = 1 :=
by rw [← card_units p, pow_card_eq_one]

/-- **Fermat's Little Theorem**: for all nonzero `a : zmod p`, we have `a ^ (p - 1) = 1`. -/
theorem pow_card_sub_one_eq_one {p : ℕ} [fact p.prime] {a : zmod p} (ha : a ≠ 0) :
  a ^ (p - 1) = 1 :=
by { have h := pow_card_sub_one_eq_one a ha, rwa zmod.card p at h }

open polynomial

lemma expand_card {p : ℕ} [fact p.prime] (f : polynomial (zmod p)) :
  expand (zmod p) p f = f ^ p :=
by { have h := finite_field.expand_card f, rwa zmod.card p at h }

end zmod

/-- **Fermat's Little Theorem**: for all `a : ℤ` coprime to `p`, we have
`a ^ (p - 1) ≡ 1 [ZMOD p]`. -/
lemma int.modeq.pow_card_sub_one_eq_one {p : ℕ} (hp : nat.prime p) {n : ℤ} (hpn : is_coprime n p) :
  n ^ (p - 1) ≡ 1 [ZMOD p] :=
begin
  haveI : fact p.prime := ⟨hp⟩,
  have : ¬ (n : zmod p) = 0,
  { rw [char_p.int_cast_eq_zero_iff _ p, ← (nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd],
    { exact hpn.symm },
    exact zmod.char_p p },
  simpa [← zmod.int_coe_eq_int_coe_iff] using zmod.pow_card_sub_one_eq_one this
end
