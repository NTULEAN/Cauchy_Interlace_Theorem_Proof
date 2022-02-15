/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/

import algebra.order.with_zero
import algebra.punit_instances
import ring_theory.ideal.operations

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
 * `v 0 = 0`
 * `∀ x y, v (x + y) ≤ max (v x) (v y)`

`valuation R Γ₀`is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : valuation R Γ₁` and `v₂ : valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

The support of a valuation `v : valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

## Main definitions

* `valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `valuation.is_equiv`, the heterogeneous equivalence relation on valuations
* `valuation.supp`, the support of a valuation

* `add_valuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`add_valuation R Γ₀` is implemented as `valuation R (multiplicative (order_dual Γ₀))`.

## TODO

If ever someone extends `valuation`, we should fully comply to the `fun_like` by migrating the
boilerplate lemmas to `valuation_class`.
-/

open_locale classical big_operators
noncomputable theory

open function ideal

variables {F R : Type*} -- This will be a ring, assumed commutative in some sections

section
variables (F R) (Γ₀ : Type*) [linear_ordered_comm_monoid_with_zero Γ₀] [ring R]

/-- The type of `Γ₀`-valued valuations on `R`.

When you extend this structure, make sure to extend `valuation_class`. -/
@[nolint has_inhabited_instance]
structure valuation extends R →*₀ Γ₀ :=
(map_add_le_max' : ∀ x y, to_fun (x + y) ≤ max (to_fun x) (to_fun y))

/-- `valuation_class F α β` states that `F` is a type of valuations.

You should also extend this typeclass when you extend `valuation`. -/
class valuation_class extends monoid_with_zero_hom_class F R Γ₀ :=
(map_add_le_max (f : F) (x y : R) : f (x + y) ≤ max (f x) (f y))

export valuation_class (map_add_le_max)

instance [valuation_class F R Γ₀] : has_coe_t F (valuation R Γ₀) :=
⟨λ f, { to_fun := f, map_one' := map_one f, map_zero' := map_zero f, map_mul' := map_mul f,
  map_add_le_max' := map_add_le_max f }⟩

end

namespace valuation

variables {Γ₀   : Type*}
variables {Γ'₀  : Type*}
variables {Γ''₀ : Type*} [linear_ordered_comm_monoid_with_zero Γ''₀]

section basic
variables [ring R]

section monoid
variables [linear_ordered_comm_monoid_with_zero Γ₀] [linear_ordered_comm_monoid_with_zero Γ'₀]

instance : valuation_class (valuation R Γ₀) R Γ₀ :=
{ coe := λ f, f.to_fun,
  coe_injective' := λ f g h, by { obtain ⟨⟨_, _⟩, _⟩ := f, obtain ⟨⟨_, _⟩, _⟩ := g, congr' },
  map_mul := λ f, f.map_mul',
  map_one := λ f, f.map_one',
  map_zero := λ f, f.map_zero',
  map_add_le_max := λ f, f.map_add_le_max' }

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : has_coe_to_fun (valuation R Γ₀) (λ _, R → Γ₀) := fun_like.has_coe_to_fun

@[simp] lemma to_fun_eq_coe (v : valuation R Γ₀) : v.to_fun = v := rfl
@[ext] lemma ext {v₁ v₂ : valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ := fun_like.ext _ _ h

variables (v : valuation R Γ₀) {x y z : R}

@[simp, norm_cast] lemma coe_coe : ⇑(v : R →*₀ Γ₀) = v := rfl

@[simp] lemma map_zero : v 0 = 0 := v.map_zero'
@[simp] lemma map_one  : v 1 = 1 := v.map_one'
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.map_mul'
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ max (v x) (v y) := v.map_add_le_max'

lemma map_add_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x + y) ≤ g :=
le_trans (v.map_add x y) $ max_le hx hy

lemma map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g :=
lt_of_le_of_lt (v.map_add x y) $ max_lt hx hy

lemma map_sum_le {ι : Type*} {s : finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, v (f i) ≤ g) :
  v (∑ i in s, f i) ≤ g :=
begin
  refine finset.induction_on s
    (λ _, trans_rel_right (≤) v.map_zero zero_le') (λ a s has ih hf, _) hf,
  rw finset.forall_mem_insert at hf, rw finset.sum_insert has,
  exact v.map_add_le hf.1 (ih hf.2)
end

lemma map_sum_lt {ι : Type*} {s : finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ 0)
  (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i in s, f i) < g :=
begin
  refine finset.induction_on s
    (λ _, trans_rel_right (<) v.map_zero (zero_lt_iff.2 hg)) (λ a s has ih hf, _) hf,
  rw finset.forall_mem_insert at hf, rw finset.sum_insert has,
  exact v.map_add_lt hf.1 (ih hf.2)
end

lemma map_sum_lt' {ι : Type*} {s : finset ι} {f : ι → R} {g : Γ₀} (hg : 0 < g)
  (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i in s, f i) < g :=
v.map_sum_lt (ne_of_gt hg) hf

@[simp] lemma map_pow  : ∀ x (n:ℕ), v (x^n) = (v x)^n :=
v.to_monoid_with_zero_hom.to_monoid_hom.map_pow

/-- Deprecated. Use `fun_like.ext_iff`. -/
lemma ext_iff {v₁ v₂ : valuation R Γ₀} : v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r := fun_like.ext_iff

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.

/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder : preorder R := preorder.lift v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
@[simp] lemma zero_iff [nontrivial Γ₀] {K : Type*} [division_ring K]
  (v : valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
v.to_monoid_with_zero_hom.map_eq_zero

lemma ne_zero_iff [nontrivial Γ₀] {K : Type*} [division_ring K]
  (v : valuation K Γ₀) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
v.to_monoid_with_zero_hom.map_ne_zero

theorem unit_map_eq (u : Rˣ) :
  (units.map (v : R →* Γ₀) u : Γ₀) = v u := rfl

/-- A ring homomorphism `S → R` induces a map `valuation R Γ₀ → valuation S Γ₀`. -/
def comap {S : Type*} [ring S] (f : S →+* R) (v : valuation R Γ₀) :
  valuation S Γ₀ :=
{ to_fun := v ∘ f,
  map_add_le_max' := λ x y, by simp only [comp_app, map_add, f.map_add],
  .. v.to_monoid_with_zero_hom.comp f.to_monoid_with_zero_hom, }

@[simp] lemma comap_id : v.comap (ring_hom.id R) = v := ext $ λ r, rfl

lemma comap_comp {S₁ : Type*} {S₂ : Type*} [ring S₁] [ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
  v.comap (g.comp f) = (v.comap g).comap f :=
ext $ λ r, rfl

/-- A `≤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map `valuation R Γ₀ → valuation R Γ'₀`.
-/
def map (f : Γ₀ →*₀ Γ'₀) (hf : monotone f) (v : valuation R Γ₀) :
  valuation R Γ'₀ :=
{ to_fun := f ∘ v,
  map_add_le_max' := λ r s,
    calc f (v (r + s)) ≤ f (max (v r) (v s))     : hf (v.map_add r s)
                   ... = max (f (v r)) (f (v s)) : hf.map_max,
  .. monoid_with_zero_hom.comp f v.to_monoid_with_zero_hom }

/-- Two valuations on `R` are defined to be equivalent if they induce the same preorder on `R`. -/
def is_equiv (v₁ : valuation R Γ₀) (v₂ : valuation R Γ'₀) : Prop :=
∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

end monoid

section group
variables [linear_ordered_comm_group_with_zero Γ₀] {R} {Γ₀} (v : valuation R Γ₀) {x y z : R}

@[simp] lemma map_inv {K : Type*} [division_ring K]
  (v : valuation K Γ₀) {x : K} : v x⁻¹ = (v x)⁻¹ :=
v.to_monoid_with_zero_hom.map_inv x

@[simp] lemma map_zpow {K : Type*} [division_ring K] (v : valuation K Γ₀) {x : K} {n : ℤ} :
  v (x^n) = (v x)^n :=
v.to_monoid_with_zero_hom.map_zpow x n

lemma map_units_inv (x : Rˣ) : v (x⁻¹ : Rˣ) = (v x)⁻¹ :=
v.to_monoid_with_zero_hom.to_monoid_hom.map_units_inv x

@[simp] lemma map_neg (x : R) : v (-x) = v x :=
v.to_monoid_with_zero_hom.to_monoid_hom.map_neg x

lemma map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
v.to_monoid_with_zero_hom.to_monoid_hom.map_sub_swap x y

lemma map_sub (x y : R) : v (x - y) ≤ max (v x) (v y) :=
calc v (x - y) = v (x + -y)         : by rw [sub_eq_add_neg]
           ... ≤ max (v x) (v $ -y) : v.map_add _ _
           ... = max (v x) (v y)    : by rw map_neg

lemma map_sub_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x - y) ≤ g :=
begin
  rw sub_eq_add_neg,
  exact v.map_add_le hx (le_trans (le_of_eq (v.map_neg y)) hy)
end

lemma map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) :=
begin
  suffices : ¬v (x + y) < max (v x) (v y),
    from or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this,
  intro h',
  wlog vyx : v y < v x using x y,
  { apply lt_or_gt_of_ne h.symm },
  { rw max_eq_left_of_lt vyx at h',
    apply lt_irrefl (v x),
    calc v x = v ((x+y) - y)         : by simp
         ... ≤ max (v $ x + y) (v y) : map_sub _ _ _
         ... < v x                   : max_lt h' vyx },
  { apply this h.symm,
    rwa [add_comm, max_comm] at h' }
end

lemma map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x :=
begin
  have := valuation.map_add_of_distinct_val v (ne_of_gt h).symm,
  rw max_eq_right (le_of_lt h) at this,
  simpa using this
end

/-- The subgroup of elements whose valuation is less than a certain unit.-/
def lt_add_subgroup (v : valuation R Γ₀) (γ : Γ₀ˣ) : add_subgroup R :=
{ carrier   := {x | v x < γ},
  zero_mem' := by { have h := units.ne_zero γ, contrapose! h, simpa using h },
  add_mem'  := λ x y x_in y_in, lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in),
  neg_mem'  := λ x x_in, by rwa [set.mem_set_of_eq, map_neg] }

end group
end basic -- end of section

namespace is_equiv
variables [ring R]
variables [linear_ordered_comm_monoid_with_zero Γ₀] [linear_ordered_comm_monoid_with_zero Γ'₀]
variables {v : valuation R Γ₀}
variables {v₁ : valuation R Γ₀} {v₂ : valuation R Γ'₀} {v₃ : valuation R Γ''₀}

@[refl] lemma refl : v.is_equiv v :=
λ _ _, iff.refl _

@[symm] lemma symm (h : v₁.is_equiv v₂) : v₂.is_equiv v₁ :=
λ _ _, iff.symm (h _ _)

@[trans] lemma trans (h₁₂ : v₁.is_equiv v₂) (h₂₃ : v₂.is_equiv v₃) : v₁.is_equiv v₃ :=
λ _ _, iff.trans (h₁₂ _ _) (h₂₃ _ _)

lemma of_eq {v' : valuation R Γ₀} (h : v = v') : v.is_equiv v' :=
by { subst h }

lemma map {v' : valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀) (hf : monotone f)
  (inf : injective f) (h : v.is_equiv v') :
  (v.map f hf).is_equiv (v'.map f hf) :=
let H : strict_mono f := hf.strict_mono_of_injective inf in
λ r s,
calc f (v r) ≤ f (v s) ↔ v r ≤ v s   : by rw H.le_iff_le
                   ... ↔ v' r ≤ v' s : h r s
                   ... ↔ f (v' r) ≤ f (v' s) : by rw H.le_iff_le

/-- `comap` preserves equivalence. -/
lemma comap {S : Type*} [ring S] (f : S →+* R) (h : v₁.is_equiv v₂) :
  (v₁.comap f).is_equiv (v₂.comap f) :=
λ r s, h (f r) (f s)

lemma val_eq (h : v₁.is_equiv v₂) {r s : R} :
  v₁ r = v₁ s ↔ v₂ r = v₂ s :=
by simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)

lemma ne_zero (h : v₁.is_equiv v₂) {r : R} :
  v₁ r ≠ 0 ↔ v₂ r ≠ 0 :=
begin
  have : v₁ r ≠ v₁ 0 ↔ v₂ r ≠ v₂ 0 := not_iff_not_of_iff h.val_eq,
  rwa [v₁.map_zero, v₂.map_zero] at this,
end

end is_equiv -- end of namespace

section

lemma is_equiv_of_map_strict_mono [linear_ordered_comm_monoid_with_zero Γ₀]
  [linear_ordered_comm_monoid_with_zero Γ'₀] [ring R] {v : valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀)
  (H : strict_mono f) :
  is_equiv (v.map f (H.monotone)) v :=
λ x y, ⟨H.le_iff_le.mp, λ h, H.monotone h⟩

lemma is_equiv_of_val_le_one [linear_ordered_comm_group_with_zero Γ₀]
  [linear_ordered_comm_group_with_zero Γ'₀]
  {K : Type*} [division_ring K]
  (v : valuation K Γ₀) (v' : valuation K Γ'₀) (h : ∀ {x:K}, v x ≤ 1 ↔ v' x ≤ 1) :
  v.is_equiv v' :=
begin
  intros x y,
  by_cases hy : y = 0, { simp [hy, zero_iff], },
  rw show y = 1 * y, by rw one_mul,
  rw [← (inv_mul_cancel_right₀ hy x)],
  iterate 2 {rw [v.map_mul _ y, v'.map_mul _ y]},
  rw [v.map_one, v'.map_one],
  split; intro H,
  { apply mul_le_mul_right',
    replace hy := v.ne_zero_iff.mpr hy,
    replace H := le_of_le_mul_right hy H,
    rwa h at H, },
  { apply mul_le_mul_right',
    replace hy := v'.ne_zero_iff.mpr hy,
    replace H := le_of_le_mul_right hy H,
    rwa h, },
end

end

section supp
variables [comm_ring R]
variables [linear_ordered_comm_monoid_with_zero Γ₀] [linear_ordered_comm_monoid_with_zero Γ'₀]
variables (v : valuation R Γ₀)

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
def supp : ideal R :=
{ carrier   := {x | v x = 0},
  zero_mem' := map_zero v,
  add_mem'  := λ x y hx hy, le_zero_iff.mp $
    calc v (x + y) ≤ max (v x) (v y) : v.map_add x y
               ... ≤ 0               : max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy),
  smul_mem' := λ c x hx, calc v (c * x)
                        = v c * v x : map_mul v c x
                    ... = v c * 0 : congr_arg _ hx
                    ... = 0 : mul_zero _ }

@[simp] lemma mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 := iff.rfl
-- @[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl

/-- The support of a valuation is a prime ideal. -/
instance [nontrivial Γ₀] [no_zero_divisors Γ₀] : ideal.is_prime (supp v) :=
⟨λ (h : v.supp = ⊤), one_ne_zero $ show (1 : Γ₀) = 0,
from calc 1 = v 1 : v.map_one.symm
        ... = 0   : show (1:R) ∈ supp v, by { rw h, trivial },
 λ x y hxy, begin
    show v x = 0 ∨ v y = 0,
    change v (x * y) = 0 at hxy,
    rw [v.map_mul x y] at hxy,
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy
  end⟩

lemma map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
begin
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a,
  { intros a' s' h', refine le_trans (v.map_add a' s') (max_le le_rfl _), simp [h'], },
  apply le_antisymm (aux a s h),
  calc v a = v (a + s + -s) : by simp
       ... ≤ v (a + s)      : aux (a + s) (-s) (by rwa ←ideal.neg_mem_iff at h)
end

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def on_quot_val {J : ideal R} (hJ : J ≤ supp v) :
  R ⧸ J → Γ₀ :=
λ q, quotient.lift_on' q v $ λ a b h,
calc v a = v (b + (a - b)) : by simp
     ... = v b             : v.map_add_supp b (hJ h)

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def on_quot {J : ideal R} (hJ : J ≤ supp v) :
  valuation (R ⧸ J) Γ₀ :=
{ to_fun := v.on_quot_val hJ,
  map_zero' := v.map_zero,
  map_one'  := v.map_one,
  map_mul'  := λ xbar ybar, quotient.ind₂' v.map_mul xbar ybar,
  map_add_le_max'  := λ xbar ybar, quotient.ind₂' v.map_add xbar ybar }

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
ext $ λ r,
begin
  refine @quotient.lift_on_mk _ _ (J.quotient_rel) v (λ a b h, _) _,
  calc v a = v (b + (a - b)) : by simp
       ... = v b             : v.map_add_supp b (hJ h)
end

lemma comap_supp {S : Type*} [comm_ring S] (f : S →+* R) :
  supp (v.comap f) = ideal.comap f v.supp :=
ideal.ext $ λ x,
begin
  rw [mem_supp_iff, ideal.mem_comap, mem_supp_iff],
  refl,
end

lemma self_le_supp_comap (J : ideal R) (v : valuation (R ⧸ J) Γ₀) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
by { rw [comap_supp, ← ideal.map_le_iff_le_comap], simp }

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : valuation (R ⧸ J) Γ₀) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
ext $ by { rintro ⟨x⟩, refl }

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
  supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
begin
  apply le_antisymm,
  { rintro ⟨x⟩ hx,
    apply ideal.subset_span,
    exact ⟨x, hx, rfl⟩ },
  { rw ideal.map_le_iff_le_comap,
    intros x hx, exact hx }
end

lemma supp_quot_supp : supp (v.on_quot le_rfl) = 0 :=
by { rw supp_quot, exact ideal.map_quotient_self _ }

end supp -- end of section

end valuation

section add_monoid

variables (R) [ring R] (Γ₀ : Type*) [linear_ordered_add_comm_monoid_with_top Γ₀]

/-- The type of `Γ₀`-valued additive valuations on `R`. -/
@[nolint has_inhabited_instance]
def add_valuation := valuation R (multiplicative (order_dual Γ₀))

end add_monoid

namespace add_valuation
variables {Γ₀ : Type*} {Γ'₀ : Type*}

section basic

section monoid

variables [linear_ordered_add_comm_monoid_with_top Γ₀] [linear_ordered_add_comm_monoid_with_top Γ'₀]
variables (R) (Γ₀) [ring R]

/-- A valuation is coerced to the underlying function `R → Γ₀`. -/
instance : has_coe_to_fun (add_valuation R Γ₀) (λ _, R → Γ₀) :=
{ coe := λ v, v.to_monoid_with_zero_hom.to_fun }

variables {R} {Γ₀} (v : add_valuation R Γ₀) {x y z : R}

section

variables (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)
variables (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y)

/-- An alternate constructor of `add_valuation`, that doesn't reference
  `multiplicative (order_dual Γ₀)` -/
def of : add_valuation R Γ₀ :=
{ to_fun := f,
  map_one' := h1,
  map_zero' := h0,
  map_add_le_max' := hadd,
  map_mul' := hmul }

variables {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
theorem of_apply : (of f h0 h1 hadd hmul) r = f r := rfl

end

@[simp] lemma map_zero : v 0 = ⊤ := v.map_zero
@[simp] lemma map_one  : v 1 = 0 := v.map_one
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x + v y := v.map_mul
@[simp] lemma map_add  : ∀ x y, min (v x) (v y) ≤ v (x + y) := v.map_add

lemma map_le_add {x y g} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x + y) := v.map_add_le hx hy

lemma map_lt_add {x y g} (hx : g < v x) (hy : g < v y) : g < v (x + y) := v.map_add_lt hx hy

lemma map_le_sum {ι : Type*} {s : finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, g ≤ v (f i)) :
  g ≤ v (∑ i in s, f i) := v.map_sum_le hf

lemma map_lt_sum {ι : Type*} {s : finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ ⊤)
  (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i in s, f i) := v.map_sum_lt hg hf

lemma map_lt_sum' {ι : Type*} {s : finset ι} {f : ι → R} {g : Γ₀} (hg : g < ⊤)
  (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i in s, f i) := v.map_sum_lt' hg hf

@[simp] lemma map_pow  : ∀ x (n:ℕ), v (x^n) = n • (v x) := v.map_pow

@[ext] lemma ext {v₁ v₂ : add_valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
valuation.ext h

lemma ext_iff {v₁ v₂ : add_valuation R Γ₀} : v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
valuation.ext_iff

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.

/-- A valuation gives a preorder on the underlying ring. -/
def to_preorder : preorder R := preorder.lift v

/-- If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`. -/
@[simp] lemma top_iff [nontrivial Γ₀] {K : Type*} [division_ring K]
  (v : add_valuation K Γ₀) {x : K} : v x = ⊤ ↔ x = 0 :=
v.zero_iff

lemma ne_top_iff [nontrivial Γ₀] {K : Type*} [division_ring K]
  (v : add_valuation K Γ₀) {x : K} : v x ≠ ⊤ ↔ x ≠ 0 := v.ne_zero_iff

/-- A ring homomorphism `S → R` induces a map `add_valuation R Γ₀ → add_valuation S Γ₀`. -/
def comap {S : Type*} [ring S] (f : S →+* R) (v : add_valuation R Γ₀) :
  add_valuation S Γ₀ :=
v.comap f

@[simp] lemma comap_id : v.comap (ring_hom.id R) = v := v.comap_id

lemma comap_comp {S₁ : Type*} {S₂ : Type*} [ring S₁] [ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
  v.comap (g.comp f) = (v.comap g).comap f :=
v.comap_comp f g

/-- A `≤`-preserving, `⊤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map
  `add_valuation R Γ₀ → add_valuation R Γ'₀`.
-/
def map (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : monotone f) (v : add_valuation R Γ₀) :
  add_valuation R Γ'₀ :=
v.map
{ to_fun := f,
  map_mul' := f.map_add,
  map_one' := f.map_zero,
  map_zero' := ht } (λ x y h, hf h)

/-- Two additive valuations on `R` are defined to be equivalent if they induce the same
  preorder on `R`. -/
def is_equiv (v₁ : add_valuation R Γ₀) (v₂ : add_valuation R Γ'₀) : Prop :=
v₁.is_equiv v₂

end monoid

section group
variables [linear_ordered_add_comm_group_with_top Γ₀] [ring R] (v : add_valuation R Γ₀) {x y z : R}

@[simp] lemma map_inv {K : Type*} [division_ring K]
  (v : add_valuation K Γ₀) {x : K} : v x⁻¹ = - (v x) :=
v.map_inv

lemma map_units_inv (x : Rˣ) : v (x⁻¹ : Rˣ) = - (v x) :=
v.map_units_inv x

@[simp] lemma map_neg (x : R) : v (-x) = v x :=
v.map_neg x

lemma map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
v.map_sub_swap x y

lemma map_sub (x y : R) : min (v x) (v y) ≤ v (x - y) :=
v.map_sub x y

lemma map_le_sub {x y g} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x - y) := v.map_sub_le hx hy

lemma map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = min (v x) (v y) :=
v.map_add_of_distinct_val h

lemma map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x :=
v.map_eq_of_sub_lt h

end group

end basic

namespace is_equiv
variables [linear_ordered_add_comm_monoid_with_top Γ₀] [linear_ordered_add_comm_monoid_with_top Γ'₀]
variables [ring R]
variables {Γ''₀ : Type*} [linear_ordered_add_comm_monoid_with_top Γ''₀]
variables {v : add_valuation R Γ₀}
variables {v₁ : add_valuation R Γ₀} {v₂ : add_valuation R Γ'₀} {v₃ : add_valuation R Γ''₀}

@[refl] lemma refl : v.is_equiv v := valuation.is_equiv.refl

@[symm] lemma symm (h : v₁.is_equiv v₂) : v₂.is_equiv v₁ := h.symm

@[trans] lemma trans (h₁₂ : v₁.is_equiv v₂) (h₂₃ : v₂.is_equiv v₃) : v₁.is_equiv v₃ :=
h₁₂.trans h₂₃

lemma of_eq {v' : add_valuation R Γ₀} (h : v = v') : v.is_equiv v' :=
valuation.is_equiv.of_eq h

lemma map {v' : add_valuation R Γ₀} (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : monotone f)
  (inf : injective f) (h : v.is_equiv v') :
  (v.map f ht hf).is_equiv (v'.map f ht hf) :=
h.map
{ to_fun := f,
  map_mul' := f.map_add,
  map_one' := f.map_zero,
  map_zero' := ht } (λ x y h, hf h) inf

/-- `comap` preserves equivalence. -/
lemma comap {S : Type*} [ring S] (f : S →+* R) (h : v₁.is_equiv v₂) :
  (v₁.comap f).is_equiv (v₂.comap f) :=
h.comap f

lemma val_eq (h : v₁.is_equiv v₂) {r s : R} :
  v₁ r = v₁ s ↔ v₂ r = v₂ s :=
h.val_eq

lemma ne_top (h : v₁.is_equiv v₂) {r : R} :
  v₁ r ≠ ⊤ ↔ v₂ r ≠ ⊤ :=
h.ne_zero

end is_equiv

section supp
variables [linear_ordered_add_comm_monoid_with_top Γ₀] [linear_ordered_add_comm_monoid_with_top Γ'₀]
variables [comm_ring R]
variables (v : add_valuation R Γ₀)

/-- The support of an additive valuation `v : R → Γ₀` is the ideal of `R` where `v x = ⊤` -/
def supp : ideal R := v.supp

@[simp] lemma mem_supp_iff (x : R) : x ∈ supp v ↔ v x = ⊤ := v.mem_supp_iff x

lemma map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
v.map_add_supp a h

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def on_quot_val {J : ideal R} (hJ : J ≤ supp v) : (R ⧸ J) → Γ₀ := v.on_quot_val hJ

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def on_quot {J : ideal R} (hJ : J ≤ supp v) :
  add_valuation (R ⧸ J) Γ₀ :=
v.on_quot hJ

@[simp] lemma on_quot_comap_eq {J : ideal R} (hJ : J ≤ supp v) :
  (v.on_quot hJ).comap (ideal.quotient.mk J) = v :=
v.on_quot_comap_eq hJ

lemma comap_supp {S : Type*} [comm_ring S] (f : S →+* R) :
  supp (v.comap f) = ideal.comap f v.supp :=
v.comap_supp f

lemma self_le_supp_comap (J : ideal R) (v : add_valuation (R ⧸ J) Γ₀) :
  J ≤ (v.comap (ideal.quotient.mk J)).supp :=
v.self_le_supp_comap J

@[simp] lemma comap_on_quot_eq (J : ideal R) (v : add_valuation (R ⧸ J) Γ₀) :
  (v.comap (ideal.quotient.mk J)).on_quot (v.self_le_supp_comap J) = v :=
v.comap_on_quot_eq J

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
lemma supp_quot {J : ideal R} (hJ : J ≤ supp v) :
  supp (v.on_quot hJ) = (supp v).map (ideal.quotient.mk J) :=
v.supp_quot hJ

lemma supp_quot_supp : supp (v.on_quot le_rfl) = 0 :=
v.supp_quot_supp

end supp -- end of section

attribute [irreducible] add_valuation

end add_valuation
