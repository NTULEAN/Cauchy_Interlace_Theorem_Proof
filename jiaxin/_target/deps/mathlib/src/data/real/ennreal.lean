/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import data.real.nnreal

/-!
# Extended non-negative reals

We define `ennreal = ℝ≥0∞ := with_top ℝ≥0` to be the type of extended nonnegative real numbers,
i.e., the interval `[0, +∞]`. This type is used as the codomain of a `measure_theory.measure`,
and of the extended distance `edist` in a `emetric_space`.
In this file we define some algebraic operations and a linear order on `ℝ≥0∞`
and prove basic properties of these operations, order, and conversions to/from `ℝ`, `ℝ≥0`, and `ℕ`.

## Main definitions

* `ℝ≥0∞`: the extended nonnegative real numbers `[0, ∞]`; defined as `with_top ℝ≥0`; it is
  equipped with the following structures:

  - coercion from `ℝ≥0` defined in the natural way;

  - the natural structure of a complete dense linear order: `↑p ≤ ↑q ↔ p ≤ q` and `∀ a, a ≤ ∞`;

  - `a + b` is defined so that `↑p + ↑q = ↑(p + q)` for `(p q : ℝ≥0)` and `a + ∞ = ∞ + a = ∞`;

  - `a * b` is defined so that `↑p * ↑q = ↑(p * q)` for `(p q : ℝ≥0)`, `0 * ∞ = ∞ * 0 = 0`, and `a *
    ∞ = ∞ * a = ∞` for `a ≠ 0`;

  - `a - b` is defined as the minimal `d` such that `a ≤ d + b`; this way we have
    `↑p - ↑q = ↑(p - q)`, `∞ - ↑p = ∞`, `↑p - ∞ = ∞ - ∞ = 0`; note that there is no negation, only
    subtraction;

  - `a⁻¹` is defined as `Inf {b | 1 ≤ a * b}`. This way we have `(↑p)⁻¹ = ↑(p⁻¹)` for
    `p : ℝ≥0`, `p ≠ 0`, `0⁻¹ = ∞`, and `∞⁻¹ = 0`.

  - `a / b` is defined as `a * b⁻¹`.

  The addition and multiplication defined this way together with `0 = ↑0` and `1 = ↑1` turn
  `ℝ≥0∞` into a canonically ordered commutative semiring of characteristic zero.

* Coercions to/from other types:

  - coercion `ℝ≥0 → ℝ≥0∞` is defined as `has_coe`, so one can use `(p : ℝ≥0)` in a context that
    expects `a : ℝ≥0∞`, and Lean will apply `coe` automatically;

  - `ennreal.to_nnreal` sends `↑p` to `p` and `∞` to `0`;

  - `ennreal.to_real := coe ∘ ennreal.to_nnreal` sends `↑p`, `p : ℝ≥0` to `(↑p : ℝ)` and `∞` to `0`;

  - `ennreal.of_real := coe ∘ real.to_nnreal` sends `x : ℝ` to `↑⟨max x 0, _⟩`

  - `ennreal.ne_top_equiv_nnreal` is an equivalence between `{a : ℝ≥0∞ // a ≠ 0}` and `ℝ≥0`.

## Implementation notes

We define a `can_lift ℝ≥0∞ ℝ≥0` instance, so one of the ways to prove theorems about an `ℝ≥0∞`
number `a` is to consider the cases `a = ∞` and `a ≠ ∞`, and use the tactic `lift a to ℝ≥0 using ha`
in the second case. This instance is even more useful if one already has `ha : a ≠ ∞` in the
context, or if we have `(f : α → ℝ≥0∞) (hf : ∀ x, f x ≠ ∞)`.

## Notations

* `ℝ≥0∞`: the type of the extended nonnegative real numbers;
* `ℝ≥0`: the type of nonnegative real numbers `[0, ∞)`; defined in `data.real.nnreal`;
* `∞`: a localized notation in `ℝ≥0∞` for `⊤ : ℝ≥0∞`.

-/
open classical set

open_locale classical big_operators nnreal
variables {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
@[derive [
  has_zero, add_comm_monoid,
  canonically_ordered_comm_semiring, complete_linear_order, densely_ordered, nontrivial,
  canonically_linear_ordered_add_monoid, has_sub, has_ordered_sub,
  linear_ordered_add_comm_monoid_with_top]]
def ennreal := with_top ℝ≥0

localized "notation `ℝ≥0∞` := ennreal" in ennreal
localized "notation `∞` := (⊤ : ennreal)" in ennreal

-- TODO: why are the two covariant instances necessary? why aren't they inferred?
instance covariant_class_mul : covariant_class ℝ≥0∞ ℝ≥0∞ (*) (≤) :=
canonically_ordered_comm_semiring.to_covariant_mul_le

instance covariant_class_add : covariant_class ℝ≥0∞ ℝ≥0∞ (+) (≤) :=
ordered_add_comm_monoid.to_covariant_class_left ℝ≥0∞

namespace ennreal
variables {a b c d : ℝ≥0∞} {r p q : ℝ≥0}

instance : inhabited ℝ≥0∞ := ⟨0⟩

instance : has_coe ℝ≥0 ℝ≥0∞ := ⟨ option.some ⟩

instance : can_lift ℝ≥0∞ ℝ≥0 :=
{ coe := coe,
  cond := λ r, r ≠ ∞,
  prf := λ x hx, ⟨option.get $ option.ne_none_iff_is_some.1 hx, option.some_get _⟩ }

@[simp] lemma none_eq_top : (none : ℝ≥0∞) = ∞ := rfl
@[simp] lemma some_eq_coe (a : ℝ≥0) : (some a : ℝ≥0∞) = (↑a : ℝ≥0∞) := rfl

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def to_nnreal : ℝ≥0∞ → ℝ≥0
| (some r) := r
| none := 0

/-- `to_real x` returns `x` if it is real, `0` otherwise. -/
protected def to_real (a : ℝ≥0∞) : real := coe (a.to_nnreal)

/-- `of_real x` returns `x` if it is nonnegative, `0` otherwise. -/
protected noncomputable def of_real (r : real) : ℝ≥0∞ := coe (real.to_nnreal r)

@[simp, norm_cast] lemma to_nnreal_coe : (r : ℝ≥0∞).to_nnreal = r := rfl

@[simp] lemma coe_to_nnreal : ∀{a:ℝ≥0∞}, a ≠ ∞ → ↑(a.to_nnreal) = a
| (some r) h := rfl
| none     h := (h rfl).elim

@[simp] lemma of_real_to_real {a : ℝ≥0∞} (h : a ≠ ∞) : ennreal.of_real (a.to_real) = a :=
by simp [ennreal.to_real, ennreal.of_real, h]

@[simp] lemma to_real_of_real {r : ℝ} (h : 0 ≤ r) : ennreal.to_real (ennreal.of_real r) = r :=
by simp [ennreal.to_real, ennreal.of_real, real.coe_to_nnreal _ h]

lemma to_real_of_real' {r : ℝ} : ennreal.to_real (ennreal.of_real r) = max r 0 := rfl

lemma coe_to_nnreal_le_self : ∀{a:ℝ≥0∞}, ↑(a.to_nnreal) ≤ a
| (some r) := by rw [some_eq_coe, to_nnreal_coe]; exact le_rfl
| none     := le_top

lemma coe_nnreal_eq (r : ℝ≥0) : (r : ℝ≥0∞) = ennreal.of_real r :=
by { rw [ennreal.of_real, real.to_nnreal], cases r with r h, congr, dsimp, rw max_eq_left h }

lemma of_real_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) :
  ennreal.of_real x = @coe ℝ≥0 ℝ≥0∞ _ (⟨x, h⟩ : ℝ≥0) :=
by { rw [coe_nnreal_eq], refl }

@[simp] lemma of_real_coe_nnreal : ennreal.of_real p = p := (coe_nnreal_eq p).symm

@[simp, norm_cast] lemma coe_zero : ↑(0 : ℝ≥0) = (0 : ℝ≥0∞) := rfl
@[simp, norm_cast] lemma coe_one : ↑(1 : ℝ≥0) = (1 : ℝ≥0∞) := rfl

@[simp] lemma to_real_nonneg {a : ℝ≥0∞} : 0 ≤ a.to_real := by simp [ennreal.to_real]

@[simp] lemma top_to_nnreal : ∞.to_nnreal = 0 := rfl
@[simp] lemma top_to_real : ∞.to_real = 0 := rfl
@[simp] lemma one_to_real : (1 : ℝ≥0∞).to_real = 1 := rfl
@[simp] lemma one_to_nnreal : (1 : ℝ≥0∞).to_nnreal = 1 := rfl
@[simp] lemma coe_to_real (r : ℝ≥0) : (r : ℝ≥0∞).to_real = r := rfl
@[simp] lemma zero_to_nnreal : (0 : ℝ≥0∞).to_nnreal = 0 := rfl
@[simp] lemma zero_to_real : (0 : ℝ≥0∞).to_real = 0 := rfl
@[simp] lemma of_real_zero : ennreal.of_real (0 : ℝ) = 0 :=
by simp [ennreal.of_real]; refl
@[simp] lemma of_real_one : ennreal.of_real (1 : ℝ) = (1 : ℝ≥0∞) :=
by simp [ennreal.of_real]

lemma of_real_to_real_le {a : ℝ≥0∞} : ennreal.of_real (a.to_real) ≤ a :=
if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (of_real_to_real ha)

lemma forall_ennreal {p : ℝ≥0∞ → Prop} : (∀a, p a) ↔ (∀r:ℝ≥0, p r) ∧ p ∞ :=
⟨assume h, ⟨assume r, h _, h _⟩,
  assume ⟨h₁, h₂⟩ a, match a with some r := h₁ _ | none := h₂ end⟩

lemma forall_ne_top {p : ℝ≥0∞ → Prop} : (∀ a ≠ ∞, p a) ↔ ∀ r : ℝ≥0, p r :=
option.ball_ne_none

lemma exists_ne_top {p : ℝ≥0∞ → Prop} : (∃ a ≠ ∞, p a) ↔ ∃ r : ℝ≥0, p r :=
option.bex_ne_none

lemma to_nnreal_eq_zero_iff (x : ℝ≥0∞) : x.to_nnreal = 0 ↔ x = 0 ∨ x = ∞ :=
⟨begin
  cases x,
  { simp [none_eq_top] },
  { have A : some (0:ℝ≥0) = (0:ℝ≥0∞) := rfl,
    simp [ennreal.to_nnreal, A] {contextual := tt} }
end,
by intro h; cases h; simp [h]⟩

lemma to_real_eq_zero_iff (x : ℝ≥0∞) : x.to_real = 0 ↔ x = 0 ∨ x = ∞ :=
by simp [ennreal.to_real, to_nnreal_eq_zero_iff]

@[simp] lemma coe_ne_top : (r : ℝ≥0∞) ≠ ∞ := with_top.coe_ne_top
@[simp] lemma top_ne_coe : ∞ ≠ (r : ℝ≥0∞) := with_top.top_ne_coe
@[simp] lemma of_real_ne_top {r : ℝ} : ennreal.of_real r ≠ ∞ := by simp [ennreal.of_real]
@[simp] lemma of_real_lt_top {r : ℝ} : ennreal.of_real r < ∞ := lt_top_iff_ne_top.2 of_real_ne_top
@[simp] lemma top_ne_of_real {r : ℝ} : ∞ ≠ ennreal.of_real r := by simp [ennreal.of_real]

@[simp] lemma zero_ne_top : 0 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_zero : ∞ ≠ 0 := top_ne_coe

@[simp] lemma one_ne_top : 1 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_one : ∞ ≠ 1 := top_ne_coe

@[simp, norm_cast] lemma coe_eq_coe : (↑r : ℝ≥0∞) = ↑q ↔ r = q := with_top.coe_eq_coe
@[simp, norm_cast] lemma coe_le_coe : (↑r : ℝ≥0∞) ≤ ↑q ↔ r ≤ q := with_top.coe_le_coe
@[simp, norm_cast] lemma coe_lt_coe : (↑r : ℝ≥0∞) < ↑q ↔ r < q := with_top.coe_lt_coe
lemma coe_mono : monotone (coe : ℝ≥0 → ℝ≥0∞) := λ _ _, coe_le_coe.2

@[simp, norm_cast] lemma coe_eq_zero : (↑r : ℝ≥0∞) = 0 ↔ r = 0 := coe_eq_coe
@[simp, norm_cast] lemma zero_eq_coe : 0 = (↑r : ℝ≥0∞) ↔ 0 = r := coe_eq_coe
@[simp, norm_cast] lemma coe_eq_one : (↑r : ℝ≥0∞) = 1 ↔ r = 1 := coe_eq_coe
@[simp, norm_cast] lemma one_eq_coe : 1 = (↑r : ℝ≥0∞) ↔ 1 = r := coe_eq_coe
@[simp, norm_cast] lemma coe_nonneg : 0 ≤ (↑r : ℝ≥0∞) ↔ 0 ≤ r := coe_le_coe
@[simp, norm_cast] lemma coe_pos : 0 < (↑r : ℝ≥0∞) ↔ 0 < r := coe_lt_coe
lemma coe_ne_zero : (r : ℝ≥0∞) ≠ 0 ↔ r ≠ 0 := not_congr coe_eq_coe


@[simp, norm_cast] lemma coe_add : ↑(r + p) = (r + p : ℝ≥0∞) := with_top.coe_add
@[simp, norm_cast] lemma coe_mul : ↑(r * p) = (r * p : ℝ≥0∞) := with_top.coe_mul

@[simp, norm_cast] lemma coe_bit0 : (↑(bit0 r) : ℝ≥0∞) = bit0 r := coe_add
@[simp, norm_cast] lemma coe_bit1 : (↑(bit1 r) : ℝ≥0∞) = bit1 r := by simp [bit1]
lemma coe_two : ((2:ℝ≥0) : ℝ≥0∞) = 2 := by norm_cast

protected lemma zero_lt_one : 0 < (1 : ℝ≥0∞) :=
  canonically_ordered_comm_semiring.zero_lt_one

@[simp] lemma one_lt_two : (1 : ℝ≥0∞) < 2 :=
coe_one ▸ coe_two ▸ by exact_mod_cast (@one_lt_two ℕ _ _)
@[simp] lemma zero_lt_two : (0:ℝ≥0∞) < 2 := lt_trans ennreal.zero_lt_one one_lt_two
lemma two_ne_zero : (2:ℝ≥0∞) ≠ 0 := (ne_of_lt zero_lt_two).symm
lemma two_ne_top : (2:ℝ≥0∞) ≠ ∞ := coe_two ▸ coe_ne_top

/-- `(1 : ℝ≥0∞) ≤ 1`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_one_ennreal : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩

/-- `(1 : ℝ≥0∞) ≤ 2`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_two_ennreal : fact ((1 : ℝ≥0∞) ≤ 2) :=
⟨ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num)⟩

/-- `(1 : ℝ≥0∞) ≤ ∞`, recorded as a `fact` for use with `Lp` spaces. -/
instance _root_.fact_one_le_top_ennreal : fact ((1 : ℝ≥0∞) ≤ ∞) := ⟨le_top⟩

/-- The set of numbers in `ℝ≥0∞` that are not equal to `∞` is equivalent to `ℝ≥0`. -/
def ne_top_equiv_nnreal : {a | a ≠ ∞} ≃ ℝ≥0 :=
{ to_fun := λ x, ennreal.to_nnreal x,
  inv_fun := λ x, ⟨x, coe_ne_top⟩,
  left_inv := λ ⟨x, hx⟩, subtype.eq $ coe_to_nnreal hx,
  right_inv := λ x, to_nnreal_coe }

lemma cinfi_ne_top [has_Inf α] (f : ℝ≥0∞ → α) : (⨅ x : {x // x ≠ ∞}, f x) = ⨅ x : ℝ≥0, f x :=
eq.symm $ infi_congr _ ne_top_equiv_nnreal.symm.surjective $ λ x, rfl

lemma infi_ne_top [complete_lattice α] (f : ℝ≥0∞ → α) : (⨅ x ≠ ∞, f x) = ⨅ x : ℝ≥0, f x :=
by rw [infi_subtype', cinfi_ne_top]

lemma csupr_ne_top [has_Sup α] (f : ℝ≥0∞ → α) : (⨆ x : {x // x ≠ ∞}, f x) = ⨆ x : ℝ≥0, f x :=
@cinfi_ne_top (order_dual α) _ _

lemma supr_ne_top [complete_lattice α] (f : ℝ≥0∞ → α) : (⨆ x ≠ ∞, f x) = ⨆ x : ℝ≥0, f x :=
@infi_ne_top (order_dual α) _ _

lemma infi_ennreal {α : Type*} [complete_lattice α] {f : ℝ≥0∞ → α} :
  (⨅ n, f n) = (⨅ n : ℝ≥0, f n) ⊓ f ∞ :=
le_antisymm
  (le_inf (le_infi $ assume i, infi_le _ _) (infi_le _ _))
  (le_infi $ forall_ennreal.2 ⟨λ r, inf_le_of_left_le $ infi_le _ _, inf_le_right⟩)

lemma supr_ennreal {α : Type*} [complete_lattice α] {f : ℝ≥0∞ → α} :
  (⨆ n, f n) = (⨆ n : ℝ≥0, f n) ⊔ f ∞ :=
@infi_ennreal (order_dual α) _ _

@[simp] lemma add_top : a + ∞ = ∞ := add_top _
@[simp] lemma top_add : ∞ + a = ∞ := top_add _

/-- Coercion `ℝ≥0 → ℝ≥0∞` as a `ring_hom`. -/
noncomputable def of_nnreal_hom : ℝ≥0 →+* ℝ≥0∞ :=
⟨coe, coe_one, λ _ _, coe_mul, coe_zero, λ _ _, coe_add⟩

@[simp] lemma coe_of_nnreal_hom : ⇑of_nnreal_hom = coe := rfl

section actions

/-- A `mul_action` over `ℝ≥0∞` restricts to a `mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [mul_action ℝ≥0∞ M] : mul_action ℝ≥0 M :=
mul_action.comp_hom M of_nnreal_hom.to_monoid_hom

lemma smul_def {M : Type*} [mul_action ℝ≥0∞ M] (c : ℝ≥0) (x : M) :
  c • x = (c : ℝ≥0∞) • x := rfl

instance {M N : Type*} [mul_action ℝ≥0∞ M] [mul_action ℝ≥0∞ N] [has_scalar M N]
  [is_scalar_tower ℝ≥0∞ M N] : is_scalar_tower ℝ≥0 M N :=
{ smul_assoc := λ r, (smul_assoc (r : ℝ≥0∞) : _)}

instance smul_comm_class_left {M N : Type*} [mul_action ℝ≥0∞ N] [has_scalar M N]
  [smul_comm_class ℝ≥0∞ M N] : smul_comm_class ℝ≥0 M N :=
{ smul_comm := λ r, (smul_comm (r : ℝ≥0∞) : _)}

instance smul_comm_class_right {M N : Type*} [mul_action ℝ≥0∞ N] [has_scalar M N]
  [smul_comm_class M ℝ≥0∞ N] : smul_comm_class M ℝ≥0 N :=
{ smul_comm := λ m r, (smul_comm m (r : ℝ≥0∞) : _)}

/-- A `distrib_mul_action` over `ℝ≥0∞` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [add_monoid M] [distrib_mul_action ℝ≥0∞ M] :
  distrib_mul_action ℝ≥0 M :=
distrib_mul_action.comp_hom M of_nnreal_hom.to_monoid_hom

/-- A `module` over `ℝ≥0∞` restricts to a `module` over `ℝ≥0`. -/
noncomputable instance {M : Type*} [add_comm_monoid M] [module ℝ≥0∞ M] : module ℝ≥0 M :=
module.comp_hom M of_nnreal_hom

/-- An `algebra` over `ℝ≥0∞` restricts to an `algebra` over `ℝ≥0`. -/
noncomputable instance {A : Type*} [semiring A] [algebra ℝ≥0∞ A] : algebra ℝ≥0 A :=
{ smul := (•),
  commutes' := λ r x, by simp [algebra.commutes],
  smul_def' := λ r x, by simp [←algebra.smul_def (r : ℝ≥0∞) x, smul_def],
  to_ring_hom := ((algebra_map ℝ≥0∞ A).comp (of_nnreal_hom : ℝ≥0 →+* ℝ≥0∞)) }

-- verify that the above produces instances we might care about
noncomputable example : algebra ℝ≥0 ℝ≥0∞ := by apply_instance
noncomputable example : distrib_mul_action ℝ≥0ˣ ℝ≥0∞ := by apply_instance

lemma coe_smul {R} (r : R) (s : ℝ≥0) [has_scalar R ℝ≥0] [has_scalar R ℝ≥0∞]
  [is_scalar_tower R ℝ≥0 ℝ≥0] [is_scalar_tower R ℝ≥0 ℝ≥0∞] :
  (↑(r • s) : ℝ≥0∞) = r • ↑s :=
by rw [←smul_one_smul ℝ≥0 r (s: ℝ≥0∞), smul_def, smul_eq_mul, ←ennreal.coe_mul, smul_mul_assoc,
    one_mul]

end actions

@[simp, norm_cast] lemma coe_indicator {α} (s : set α) (f : α → ℝ≥0) (a : α) :
  ((s.indicator f a : ℝ≥0) : ℝ≥0∞) = s.indicator (λ x, f x) a :=
(of_nnreal_hom : ℝ≥0 →+ ℝ≥0∞).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (n : ℕ) : (↑(r^n) : ℝ≥0∞) = r^n :=
of_nnreal_hom.map_pow r n

@[simp] lemma add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := with_top.add_eq_top
@[simp] lemma add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := with_top.add_lt_top

lemma to_nnreal_add {r₁ r₂ : ℝ≥0∞} (h₁ : r₁ ≠ ∞) (h₂ : r₂ ≠ ∞) :
  (r₁ + r₂).to_nnreal = r₁.to_nnreal + r₂.to_nnreal :=
by { lift r₁ to ℝ≥0 using h₁, lift r₂ to ℝ≥0 using h₂, refl }

lemma not_lt_top {x : ℝ≥0∞} : ¬ x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, not_not]

lemma add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ :=
by simpa only [lt_top_iff_ne_top] using add_lt_top

lemma mul_top : a * ∞ = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.mul_top h } end

lemma top_mul : ∞ * a = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.top_mul h } end

@[simp] lemma top_mul_top : ∞ * ∞ = ∞ := with_top.top_mul_top

lemma top_pow {n:ℕ} (h : 0 < n) : ∞^n = ∞ :=
nat.le_induction (pow_one _) (λ m hm hm', by rw [pow_succ, hm', top_mul_top])
  _ (nat.succ_le_of_lt h)

lemma mul_eq_top : a * b = ∞ ↔ (a ≠ 0 ∧ b = ∞) ∨ (a = ∞ ∧ b ≠ 0) :=
with_top.mul_eq_top_iff

lemma mul_lt_top  : a ≠ ∞ → b ≠ ∞ → a * b < ∞ :=
with_top.mul_lt_top

lemma mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ :=
by simpa only [lt_top_iff_ne_top] using mul_lt_top

lemma lt_top_of_mul_ne_top_left (h : a * b ≠ ∞) (hb : b ≠ 0) : a < ∞ :=
lt_top_iff_ne_top.2 $ λ ha, h $ mul_eq_top.2 (or.inr ⟨ha, hb⟩)

lemma lt_top_of_mul_ne_top_right (h : a * b ≠ ∞) (ha : a ≠ 0) : b < ∞ :=
lt_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

lemma mul_lt_top_iff {a b : ℝ≥0∞} : a * b < ∞ ↔ (a < ∞ ∧ b < ∞) ∨ a = 0 ∨ b = 0 :=
begin
  split,
  { intro h, rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right], intros hb ha,
    exact ⟨lt_top_of_mul_ne_top_left h.ne hb, lt_top_of_mul_ne_top_right h.ne ha⟩ },
  { rintro (⟨ha, hb⟩|rfl|rfl); [exact mul_lt_top ha.ne hb.ne, simp, simp] }
end

lemma mul_self_lt_top_iff {a : ℝ≥0∞} : a * a < ⊤ ↔ a < ⊤ :=
by { rw [ennreal.mul_lt_top_iff, and_self, or_self, or_iff_left_iff_imp], rintro rfl, norm_num }

lemma mul_pos_iff : 0 < a * b ↔ 0 < a ∧ 0 < b := canonically_ordered_comm_semiring.mul_pos

lemma mul_pos (ha : a ≠ 0) (hb : b ≠ 0) : 0 < a * b :=
mul_pos_iff.2 ⟨pos_iff_ne_zero.2 ha, pos_iff_ne_zero.2 hb⟩

@[simp] lemma pow_eq_top_iff {n : ℕ} : a ^ n = ∞ ↔ a = ∞ ∧ n ≠ 0 :=
begin
  induction n with n ihn, { simp },
  rw [pow_succ, mul_eq_top, ihn],
  fsplit,
  { rintro (⟨-,rfl,h0⟩|⟨rfl,h0⟩); exact ⟨rfl, n.succ_ne_zero⟩ },
  { rintro ⟨rfl, -⟩, exact or.inr ⟨rfl, pow_ne_zero n top_ne_zero⟩ }
end

lemma pow_eq_top (n : ℕ) (h : a ^ n = ∞) : a = ∞ :=
(pow_eq_top_iff.1 h).1

lemma pow_ne_top (h : a ≠ ∞) {n:ℕ} : a^n ≠ ∞ :=
mt (pow_eq_top n) h

lemma pow_lt_top : a < ∞ → ∀ n:ℕ, a^n < ∞ :=
by simpa only [lt_top_iff_ne_top] using pow_ne_top

@[simp, norm_cast] lemma coe_finset_sum {s : finset α} {f : α → ℝ≥0} :
  ↑(∑ a in s, f a) = (∑ a in s, f a : ℝ≥0∞) :=
of_nnreal_hom.map_sum f s

@[simp, norm_cast] lemma coe_finset_prod {s : finset α} {f : α → ℝ≥0} :
  ↑(∏ a in s, f a) = ((∏ a in s, f a) : ℝ≥0∞) :=
of_nnreal_hom.map_prod f s

section order

@[simp] lemma bot_eq_zero : (⊥ : ℝ≥0∞) = 0 := rfl

@[simp] lemma coe_lt_top : coe r < ∞ := with_top.coe_lt_top r
@[simp] lemma not_top_le_coe : ¬ ∞ ≤ ↑r := with_top.not_top_le_coe r
@[simp, norm_cast] lemma one_le_coe_iff : (1:ℝ≥0∞) ≤ ↑r ↔ 1 ≤ r := coe_le_coe
@[simp, norm_cast] lemma coe_le_one_iff : ↑r ≤ (1:ℝ≥0∞) ↔ r ≤ 1 := coe_le_coe
@[simp, norm_cast] lemma coe_lt_one_iff : (↑p : ℝ≥0∞) < 1 ↔ p < 1 := coe_lt_coe
@[simp, norm_cast] lemma one_lt_coe_iff : 1 < (↑p : ℝ≥0∞) ↔ 1 < p := coe_lt_coe
@[simp, norm_cast] lemma coe_nat (n : ℕ) : ((n : ℝ≥0) : ℝ≥0∞) = n := with_top.coe_nat n
@[simp] lemma of_real_coe_nat (n : ℕ) : ennreal.of_real n = n := by simp [ennreal.of_real]
@[simp] lemma nat_ne_top (n : ℕ) : (n : ℝ≥0∞) ≠ ∞ := with_top.nat_ne_top n
@[simp] lemma top_ne_nat (n : ℕ) : ∞ ≠ n := with_top.top_ne_nat n
@[simp] lemma one_lt_top : 1 < ∞ := coe_lt_top

@[simp, norm_cast] lemma to_nnreal_nat (n : ℕ) : (n : ℝ≥0∞).to_nnreal = n :=
by conv_lhs { rw [← ennreal.coe_nat n, ennreal.to_nnreal_coe] }

@[simp, norm_cast] lemma to_real_nat (n : ℕ) : (n : ℝ≥0∞).to_real = n :=
by conv_lhs { rw [← ennreal.of_real_coe_nat n, ennreal.to_real_of_real (nat.cast_nonneg _)] }

lemma le_coe_iff : a ≤ ↑r ↔ (∃p:ℝ≥0, a = p ∧ p ≤ r) := with_top.le_coe_iff
lemma coe_le_iff : ↑r ≤ a ↔ (∀p:ℝ≥0, a = p → r ≤ p) := with_top.coe_le_iff

lemma lt_iff_exists_coe : a < b ↔ (∃p:ℝ≥0, a = p ∧ ↑p < b) := with_top.lt_iff_exists_coe

lemma to_real_le_coe_of_le_coe {a : ℝ≥0∞} {b : ℝ≥0} (h : a ≤ b) : a.to_real ≤ b :=
show ↑a.to_nnreal ≤ ↑b,
begin
  have : ↑a.to_nnreal = a := ennreal.coe_to_nnreal (lt_of_le_of_lt h coe_lt_top).ne,
  rw ← this at h,
  exact_mod_cast h
end

@[simp, norm_cast] lemma coe_finset_sup {s : finset α} {f : α → ℝ≥0} :
  ↑(s.sup f) = s.sup (λ x, (f x : ℝ≥0∞)) :=
finset.comp_sup_eq_sup_comp_of_is_total _ coe_mono rfl

lemma pow_le_pow {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
begin
  cases a,
  { cases m,
    { rw eq_bot_iff.mpr h,
      exact le_rfl },
    { rw [none_eq_top, top_pow (nat.succ_pos m)],
      exact le_top } },
  { rw [some_eq_coe, ← coe_pow, ← coe_pow, coe_le_coe],
    exact pow_le_pow (by simpa using ha) h }
end

lemma one_le_pow_of_one_le (ha : 1 ≤ a) (n : ℕ) : 1 ≤ a ^ n :=
by simpa using pow_le_pow ha (zero_le n)

@[simp] lemma max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 :=
by simp only [nonpos_iff_eq_zero.symm, max_le_iff]

@[simp] lemma max_zero_left : max 0 a = a := max_eq_right (zero_le a)
@[simp] lemma max_zero_right : max a 0 = a := max_eq_left (zero_le a)

@[simp] lemma sup_eq_max : a ⊔ b = max a b :=
rfl

protected lemma pow_pos : 0 < a → ∀ n : ℕ, 0 < a^n :=
canonically_ordered_comm_semiring.pow_pos

protected lemma pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a^n ≠ 0 :=
by simpa only [pos_iff_ne_zero] using ennreal.pow_pos

@[simp] lemma not_lt_zero : ¬ a < 0 := by simp

lemma add_lt_add_iff_left (ha : a ≠ ∞) : a + c < a + b ↔ c < b :=
with_top.add_lt_add_iff_left ha

lemma add_lt_add_left (ha : a ≠ ∞) (h : b < c) : a + b < a + c :=
(add_lt_add_iff_left ha).2 h

lemma add_lt_add_iff_right (ha : a ≠ ∞) : c + a < b + a ↔ c < b :=
with_top.add_lt_add_iff_right ha

lemma add_lt_add_right (ha : a ≠ ∞) (h : b < c) : b + a < c + a :=
(add_lt_add_iff_right ha).2 h

instance contravariant_class_add_lt : contravariant_class ℝ≥0∞ ℝ≥0∞ (+) (<) :=
with_top.contravariant_class_add_lt

lemma lt_add_right (ha : a ≠ ∞) (hb : b ≠ 0) : a < a + b :=
by rwa [← pos_iff_ne_zero, ← add_lt_add_iff_left ha, add_zero] at hb

lemma le_of_forall_pos_le_add : ∀{a b : ℝ≥0∞}, (∀ε : ℝ≥0, 0 < ε → b < ∞ → a ≤ b + ε) → a ≤ b
| a    none     h := le_top
| none (some a) h :=
  have ∞ ≤ ↑a + ↑(1:ℝ≥0), from h 1 zero_lt_one coe_lt_top,
  by rw [← coe_add] at this; exact (not_top_le_coe this).elim
| (some a) (some b) h :=
    by simp only [none_eq_top, some_eq_coe, coe_add.symm, coe_le_coe, coe_lt_top, true_implies_iff]
      at *; exact nnreal.le_of_forall_pos_le_add h

lemma lt_iff_exists_rat_btwn :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < real.to_nnreal q ∧ (real.to_nnreal q:ℝ≥0∞) < b) :=
⟨λ h,
  begin
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩,
    rcases exists_between h with ⟨c, pc, cb⟩,
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩,
    rcases (nnreal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩,
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩
  end,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

lemma lt_iff_exists_real_btwn :
  a < b ↔ (∃r:ℝ, 0 ≤ r ∧ a < ennreal.of_real r ∧ (ennreal.of_real r:ℝ≥0∞) < b) :=
⟨λ h, let ⟨q, q0, aq, qb⟩ := ennreal.lt_iff_exists_rat_btwn.1 h in
  ⟨q, rat.cast_nonneg.2 q0, aq, qb⟩,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

lemma lt_iff_exists_nnreal_btwn :
  a < b ↔ (∃r:ℝ≥0, a < r ∧ (r : ℝ≥0∞) < b) :=
with_top.lt_iff_exists_coe_btwn

lemma lt_iff_exists_add_pos_lt : a < b ↔ (∃ r : ℝ≥0, 0 < r ∧ a + r < b) :=
begin
  refine ⟨λ hab, _, λ ⟨r, rpos, hr⟩, lt_of_le_of_lt (le_self_add) hr⟩,
  cases a, { simpa using hab },
  rcases lt_iff_exists_real_btwn.1 hab with ⟨c, c_nonneg, ac, cb⟩,
  let d : ℝ≥0 := ⟨c, c_nonneg⟩,
  have ad : a < d,
  { rw of_real_eq_coe_nnreal c_nonneg at ac,
    exact coe_lt_coe.1 ac },
  refine ⟨d-a, tsub_pos_iff_lt.2 ad, _⟩,
  rw [some_eq_coe, ← coe_add],
  convert cb,
  have : real.to_nnreal c = d,
    by { rw [← nnreal.coe_eq, real.coe_to_nnreal _ c_nonneg], refl },
  rw [add_comm, this],
  exact tsub_add_cancel_of_le ad.le
end

lemma coe_nat_lt_coe {n : ℕ} : (n : ℝ≥0∞) < r ↔ ↑n < r := ennreal.coe_nat n ▸ coe_lt_coe
lemma coe_lt_coe_nat {n : ℕ} : (r : ℝ≥0∞) < n ↔ r < n := ennreal.coe_nat n ▸ coe_lt_coe
@[simp, norm_cast] lemma coe_nat_lt_coe_nat {m n : ℕ} : (m : ℝ≥0∞) < n ↔ m < n :=
ennreal.coe_nat n ▸ coe_nat_lt_coe.trans nat.cast_lt
lemma coe_nat_ne_top {n : ℕ} : (n : ℝ≥0∞) ≠ ∞ := ennreal.coe_nat n ▸ coe_ne_top
lemma coe_nat_mono : strict_mono (coe : ℕ → ℝ≥0∞) := λ _ _, coe_nat_lt_coe_nat.2
@[simp, norm_cast] lemma coe_nat_le_coe_nat {m n : ℕ} : (m : ℝ≥0∞) ≤ n ↔ m ≤ n :=
coe_nat_mono.le_iff_le

instance : char_zero ℝ≥0∞ := ⟨coe_nat_mono.injective⟩

protected lemma exists_nat_gt {r : ℝ≥0∞} (h : r ≠ ∞) : ∃n:ℕ, r < n :=
begin
  lift r to ℝ≥0 using h,
  rcases exists_nat_gt r with ⟨n, hn⟩,
  exact ⟨n, coe_lt_coe_nat.2 hn⟩,
end

lemma add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d :=
begin
  lift a to ℝ≥0 using ne_top_of_lt ac,
  lift b to ℝ≥0 using ne_top_of_lt bd,
  cases c, { simp }, cases d, { simp },
  simp only [← coe_add, some_eq_coe, coe_lt_coe] at *,
  exact add_lt_add ac bd
end

@[norm_cast] lemma coe_min : ((min r p:ℝ≥0):ℝ≥0∞) = min r p :=
coe_mono.map_min

@[norm_cast] lemma coe_max : ((max r p:ℝ≥0):ℝ≥0∞) = max r p :=
coe_mono.map_max

lemma le_of_top_imp_top_of_to_nnreal_le {a b : ℝ≥0∞} (h : a = ⊤ → b = ⊤)
  (h_nnreal : a ≠ ⊤ → b ≠ ⊤ → a.to_nnreal ≤ b.to_nnreal) :
  a ≤ b :=
begin
  by_cases ha : a = ⊤,
  { rw h ha,
    exact le_top, },
  by_cases hb : b = ⊤,
  { rw hb,
    exact le_top, },
  rw [←coe_to_nnreal hb, ←coe_to_nnreal ha, coe_le_coe],
  exact h_nnreal ha hb,
end

end order

section complete_lattice

lemma coe_Sup {s : set ℝ≥0} : bdd_above s → (↑(Sup s) : ℝ≥0∞) = (⨆a∈s, ↑a) := with_top.coe_Sup
lemma coe_Inf {s : set ℝ≥0} : s.nonempty → (↑(Inf s) : ℝ≥0∞) = (⨅a∈s, ↑a) := with_top.coe_Inf

@[simp] lemma top_mem_upper_bounds {s : set ℝ≥0∞} : ∞ ∈ upper_bounds s :=
assume x hx, le_top

lemma coe_mem_upper_bounds {s : set ℝ≥0} :
  ↑r ∈ upper_bounds ((coe : ℝ≥0 → ℝ≥0∞) '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, -mem_image, *] {contextual := tt}

end complete_lattice

/-- `le_of_add_le_add_left` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds in `ℝ≥0∞` with the additional assumption that `a ≠ ∞`. -/
lemma le_of_add_le_add_left {a b c : ℝ≥0∞} (ha : a ≠ ∞) :
  a + b ≤ a + c → b ≤ c :=
begin
  lift a to ℝ≥0 using ha,
  cases b; cases c; simp [← ennreal.coe_add, ennreal.coe_le_coe]
end

/-- `le_of_add_le_add_right` is normally applicable to `ordered_cancel_add_comm_monoid`,
but it holds in `ℝ≥0∞` with the additional assumption that `a ≠ ∞`. -/
lemma le_of_add_le_add_right {a b c : ℝ≥0∞} : a ≠ ∞ →
  b + a ≤ c + a → b ≤ c :=
by simpa only [add_comm _ a] using le_of_add_le_add_left

section mul

@[mono] lemma mul_le_mul : a ≤ b → c ≤ d → a * c ≤ b * d :=
mul_le_mul'

@[mono] lemma mul_lt_mul (ac : a < c) (bd : b < d) : a * b < c * d :=
begin
  rcases lt_iff_exists_nnreal_btwn.1 ac with ⟨a', aa', a'c⟩,
  lift a to ℝ≥0 using ne_top_of_lt aa',
  rcases lt_iff_exists_nnreal_btwn.1 bd with ⟨b', bb', b'd⟩,
  lift b to ℝ≥0 using ne_top_of_lt bb',
  norm_cast at *,
  calc ↑(a * b) < ↑(a' * b') :
    coe_lt_coe.2 (mul_lt_mul' aa'.le bb' (zero_le _) ((zero_le a).trans_lt aa'))
  ... = ↑a' * ↑b' : coe_mul
  ... ≤ c * d : mul_le_mul a'c.le b'd.le
end

lemma mul_left_mono : monotone ((*) a) := λ b c, mul_le_mul (le_refl a)

lemma mul_right_mono : monotone (λ x, x * a) := λ b c h, mul_le_mul h (le_refl a)

lemma pow_strict_mono {n : ℕ} (hn : n ≠ 0) : strict_mono (λ (x : ℝ≥0∞), x^n) :=
begin
  assume x y hxy,
  obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn,
  induction n with n IH,
  { simp only [hxy, pow_one] },
  { simp only [pow_succ _ n.succ, mul_lt_mul hxy (IH (nat.succ_pos _).ne')] }
end

lemma max_mul : max a b * c = max (a * c) (b * c) :=
mul_right_mono.map_max

lemma mul_max : a * max b c = max (a * b) (a * c) :=
mul_left_mono.map_max

lemma mul_eq_mul_left : a ≠ 0 → a ≠ ∞ → (a * b = a * c ↔ b = c) :=
begin
  cases a; cases b; cases c;
    simp [none_eq_top, some_eq_coe, mul_top, top_mul, -coe_mul, coe_mul.symm,
      nnreal.mul_eq_mul_left] {contextual := tt},
end

lemma mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left

lemma mul_le_mul_left : a ≠ 0 → a ≠ ∞ → (a * b ≤ a * c ↔ b ≤ c) :=
begin
  cases a; cases b; cases c;
    simp [none_eq_top, some_eq_coe, mul_top, top_mul, -coe_mul, coe_mul.symm] {contextual := tt},
  assume h, exact mul_le_mul_left (pos_iff_ne_zero.2 h)
end

lemma mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

lemma mul_lt_mul_left : a ≠ 0 → a ≠ ∞ → (a * b < a * c ↔ b < c) :=
λ h0 ht, by simp only [mul_le_mul_left h0 ht, lt_iff_le_not_le]

lemma mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left

end mul

section cancel
/-- An element `a` is `add_le_cancellable` if `a + b ≤ a + c` implies `b ≤ c` for all `b` and `c`.
  This is true in `ℝ≥0∞` for all elements except `∞`. -/
lemma add_le_cancellable_iff_ne {a : ℝ≥0∞} : add_le_cancellable a ↔ a ≠ ∞ :=
begin
  split,
  { rintro h rfl, refine ennreal.zero_lt_one.not_le (h _), simp, },
  { rintro h b c hbc, apply ennreal.le_of_add_le_add_left h hbc }
end

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_of_ne {a : ℝ≥0∞} (h : a ≠ ∞) : add_le_cancellable a :=
add_le_cancellable_iff_ne.mpr h

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_of_lt {a : ℝ≥0∞} (h : a < ∞) : add_le_cancellable a :=
cancel_of_ne h.ne

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_of_lt' {a b : ℝ≥0∞} (h : a < b) : add_le_cancellable a :=
cancel_of_ne h.ne_top

/-- This lemma has an abbreviated name because it is used frequently. -/
lemma cancel_coe {a : ℝ≥0} : add_le_cancellable (a : ℝ≥0∞) :=
cancel_of_ne coe_ne_top

lemma add_right_inj (h : a ≠ ∞) : a + b = a + c ↔ b = c :=
(cancel_of_ne h).inj

lemma add_left_inj (h : a ≠ ∞) : b + a = c + a ↔ b = c :=
(cancel_of_ne h).inj_left

end cancel

section sub

lemma sub_eq_Inf {a b : ℝ≥0∞} : a - b = Inf {d | a ≤ d + b} :=
le_antisymm (le_Inf $ λ c, tsub_le_iff_right.mpr) $ Inf_le le_tsub_add

/-- This is a special case of `with_top.coe_sub` in the `ennreal` namespace -/
lemma coe_sub : (↑(r - p) : ℝ≥0∞) = ↑r - ↑p :=
by simp

/-- This is a special case of `with_top.top_sub_coe` in the `ennreal` namespace -/
lemma top_sub_coe : ∞ - ↑r = ∞ :=
by simp

/-- This is a special case of `with_top.sub_top` in the `ennreal` namespace -/
lemma sub_top : a - ∞ = 0 :=
by simp

lemma sub_eq_top_iff : a - b = ∞ ↔ a = ∞ ∧ b ≠ ∞ :=
by { cases a; cases b; simp [← with_top.coe_sub] }

lemma sub_ne_top (ha : a ≠ ∞) : a - b ≠ ∞ :=
mt sub_eq_top_iff.mp $ mt and.left ha

protected lemma sub_lt_of_lt_add (hac : c ≤ a) (h : a < b + c) : a - c < b :=
((cancel_of_lt' $ hac.trans_lt h).tsub_lt_iff_right hac).mpr h

@[simp] lemma add_sub_self (hb : b ≠ ∞) : (a + b) - b = a :=
(cancel_of_ne hb).add_tsub_cancel_right

@[simp] lemma add_sub_self' (ha : a ≠ ∞) : (a + b) - a = b :=
(cancel_of_ne ha).add_tsub_cancel_left

lemma sub_eq_of_add_eq (hb : b ≠ ∞) (hc : a + b = c) : c - b = a :=
(cancel_of_ne hb).tsub_eq_of_eq_add hc.symm

protected lemma lt_add_of_sub_lt (ht : a ≠ ∞ ∨ b ≠ ∞) (h : a - b < c) : a < c + b :=
begin
  rcases eq_or_ne b ∞ with rfl|hb,
  { rw [add_top, lt_top_iff_ne_top], exact ht.resolve_right (not_not.2 rfl) },
  { exact (cancel_of_ne hb).lt_add_of_tsub_lt_right h }
end

protected lemma sub_lt_iff_lt_add (hb : b ≠ ∞) (hab : b ≤ a) : a - b < c ↔ a < c + b :=
(cancel_of_ne hb).tsub_lt_iff_right hab

protected lemma sub_lt_self (hat : a ≠ ∞) (ha0 : a ≠ 0) (hb : b ≠ 0) : a - b < a :=
begin
  cases b, { simp [pos_iff_ne_zero, ha0] },
  exact (cancel_of_ne hat).tsub_lt_self cancel_coe (pos_iff_ne_zero.mpr ha0)
    (pos_iff_ne_zero.mpr hb)
end

lemma sub_lt_of_sub_lt (h₂ : c ≤ a) (h₃ : a ≠ ∞ ∨ b ≠ ∞) (h₁ : a - b < c) : a - c < b :=
ennreal.sub_lt_of_lt_add h₂ (add_comm c b ▸ ennreal.lt_add_of_sub_lt h₃ h₁)

lemma sub_sub_cancel (h : a ≠ ∞) (h2 : b ≤ a) : a - (a - b) = b :=
(cancel_of_ne $ sub_ne_top h).tsub_tsub_cancel_of_le h2

lemma sub_right_inj {a b c : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≤ a) (hc : c ≤ a) :
  a - b = a - c ↔ b = c :=
(cancel_of_ne ha).tsub_right_inj (cancel_of_ne $ ne_top_of_le_ne_top ha hb)
  (cancel_of_ne $ ne_top_of_le_ne_top ha hc) hb hc

lemma sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c :=
begin
  cases le_or_lt a b with hab hab, { simp [hab, mul_right_mono hab] },
  rcases eq_or_lt_of_le (zero_le b) with rfl|hb, { simp },
  exact (cancel_of_ne $ mul_ne_top hab.ne_top (h hb hab)).tsub_mul
end

lemma mul_sub (h : 0 < c → c < b → a ≠ ∞) : a * (b - c) = a * b - a * c :=
by { simp only [mul_comm a], exact sub_mul h }

end sub

section sum

open finset

/-- A product of finite numbers is still finite -/
lemma prod_lt_top {s : finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : (∏ a in s, f a) < ∞ :=
with_top.prod_lt_top h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top {s : finset α} {f : α → ℝ≥0∞} (h : ∀ a ∈ s, f a ≠ ∞) : ∑ a in s, f a < ∞ :=
with_top.sum_lt_top h

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top_iff {s : finset α} {f : α → ℝ≥0∞} :
  ∑ a in s, f a < ∞ ↔ (∀ a ∈ s, f a < ∞) :=
with_top.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
lemma sum_eq_top_iff {s : finset α} {f : α → ℝ≥0∞} :
  (∑ x in s, f x) = ∞ ↔ (∃ a ∈ s, f a = ∞) :=
with_top.sum_eq_top_iff

lemma lt_top_of_sum_ne_top {s : finset α} {f : α → ℝ≥0∞} (h : (∑ x in s, f x) ≠ ∞) {a : α}
  (ha : a ∈ s) : f a < ∞ :=
sum_lt_top_iff.1 h.lt_top a ha

/-- seeing `ℝ≥0∞` as `ℝ≥0` does not change their sum, unless one of the `ℝ≥0∞` is
infinity -/
lemma to_nnreal_sum {s : finset α} {f : α → ℝ≥0∞} (hf : ∀a∈s, f a ≠ ∞) :
  ennreal.to_nnreal (∑ a in s, f a) = ∑ a in s, ennreal.to_nnreal (f a) :=
begin
  rw [← coe_eq_coe, coe_to_nnreal, coe_finset_sum, sum_congr rfl],
  { intros x hx, exact (coe_to_nnreal (hf x hx)).symm },
  { exact (sum_lt_top hf).ne }
end

/-- seeing `ℝ≥0∞` as `real` does not change their sum, unless one of the `ℝ≥0∞` is infinity -/
lemma to_real_sum {s : finset α} {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, f a ≠ ∞) :
  ennreal.to_real (∑ a in s, f a) = ∑ a in s, ennreal.to_real (f a) :=
by { rw [ennreal.to_real, to_nnreal_sum hf, nnreal.coe_sum], refl }

lemma of_real_sum_of_nonneg {s : finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
  ennreal.of_real (∑ i in s, f i) = ∑ i in s, ennreal.of_real (f i) :=
begin
  simp_rw [ennreal.of_real, ←coe_finset_sum, coe_eq_coe],
  exact real.to_nnreal_sum_of_nonneg hf,
end

theorem sum_lt_sum_of_nonempty {s : finset α} (hs : s.nonempty)
  {f g : α → ℝ≥0∞} (Hlt : ∀ i ∈ s, f i < g i) :
  ∑ i in s, f i < ∑ i in s, g i :=
begin
  induction hs using finset.nonempty.cons_induction with a a s as hs IH,
  { simp [Hlt _ (finset.mem_singleton_self _)] },
  { simp only [as, finset.sum_cons, not_false_iff],
    exact ennreal.add_lt_add (Hlt _ (finset.mem_cons_self _ _))
      (IH (λ i hi, Hlt _ (finset.mem_cons.2 $ or.inr hi))) }
end

theorem exists_le_of_sum_le {s : finset α} (hs : s.nonempty)
  {f g : α → ℝ≥0∞} (Hle : ∑ i in s, f i ≤ ∑ i in s, g i) :
  ∃ i ∈ s, f i ≤ g i :=
begin
  contrapose! Hle,
  apply ennreal.sum_lt_sum_of_nonempty hs Hle,
end

end sum

section interval

variables {x y z : ℝ≥0∞} {ε ε₁ ε₂ : ℝ≥0∞} {s : set ℝ≥0∞}

protected lemma Ico_eq_Iio : (Ico 0 y) = (Iio y) := Ico_bot

lemma mem_Iio_self_add : x ≠ ∞ → ε ≠ 0 → x ∈ Iio (x + ε) :=
assume xt ε0, lt_add_right xt ε0

lemma mem_Ioo_self_sub_add : x ≠ ∞ → x ≠ 0 → ε₁ ≠ 0 → ε₂ ≠ 0 → x ∈ Ioo (x - ε₁) (x + ε₂) :=
assume xt x0 ε0 ε0', ⟨ennreal.sub_lt_self xt x0 ε0, lt_add_right xt ε0'⟩

end interval

section bit

@[simp] lemma bit0_inj : bit0 a = bit0 b ↔ a = b :=
⟨λh, begin
  rcases (lt_trichotomy a b) with h₁| h₂| h₃,
  { exact (absurd h (ne_of_lt (add_lt_add h₁ h₁))) },
  { exact h₂ },
  { exact (absurd h.symm (ne_of_lt (add_lt_add h₃ h₃))) }
end,
λh, congr_arg _ h⟩

@[simp] lemma bit0_eq_zero_iff : bit0 a = 0 ↔ a = 0 :=
by simpa only [bit0_zero] using @bit0_inj a 0

@[simp] lemma bit0_eq_top_iff : bit0 a = ∞ ↔ a = ∞ :=
by rw [bit0, add_eq_top, or_self]

@[simp] lemma bit1_inj : bit1 a = bit1 b ↔ a = b :=
⟨λh, begin
  unfold bit1 at h,
  rwa [add_left_inj, bit0_inj] at h,
  simp [lt_top_iff_ne_top]
end,
λh, congr_arg _ h⟩

@[simp] lemma bit1_ne_zero : bit1 a ≠ 0 :=
by unfold bit1; simp

@[simp] lemma bit1_eq_one_iff : bit1 a = 1 ↔ a = 0 :=
by simpa only [bit1_zero] using @bit1_inj a 0

@[simp] lemma bit1_eq_top_iff : bit1 a = ∞ ↔ a = ∞ :=
by unfold bit1; rw add_eq_top; simp

end bit

section inv
noncomputable theory

instance : has_inv ℝ≥0∞ := ⟨λa, Inf {b | 1 ≤ a * b}⟩

instance : div_inv_monoid ℝ≥0∞ :=
{ inv := has_inv.inv,
  .. (infer_instance : monoid ℝ≥0∞) }

@[simp] lemma inv_zero : (0 : ℝ≥0∞)⁻¹ = ∞ :=
show Inf {b : ℝ≥0∞ | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_top : ∞⁻¹ = 0 :=
bot_unique $ le_of_forall_le_of_dense $ λ a (h : a > 0), Inf_le $ by simp [*, ne_of_gt h, top_mul]

@[simp, norm_cast] lemma coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ℝ≥0∞) = (↑r)⁻¹ :=
le_antisymm
  (le_Inf $ assume b (hb : 1 ≤ ↑r * b), coe_le_iff.2 $
    by rintros b rfl; rwa [← coe_mul, ← coe_one, coe_le_coe, ← nnreal.inv_le hr] at hb)
  (Inf_le $ by simp; rw [← coe_mul, mul_inv_cancel hr]; exact le_refl 1)

lemma coe_inv_le : (↑r⁻¹ : ℝ≥0∞) ≤ (↑r)⁻¹ :=
if hr : r = 0 then by simp only [hr, inv_zero, coe_zero, le_top]
else by simp only [coe_inv hr, le_refl]

@[norm_cast] lemma coe_inv_two : ((2⁻¹:ℝ≥0):ℝ≥0∞) = 2⁻¹ :=
by rw [coe_inv (ne_of_gt _root_.zero_lt_two), coe_two]

@[simp, norm_cast] lemma coe_div (hr : r ≠ 0) : (↑(p / r) : ℝ≥0∞) = p / r :=
by rw [div_eq_mul_inv, div_eq_mul_inv, coe_mul, coe_inv hr]

lemma div_zero (h : a ≠ 0) : a / 0 = ∞ := by simp [div_eq_mul_inv, h]

@[simp] lemma inv_one : (1:ℝ≥0∞)⁻¹ = 1 :=
by simpa only [coe_inv one_ne_zero, coe_one] using coe_eq_coe.2 inv_one

@[simp] lemma div_one {a : ℝ≥0∞} : a / 1 = a :=
by rw [div_eq_mul_inv, inv_one, mul_one]

protected lemma inv_pow {n : ℕ} : (a^n)⁻¹ = (a⁻¹)^n :=
begin
  by_cases a = 0; cases a; cases n; simp [*, none_eq_top, some_eq_coe,
    zero_pow, top_pow, nat.zero_lt_succ] at *,
  rw [← coe_inv h, ← coe_pow, ← coe_inv (pow_ne_zero _ h), ← inv_pow₀, coe_pow]
end

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a :=
by by_cases a = 0; cases a; simp [*, none_eq_top, some_eq_coe,
  -coe_inv, (coe_inv _).symm] at *

lemma inv_involutive : function.involutive (λ a:ℝ≥0∞, a⁻¹) :=
λ a, ennreal.inv_inv

lemma inv_bijective : function.bijective (λ a:ℝ≥0∞, a⁻¹) :=
ennreal.inv_involutive.bijective

@[simp] lemma inv_eq_inv : a⁻¹ = b⁻¹ ↔ a = b := inv_bijective.1.eq_iff

@[simp] lemma inv_eq_top : a⁻¹ = ∞ ↔ a = 0 :=
inv_zero ▸ inv_eq_inv

lemma inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[simp] lemma inv_lt_top {x : ℝ≥0∞} : x⁻¹ < ∞ ↔ 0 < x :=
by { simp only [lt_top_iff_ne_top, inv_ne_top, pos_iff_ne_zero] }

lemma div_lt_top {x y : ℝ≥0∞} (h1 : x ≠ ∞) (h2 : y ≠ 0) : x / y < ∞ :=
mul_lt_top h1 (inv_ne_top.mpr h2)

@[simp] lemma inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
inv_top ▸ inv_eq_inv

lemma inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

lemma mul_inv {a b : ℝ≥0∞} (ha : a ≠ 0 ∨ b ≠ ∞) (hb : a ≠ ∞ ∨ b ≠ 0) :
  (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
begin
  induction b using with_top.rec_top_coe,
  { simp at ha, simp [ha], },
  induction a using with_top.rec_top_coe,
  { simp at hb, simp [hb] },
  by_cases h'a : a = 0,
  { simp only [h'a, with_top.top_mul, ennreal.inv_zero, ennreal.coe_ne_top, zero_mul, ne.def,
               not_false_iff, ennreal.coe_zero, ennreal.inv_eq_zero] },
  by_cases h'b : b = 0,
  { simp only [h'b, ennreal.inv_zero, ennreal.coe_ne_top, with_top.mul_top, ne.def, not_false_iff,
               mul_zero, ennreal.coe_zero, ennreal.inv_eq_zero] },
  rw [← ennreal.coe_mul, ← ennreal.coe_inv, ← ennreal.coe_inv h'a, ← ennreal.coe_inv h'b,
      ← ennreal.coe_mul, nnreal.mul_inv, mul_comm],
  simp [h'a, h'b],
end

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
pos_iff_ne_zero.trans inv_ne_zero

@[simp] lemma inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
begin
  cases a; cases b; simp only [some_eq_coe, none_eq_top, inv_top],
  { simp only [lt_irrefl] },
  { exact inv_pos.trans lt_top_iff_ne_top.symm },
  { simp only [not_lt_zero, not_top_lt] },
  { cases eq_or_lt_of_le (zero_le a) with ha ha,
    { subst a, simp },
    cases eq_or_lt_of_le (zero_le b) with hb hb,
    { subst b, simp [pos_iff_ne_zero, lt_top_iff_ne_top, inv_ne_top] },
    { rw [← coe_inv (ne_of_gt ha), ← coe_inv (ne_of_gt hb), coe_lt_coe, coe_lt_coe],
      simp only [nnreal.coe_lt_coe.symm] at *,
      exact inv_lt_inv ha hb } }
end

lemma inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a :=
by simpa only [inv_inv] using @inv_lt_inv a b⁻¹

lemma lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ :=
by simpa only [inv_inv] using @inv_lt_inv a⁻¹ b

@[simp, priority 1100] -- higher than le_inv_iff_mul_le
lemma inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by simp only [le_iff_lt_or_eq, inv_lt_inv, inv_eq_inv, eq_comm]

lemma inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by simpa only [inv_inv] using @inv_le_inv a b⁻¹

lemma le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by simpa only [inv_inv] using @inv_le_inv a⁻¹ b

@[simp] lemma inv_le_one : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
inv_le_iff_inv_le.trans $ by rw inv_one

lemma one_le_inv : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
le_inv_iff_le_inv.trans $ by rw inv_one

@[simp] lemma inv_lt_one : a⁻¹ < 1 ↔ 1 < a :=
inv_lt_iff_inv_lt.trans $ by rw [inv_one]

/-- The inverse map `λ x, x⁻¹` is an order isomorphism between `ℝ≥0∞` and its `order_dual` -/
@[simps apply]
def _root_.order_iso.inv_ennreal : ℝ≥0∞ ≃o order_dual ℝ≥0∞ :=
{ to_fun := λ x, x⁻¹,
  inv_fun := λ x, x⁻¹,
  left_inv := @ennreal.inv_inv,
  right_inv := @ennreal.inv_inv,
  map_rel_iff' := λ a b, ennreal.inv_le_inv }

@[simp]
lemma _root_.order_iso.inv_ennreal_symm_apply : order_iso.inv_ennreal.symm a = a⁻¹ := rfl

lemma pow_le_pow_of_le_one {n m : ℕ} (ha : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
begin
  rw [← @inv_inv a, ← ennreal.inv_pow, ← @ennreal.inv_pow a⁻¹, inv_le_inv],
  exact pow_le_pow (one_le_inv.2 ha) h
end

@[simp] lemma div_top : a / ∞ = 0 := by rw [div_eq_mul_inv, inv_top, mul_zero]

@[simp] lemma top_div_coe : ∞ / p = ∞ := by simp [div_eq_mul_inv, top_mul]

lemma top_div_of_ne_top (h : a ≠ ∞) : ∞ / a = ∞ :=
by { lift a to ℝ≥0 using h, exact top_div_coe }

lemma top_div_of_lt_top (h : a < ∞) : ∞ / a = ∞ :=
top_div_of_ne_top h.ne

lemma top_div : ∞ / a = if a = ∞ then 0 else ∞ :=
by by_cases a = ∞; simp [top_div_of_ne_top, *]

@[simp] lemma zero_div : 0 / a = 0 := zero_mul a⁻¹

lemma div_eq_top : a / b = ∞ ↔ (a ≠ 0 ∧ b = 0) ∨ (a = ∞ ∧ b ≠ ∞) :=
by simp [div_eq_mul_inv, ennreal.mul_eq_top]

lemma le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
  a ≤ c / b ↔ a * b ≤ c :=
begin
  cases b,
  { simp at ht,
    split,
    { assume ha, simp at ha, simp [ha] },
    { contrapose,
      assume ha,
      simp at ha,
      have : a * ∞ = ∞, by simp [ennreal.mul_eq_top, ha],
      simp [this, ht] } },
  by_cases hb : b ≠ 0,
  { have : (b : ℝ≥0∞) ≠ 0, by simp [hb],
    rw [← ennreal.mul_le_mul_left this coe_ne_top],
    suffices : ↑b * a ≤ (↑b * ↑b⁻¹) * c ↔ a * ↑b ≤ c,
    { simpa [some_eq_coe, div_eq_mul_inv, hb, mul_left_comm, mul_comm, mul_assoc] },
    rw [← coe_mul, mul_inv_cancel hb, coe_one, one_mul, mul_comm] },
  { simp at hb,
    simp [hb] at h0,
    have : c / 0 = ∞, by simp [div_eq_top, h0],
    simp [hb, this] }
end

lemma div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) : a / b ≤ c ↔ a ≤ c * b :=
begin
  suffices : a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹, by simpa [div_eq_mul_inv],
  refine (le_div_iff_mul_le _ _).symm; simpa
end

lemma lt_div_iff_mul_lt (hb0 : b ≠ 0 ∨ c ≠ ∞) (hbt : b ≠ ∞ ∨ c ≠ 0) : c < a / b ↔ c * b < a :=
lt_iff_lt_of_le_iff_le (div_le_iff_le_mul hb0 hbt)

lemma div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b :=
begin
  by_cases h0 : c = 0,
  { have : a = 0, by simpa [h0] using h, simp [*] },
  by_cases hinf : c = ∞, by simp [hinf],
  exact (div_le_iff_le_mul (or.inl h0) (or.inl hinf)).2 h
end

lemma div_le_of_le_mul' (h : a ≤ b * c) : a / b ≤ c :=
div_le_of_le_mul $ mul_comm b c ▸ h

lemma mul_le_of_le_div (h : a ≤ b / c) : a * c ≤ b :=
begin
  rcases _root_.em (c = 0 ∧ b = 0 ∨ c = ∞ ∧ b = ∞) with (⟨rfl, rfl⟩|⟨rfl, rfl⟩)|H,
  { rw [mul_zero], exact le_rfl },
  { exact le_top },
  { simp only [not_or_distrib, not_and_distrib] at H,
    rwa ← le_div_iff_mul_le H.1 H.2 }
end

lemma mul_le_of_le_div' (h : a ≤ b / c) : c * a ≤ b :=
mul_comm a c ▸ mul_le_of_le_div h

protected lemma div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ∞ ∨ c ≠ ∞) :
  c / b < a ↔ c < a * b :=
lt_iff_lt_of_le_iff_le $ le_div_iff_mul_le h0 ht

lemma mul_lt_of_lt_div (h : a < b / c) : a * c < b :=
by { contrapose! h, exact ennreal.div_le_of_le_mul h }

lemma mul_lt_of_lt_div' (h : a < b / c) : c * a < b := mul_comm a c ▸ mul_lt_of_lt_div h

lemma inv_le_iff_le_mul : (b = ∞ → a ≠ 0) → (a = ∞ → b ≠ 0) → (a⁻¹ ≤ b ↔ 1 ≤ a * b) :=
begin
  cases a; cases b; simp [none_eq_top, some_eq_coe, mul_top, top_mul] {contextual := tt},
  by_cases a = 0; simp [*, -coe_mul, coe_mul.symm, -coe_inv, (coe_inv _).symm, nnreal.inv_le]
end

@[simp] lemma le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
begin
  cases b, { by_cases a = 0; simp [*, none_eq_top, mul_top] },
  by_cases b = 0; simp [*, some_eq_coe, le_div_iff_mul_le],
  suffices : a ≤ 1 / b ↔ a * b ≤ 1, { simpa [div_eq_mul_inv, h] },
  exact le_div_iff_mul_le (or.inl (mt coe_eq_coe.1 h)) (or.inl coe_ne_top)
end

lemma mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a * a⁻¹ = 1 :=
begin
  lift a to ℝ≥0 using ht,
  norm_cast at *,
  exact mul_inv_cancel h0
end

lemma inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
mul_comm a a⁻¹ ▸ mul_inv_cancel h0 ht

lemma eq_inv_of_mul_eq_one (h : a * b = 1) : a = b⁻¹ :=
begin
  rcases eq_or_ne b ∞ with rfl|hb,
  { have : false, by simpa [left_ne_zero_of_mul_eq_one h] using h,
    exact this.elim },
  { rw [← mul_one a, ← mul_inv_cancel (right_ne_zero_of_mul_eq_one h) hb, ← mul_assoc, h, one_mul] }
end

lemma mul_le_iff_le_inv {a b r : ℝ≥0∞} (hr₀ : r ≠ 0) (hr₁ : r ≠ ∞) : (r * a ≤ b ↔ a ≤ r⁻¹ * b) :=
by rw [← @ennreal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, mul_inv_cancel hr₀ hr₁, one_mul]

lemma le_of_forall_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r < x → ↑r ≤ y) : x ≤ y :=
begin
  refine le_of_forall_ge_of_dense (λ r hr, _),
  lift r to ℝ≥0 using ne_top_of_lt hr,
  exact h r hr
end

lemma le_of_forall_pos_nnreal_lt {x y : ℝ≥0∞} (h : ∀ r : ℝ≥0, 0 < r → ↑r < x → ↑r ≤ y) : x ≤ y :=
le_of_forall_nnreal_lt $ λ r hr, (zero_le r).eq_or_lt.elim (λ h, h ▸ zero_le _) (λ h0, h r h0 hr)

lemma eq_top_of_forall_nnreal_le {x : ℝ≥0∞} (h : ∀ r : ℝ≥0, ↑r ≤ x) : x = ∞ :=
top_unique $ le_of_forall_nnreal_lt $ λ r hr, h r

lemma add_div {a b c : ℝ≥0∞} : (a + b) / c = a / c + b / c :=
right_distrib a b (c⁻¹)

lemma div_add_div_same {a b c : ℝ≥0∞} : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
mul_inv_cancel h0 hI

lemma mul_div_cancel (h0 : a ≠ 0) (hI : a ≠ ∞) : (b / a) * a = b :=
by rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel h0 hI, mul_one]

lemma mul_div_cancel' (h0 : a ≠ 0) (hI : a ≠ ∞) : a * (b / a) = b :=
by rw [mul_comm, mul_div_cancel h0 hI]

lemma mul_div_le : a * (b / a) ≤ b :=
begin
  by_cases h0 : a = 0, { simp [h0] },
  by_cases hI : a = ∞, { simp [hI] },
  rw mul_div_cancel' h0 hI, exact le_refl b
end

lemma inv_two_add_inv_two : (2:ℝ≥0∞)⁻¹ + 2⁻¹ = 1 :=
by rw [← two_mul, ← div_eq_mul_inv, div_self two_ne_zero two_ne_top]

lemma inv_three_add_inv_three : (3 : ℝ≥0∞)⁻¹ + 3⁻¹ +3⁻¹ = 1 :=
begin
  rw [show (3 : ℝ≥0∞)⁻¹ + 3⁻¹ + 3⁻¹ = 3 * 3⁻¹, by ring, ← div_eq_mul_inv, ennreal.div_self];
  simp,
end

@[simp]
lemma add_halves (a : ℝ≥0∞) : a / 2 + a / 2 = a :=
by rw [div_eq_mul_inv, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp]
lemma add_thirds (a : ℝ≥0∞) : a / 3 + a / 3 + a / 3 = a :=
by rw [div_eq_mul_inv, ← mul_add, ← mul_add, inv_three_add_inv_three, mul_one]

@[simp] lemma div_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ∞ :=
by simp [div_eq_mul_inv]

@[simp] lemma div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ∞ :=
by simp [pos_iff_ne_zero, not_or_distrib]

lemma half_pos {a : ℝ≥0∞} (h : a ≠ 0) : 0 < a / 2 :=
by simp [h]

lemma one_half_lt_one : (2⁻¹:ℝ≥0∞) < 1 := inv_lt_one.2 $ one_lt_two

lemma half_lt_self {a : ℝ≥0∞} (hz : a ≠ 0) (ht : a ≠ ∞) : a / 2 < a :=
begin
  lift a to ℝ≥0 using ht,
  have h : (2 : ℝ≥0∞) = ((2 : ℝ≥0) : ℝ≥0∞), from rfl,
  have h' : (2 : ℝ≥0) ≠ 0, from _root_.two_ne_zero',
  rw [h, ← coe_div h', coe_lt_coe], -- `norm_cast` fails to apply `coe_div`
  norm_cast at hz,
  exact nnreal.half_lt_self hz
end

lemma half_le_self : a / 2 ≤ a := le_add_self.trans_eq (add_halves _)

lemma sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 :=
begin
  lift a to ℝ≥0 using h,
  exact sub_eq_of_add_eq (mul_ne_top coe_ne_top $ by simp) (add_halves a)
end

@[simp] lemma one_sub_inv_two : (1:ℝ≥0∞) - 2⁻¹ = 2⁻¹ :=
by simpa only [div_eq_mul_inv, one_mul] using sub_half one_ne_top

lemma exists_inv_nat_lt {a : ℝ≥0∞} (h : a ≠ 0) :
  ∃n:ℕ, (n:ℝ≥0∞)⁻¹ < a :=
@inv_inv a ▸ by simp only [inv_lt_inv, ennreal.exists_nat_gt (inv_ne_top.2 h)]

lemma exists_nat_pos_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) :
  ∃ n > 0, b < (n : ℕ) * a :=
begin
  have : b / a ≠ ∞, from mul_ne_top hb (inv_ne_top.2 ha),
  refine (ennreal.exists_nat_gt this).imp (λ n hn, _),
  have : 0 < (n : ℝ≥0∞), from (zero_le _).trans_lt hn,
  refine ⟨coe_nat_lt_coe_nat.1 this, _⟩,
  rwa [← ennreal.div_lt_iff (or.inl ha) (or.inr hb)]
end

lemma exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ∞) :
  ∃ n : ℕ, b < n * a :=
(exists_nat_pos_mul_gt ha hb).imp $ λ n, Exists.snd

lemma exists_nat_pos_inv_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
  ∃ n > 0, ((n : ℕ) : ℝ≥0∞)⁻¹ * a < b :=
begin
  rcases exists_nat_pos_mul_gt hb ha with ⟨n, npos, hn⟩,
  have : (n : ℝ≥0∞) ≠ 0 := nat.cast_ne_zero.2 npos.lt.ne',
  use [n, npos],
  rwa [← one_mul b, ← inv_mul_cancel this coe_nat_ne_top,
    mul_assoc, mul_lt_mul_left (inv_ne_zero.2 coe_nat_ne_top) (inv_ne_top.2 this)]
end

lemma exists_nnreal_pos_mul_lt (ha : a ≠ ∞) (hb : b ≠ 0) :
  ∃ n > 0, ↑(n : ℝ≥0) * a < b :=
begin
  rcases exists_nat_pos_inv_mul_lt ha hb with ⟨n, npos : 0 < n, hn⟩,
  use (n : ℝ≥0)⁻¹,
  simp [*, npos.ne', zero_lt_one]
end

lemma exists_inv_two_pow_lt (ha : a ≠ 0) :
  ∃ n : ℕ, 2⁻¹ ^ n < a :=
begin
  rcases exists_inv_nat_lt ha with ⟨n, hn⟩,
  simp only [← ennreal.inv_pow],
  refine ⟨n, lt_trans (inv_lt_inv.2 _) hn⟩,
  norm_cast,
  exact n.lt_two_pow
end

@[simp, norm_cast] lemma coe_zpow (hr : r ≠ 0) (n : ℤ) : (↑(r^n) : ℝ≥0∞) = r^n :=
begin
  cases n,
  { simp only [int.of_nat_eq_coe, coe_pow, zpow_coe_nat] },
  { have : r ^ n.succ ≠ 0 := pow_ne_zero (n+1) hr,
    simp only [zpow_neg_succ_of_nat, coe_inv this, coe_pow] }
end

lemma zpow_pos (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : 0 < a ^ n :=
begin
  cases n,
  { exact ennreal.pow_pos ha.bot_lt n },
  { simp only [h'a, pow_eq_top_iff, zpow_neg_succ_of_nat, ne.def, not_false_iff,
               inv_pos, false_and] }
end

lemma zpow_lt_top (ha : a ≠ 0) (h'a : a ≠ ∞) (n : ℤ) : a ^ n < ∞ :=
begin
  cases n,
  { exact ennreal.pow_lt_top h'a.lt_top _ },
  { simp only [ennreal.pow_pos ha.bot_lt (n + 1), zpow_neg_succ_of_nat, inv_lt_top] }
end

lemma exists_mem_Ico_zpow
  {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
  ∃ n : ℤ, x ∈ Ico (y ^ n) (y ^ (n + 1)) :=
begin
  lift x to ℝ≥0 using h'x,
  lift y to ℝ≥0 using h'y,
  have A : y ≠ 0, by simpa only [ne.def, coe_eq_zero] using (ennreal.zero_lt_one.trans hy).ne',
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n ≤ x ∧ x < y ^ (n + 1),
  { refine nnreal.exists_mem_Ico_zpow _ (one_lt_coe_iff.1 hy),
    simpa only [ne.def, coe_eq_zero] using hx },
  refine ⟨n, _, _⟩,
  { rwa [← ennreal.coe_zpow A, ennreal.coe_le_coe] },
  { rwa [← ennreal.coe_zpow A, ennreal.coe_lt_coe] }
end

lemma exists_mem_Ioc_zpow
  {x y : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (hy : 1 < y) (h'y : y ≠ ⊤) :
  ∃ n : ℤ, x ∈ Ioc (y ^ n) (y ^ (n + 1)) :=
begin
  lift x to ℝ≥0 using h'x,
  lift y to ℝ≥0 using h'y,
  have A : y ≠ 0, by simpa only [ne.def, coe_eq_zero] using (ennreal.zero_lt_one.trans hy).ne',
  obtain ⟨n, hn, h'n⟩ : ∃ n : ℤ, y ^ n < x ∧ x ≤ y ^ (n + 1),
  { refine nnreal.exists_mem_Ioc_zpow _ (one_lt_coe_iff.1 hy),
    simpa only [ne.def, coe_eq_zero] using hx },
  refine ⟨n, _, _⟩,
  { rwa [← ennreal.coe_zpow A, ennreal.coe_lt_coe] },
  { rwa [← ennreal.coe_zpow A, ennreal.coe_le_coe] }
end

lemma Ioo_zero_top_eq_Union_Ico_zpow {y : ℝ≥0∞} (hy : 1 < y) (h'y : y ≠ ⊤) :
  Ioo (0 : ℝ≥0∞) (∞ : ℝ≥0∞) = ⋃ (n : ℤ), Ico (y^n) (y^(n+1)) :=
begin
  ext x,
  simp only [mem_Union, mem_Ioo, mem_Ico],
  split,
  { rintros ⟨hx, h'x⟩,
    exact exists_mem_Ico_zpow hx.ne' h'x.ne hy h'y },
  { rintros ⟨n, hn, h'n⟩,
    split,
    { apply lt_of_lt_of_le _ hn,
      exact ennreal.zpow_pos (ennreal.zero_lt_one.trans hy).ne' h'y _ },
    { apply lt_trans h'n _,
      exact ennreal.zpow_lt_top (ennreal.zero_lt_one.trans hy).ne' h'y _ } }
end

lemma zpow_le_of_le {x : ℝ≥0∞} (hx : 1 ≤ x) {a b : ℤ} (h : a ≤ b) : x ^ a ≤ x ^ b :=
begin
  induction a with a a; induction b with b b,
  { simp,
    apply pow_le_pow hx,
    apply int.le_of_coe_nat_le_coe_nat h },
  { apply absurd h,
    apply not_le_of_gt,
    exact lt_of_lt_of_le (int.neg_succ_lt_zero _) (int.of_nat_nonneg _) },
  { simp only [zpow_neg_succ_of_nat, int.of_nat_eq_coe, zpow_coe_nat],
    refine le_trans (inv_le_one.2 _) _;
    apply ennreal.one_le_pow_of_one_le hx, },
  { simp only [zpow_neg_succ_of_nat],
    apply inv_le_inv.2,
    { apply pow_le_pow hx,
      have : -(↑(a+1) : ℤ) ≤ -(↑(b+1) : ℤ), from h,
      have h' := le_of_neg_le_neg this,
      apply int.le_of_coe_nat_le_coe_nat h' },
    repeat { apply pow_pos (lt_of_lt_of_le zero_lt_one hx) } }
end

lemma monotone_zpow {x : ℝ≥0∞} (hx : 1 ≤ x) : monotone ((^) x : ℤ → ℝ≥0∞) :=
λ a b h, zpow_le_of_le hx h

lemma zpow_add {x : ℝ≥0∞} (hx : x ≠ 0) (h'x : x ≠ ∞) (m n : ℤ) :
  x ^ (m + n) = x ^ m * x ^ n :=
begin
  lift x to ℝ≥0 using h'x,
  replace hx : x ≠ 0, by simpa only [ne.def, coe_eq_zero] using hx,
  simp only [← coe_zpow hx, zpow_add₀ hx, coe_mul]
end

end inv

section real

lemma to_real_add (ha : a ≠ ∞) (hb : b ≠ ∞) : (a+b).to_real = a.to_real + b.to_real :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  refl
end

lemma to_real_sub_of_le {a b : ℝ≥0∞} (h : b ≤ a) (ha : a ≠ ∞):
  (a - b).to_real = a.to_real - b.to_real :=
begin
  lift b to ℝ≥0 using ne_top_of_le_ne_top ha h,
  lift a to ℝ≥0 using ha,
  simp only [← ennreal.coe_sub, ennreal.coe_to_real, nnreal.coe_sub (ennreal.coe_le_coe.mp h)],
end

lemma le_to_real_sub {a b : ℝ≥0∞} (hb : b ≠ ∞) : a.to_real - b.to_real ≤ (a - b).to_real :=
begin
  lift b to ℝ≥0 using hb,
  cases a,
  { simp },
  { simp only [some_eq_coe, ←coe_sub, nnreal.sub_def, real.coe_to_nnreal', coe_to_real],
    exact le_max_left _ _ }
end

lemma to_real_add_le : (a+b).to_real ≤ a.to_real + b.to_real :=
if ha : a = ∞ then by simp only [ha, top_add, top_to_real, zero_add, to_real_nonneg]
else if hb : b = ∞ then by simp only [hb, add_top, top_to_real, add_zero, to_real_nonneg]
else le_of_eq (to_real_add ha hb)

lemma of_real_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
  ennreal.of_real (p + q) = ennreal.of_real p + ennreal.of_real q :=
by rw [ennreal.of_real, ennreal.of_real, ennreal.of_real, ← coe_add,
       coe_eq_coe, real.to_nnreal_add hp hq]

lemma of_real_add_le {p q : ℝ} : ennreal.of_real (p + q) ≤ ennreal.of_real p + ennreal.of_real q :=
coe_le_coe.2 real.to_nnreal_add_le

@[simp] lemma to_real_le_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : a.to_real ≤ b.to_real ↔ a ≤ b :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  norm_cast
end

lemma to_real_mono (hb : b ≠ ∞) (h : a ≤ b) : a.to_real ≤ b.to_real :=
(to_real_le_to_real (h.trans_lt (lt_top_iff_ne_top.2 hb)).ne hb).2 h

@[simp] lemma to_real_lt_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) : a.to_real < b.to_real ↔ a < b :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  norm_cast
end

lemma to_real_strict_mono (hb : b ≠ ∞) (h : a < b) : a.to_real < b.to_real :=
(to_real_lt_to_real (h.trans (lt_top_iff_ne_top.2 hb)).ne hb).2 h

lemma to_nnreal_mono (hb : b ≠ ∞) (h : a ≤ b) : a.to_nnreal ≤ b.to_nnreal :=
by simpa [←ennreal.coe_le_coe, hb, (h.trans_lt hb.lt_top).ne]

@[simp] lemma to_nnreal_le_to_nnreal (ha : a ≠ ∞) (hb : b ≠ ∞) :
  a.to_nnreal ≤ b.to_nnreal ↔ a ≤ b :=
begin
  refine ⟨_, to_nnreal_mono hb⟩,
  { intro h,
    have key := ennreal.coe_le_coe.mpr h,
    rwa [coe_to_nnreal ha, coe_to_nnreal hb] at key, },
end

lemma to_nnreal_strict_mono (hb : b ≠ ∞) (h : a < b) : a.to_nnreal < b.to_nnreal :=
by simpa [←ennreal.coe_lt_coe, hb, (h.trans hb.lt_top).ne]

@[simp] lemma to_nnreal_lt_to_nnreal (ha : a ≠ ∞) (hb : b ≠ ∞) :
  a.to_nnreal < b.to_nnreal ↔ a < b :=
begin
  refine ⟨_, to_nnreal_strict_mono hb⟩,
  { intro h,
    have key := ennreal.coe_lt_coe.mpr h,
    rwa [coe_to_nnreal ha, coe_to_nnreal hb] at key, },
end

lemma to_real_max (hr : a ≠ ∞) (hp : b ≠ ∞) :
  ennreal.to_real (max a b) = max (ennreal.to_real a) (ennreal.to_real b) :=
(le_total a b).elim
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hr hp).2 h, max_eq_right])
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hp hr).2 h, max_eq_left])

lemma to_nnreal_pos_iff : 0 < a.to_nnreal ↔ (0 < a ∧ a < ∞) :=
begin
  cases a,
  { simp [none_eq_top] },
  { simp [some_eq_coe] }
end

lemma to_nnreal_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.to_nnreal :=
to_nnreal_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a < ∞):=
(nnreal.coe_pos).trans to_nnreal_pos_iff

lemma to_real_pos {a : ℝ≥0∞} (ha₀ : a ≠ 0) (ha_top : a ≠ ∞) : 0 < a.to_real :=
to_real_pos_iff.mpr ⟨bot_lt_iff_ne_bot.mpr ha₀, lt_top_iff_ne_top.mpr ha_top⟩

lemma of_real_le_of_real {p q : ℝ} (h : p ≤ q) : ennreal.of_real p ≤ ennreal.of_real q :=
by simp [ennreal.of_real, real.to_nnreal_le_to_nnreal h]

lemma of_real_le_of_le_to_real {a : ℝ} {b : ℝ≥0∞} (h : a ≤ ennreal.to_real b) :
  ennreal.of_real a ≤ b :=
(of_real_le_of_real h).trans of_real_to_real_le

@[simp] lemma of_real_le_of_real_iff {p q : ℝ} (h : 0 ≤ q) :
  ennreal.of_real p ≤ ennreal.of_real q ↔ p ≤ q :=
by rw [ennreal.of_real, ennreal.of_real, coe_le_coe, real.to_nnreal_le_to_nnreal_iff h]

@[simp] lemma of_real_lt_of_real_iff {p q : ℝ} (h : 0 < q) :
  ennreal.of_real p < ennreal.of_real q ↔ p < q :=
by rw [ennreal.of_real, ennreal.of_real, coe_lt_coe, real.to_nnreal_lt_to_nnreal_iff h]

lemma of_real_lt_of_real_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
  ennreal.of_real p < ennreal.of_real q ↔ p < q :=
by rw [ennreal.of_real, ennreal.of_real, coe_lt_coe, real.to_nnreal_lt_to_nnreal_iff_of_nonneg hp]

@[simp] lemma of_real_pos {p : ℝ} : 0 < ennreal.of_real p ↔ 0 < p :=
by simp [ennreal.of_real]

@[simp] lemma of_real_eq_zero {p : ℝ} : ennreal.of_real p = 0 ↔ p ≤ 0 :=
by simp [ennreal.of_real]

@[simp] lemma zero_eq_of_real {p : ℝ} : 0 = ennreal.of_real p ↔ p ≤ 0 :=
eq_comm.trans of_real_eq_zero

lemma of_real_le_iff_le_to_real {a : ℝ} {b : ℝ≥0∞} (hb : b ≠ ∞) :
  ennreal.of_real a ≤ b ↔ a ≤ ennreal.to_real b :=
begin
  lift b to ℝ≥0 using hb,
  simpa [ennreal.of_real, ennreal.to_real] using real.to_nnreal_le_iff_le_coe
end

lemma of_real_lt_iff_lt_to_real {a : ℝ} {b : ℝ≥0∞} (ha : 0 ≤ a) (hb : b ≠ ∞) :
  ennreal.of_real a < b ↔ a < ennreal.to_real b :=
begin
  lift b to ℝ≥0 using hb,
  simpa [ennreal.of_real, ennreal.to_real] using real.to_nnreal_lt_iff_lt_coe ha
end

lemma le_of_real_iff_to_real_le {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) (hb : 0 ≤ b) :
  a ≤ ennreal.of_real b ↔ ennreal.to_real a ≤ b :=
begin
  lift a to ℝ≥0 using ha,
  simpa [ennreal.of_real, ennreal.to_real] using real.le_to_nnreal_iff_coe_le hb
end

lemma to_real_le_of_le_of_real {a : ℝ≥0∞} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ennreal.of_real b) :
  ennreal.to_real a ≤ b :=
have ha : a ≠ ∞, from ne_top_of_le_ne_top of_real_ne_top h,
(le_of_real_iff_to_real_le ha hb).1 h

lemma lt_of_real_iff_to_real_lt {a : ℝ≥0∞} {b : ℝ} (ha : a ≠ ∞) :
  a < ennreal.of_real b ↔ ennreal.to_real a < b :=
begin
  lift a to ℝ≥0 using ha,
  simpa [ennreal.of_real, ennreal.to_real] using real.lt_to_nnreal_iff_coe_lt
end

lemma of_real_mul {p q : ℝ} (hp : 0 ≤ p) :
  ennreal.of_real (p * q) = (ennreal.of_real p) * (ennreal.of_real q) :=
by { simp only [ennreal.of_real, coe_mul.symm, coe_eq_coe], exact real.to_nnreal_mul hp }

lemma of_real_pow {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
  ennreal.of_real (p ^ n) = ennreal.of_real p ^ n :=
by rw [of_real_eq_coe_nnreal hp, ← coe_pow, ← of_real_coe_nnreal, nnreal.coe_pow, nnreal.coe_mk]

lemma of_real_inv_of_pos {x : ℝ} (hx : 0 < x) :
  (ennreal.of_real x)⁻¹ = ennreal.of_real x⁻¹ :=
by rw [ennreal.of_real, ennreal.of_real, ←@coe_inv (real.to_nnreal x) (by simp [hx]), coe_eq_coe,
  real.to_nnreal_inv.symm]

lemma of_real_div_of_pos {x y : ℝ} (hy : 0 < y) :
  ennreal.of_real (x / y) = ennreal.of_real x / ennreal.of_real y :=
by rw [div_eq_inv_mul, div_eq_mul_inv, of_real_mul (inv_nonneg.2 hy.le), of_real_inv_of_pos hy,
  mul_comm]

lemma to_real_of_real_mul (c : ℝ) (a : ℝ≥0∞) (h : 0 ≤ c) :
  ennreal.to_real ((ennreal.of_real c) * a) = c * ennreal.to_real a :=
begin
  cases a,
  { simp only [none_eq_top, ennreal.to_real, top_to_nnreal, nnreal.coe_zero, mul_zero, mul_top],
    by_cases h' : c ≤ 0,
    { rw [if_pos], { simp }, { convert of_real_zero, exact le_antisymm h' h } },
    { rw [if_neg], refl, rw [of_real_eq_zero], assumption } },
  { simp only [ennreal.to_real, ennreal.to_nnreal],
    simp only [some_eq_coe, ennreal.of_real, coe_mul.symm, to_nnreal_coe, nnreal.coe_mul],
    congr, apply real.coe_to_nnreal, exact h }
end

@[simp] lemma to_nnreal_mul_top (a : ℝ≥0∞) : ennreal.to_nnreal (a * ∞) = 0 :=
begin
  by_cases h : a = 0,
  { rw [h, zero_mul, zero_to_nnreal] },
  { rw [mul_top, if_neg h, top_to_nnreal] }
end

@[simp] lemma to_nnreal_top_mul (a : ℝ≥0∞) : ennreal.to_nnreal (∞ * a) = 0 :=
by rw [mul_comm, to_nnreal_mul_top]

@[simp] lemma to_real_mul_top (a : ℝ≥0∞) : ennreal.to_real (a * ∞) = 0 :=
by rw [ennreal.to_real, to_nnreal_mul_top, nnreal.coe_zero]

@[simp] lemma to_real_top_mul (a : ℝ≥0∞) : ennreal.to_real (∞ * a) = 0 :=
by { rw mul_comm, exact to_real_mul_top _ }

lemma to_real_eq_to_real (ha : a ≠ ∞) (hb : b ≠ ∞) :
  ennreal.to_real a = ennreal.to_real b ↔ a = b :=
begin
  lift a to ℝ≥0 using ha,
  lift b to ℝ≥0 using hb,
  simp only [coe_eq_coe, nnreal.coe_eq, coe_to_real],
end

lemma to_real_smul (r : ℝ≥0) (s : ℝ≥0∞) :
  (r • s).to_real = r • s.to_real :=
begin
  induction s using with_top.rec_top_coe,
  { rw [show r • ∞ = (r : ℝ≥0∞) * ∞, by refl],
    simp only [ennreal.to_real_mul_top, ennreal.top_to_real, smul_zero] },
  { rw [← coe_smul, ennreal.coe_to_real, ennreal.coe_to_real],
    refl }
end

protected lemma trichotomy (p : ℝ≥0∞) : p = 0 ∨ p = ∞ ∨ 0 < p.to_real :=
begin
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with (rfl : 0 = p) | (hp : 0 < p),
  { simp },
  rcases eq_or_lt_of_le (le_top : p ≤ ⊤) with rfl | hp',
  { simp },
  simp [ennreal.to_real_pos_iff, hp, hp'],
end

protected lemma trichotomy₂ {p q : ℝ≥0∞} (hpq : p ≤ q) :
  (p = 0 ∧ q = 0) ∨ (p = 0 ∧ q = ∞) ∨ (p = 0 ∧ 0 < q.to_real) ∨ (p = ∞ ∧ q = ∞)
  ∨ (0 < p.to_real ∧ q = ∞) ∨ (0 < p.to_real ∧ 0 < q.to_real ∧ p.to_real ≤ q.to_real) :=
begin
  rcases eq_or_lt_of_le (bot_le : 0 ≤ p) with (rfl : 0 = p) | (hp : 0 < p),
  { simpa using q.trichotomy },
  rcases eq_or_lt_of_le (le_top : q ≤ ∞) with rfl | hq,
  { simpa using p.trichotomy },
  repeat { right },
  have hq' : 0 < q := lt_of_lt_of_le hp hpq,
  have hp' : p < ∞ := lt_of_le_of_lt hpq hq,
  simp [ennreal.to_real_le_to_real hp'.ne hq.ne, ennreal.to_real_pos_iff, hpq, hp, hp', hq', hq],
end

protected lemma dichotomy (p : ℝ≥0∞) [fact (1 ≤ p)] : p = ∞ ∨ 1 ≤ p.to_real :=
begin
  have :  p = ⊤ ∨ 0 < p.to_real ∧ 1 ≤ p.to_real,
  { simpa using ennreal.trichotomy₂ (fact.out _ : 1 ≤ p) },
  exact this.imp_right (λ h, h.2)
end

/-- `ennreal.to_nnreal` as a `monoid_hom`. -/
def to_nnreal_hom : ℝ≥0∞ →* ℝ≥0 :=
{ to_fun := ennreal.to_nnreal,
  map_one' := to_nnreal_coe,
  map_mul' := by rintro (_|x) (_|y); simp only [← coe_mul, none_eq_top, some_eq_coe,
    to_nnreal_top_mul, to_nnreal_mul_top, top_to_nnreal, mul_zero, zero_mul, to_nnreal_coe] }

lemma to_nnreal_mul {a b : ℝ≥0∞}: (a * b).to_nnreal = a.to_nnreal * b.to_nnreal :=
to_nnreal_hom.map_mul a b

lemma to_nnreal_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).to_nnreal = a.to_nnreal ^ n :=
to_nnreal_hom.map_pow a n

lemma to_nnreal_prod {ι : Type*} {s : finset ι} {f : ι → ℝ≥0∞} :
  (∏ i in s, f i).to_nnreal = ∏ i in s, (f i).to_nnreal :=
to_nnreal_hom.map_prod _ _

lemma to_nnreal_inv (a : ℝ≥0∞) : (a⁻¹).to_nnreal = (a.to_nnreal)⁻¹ :=
begin
  rcases eq_or_ne a ∞ with rfl|ha, { simp },
  lift a to ℝ≥0 using ha,
  rcases eq_or_ne a 0 with rfl|ha, { simp },
  rw [← coe_inv ha, to_nnreal_coe, to_nnreal_coe]
end

lemma to_nnreal_div (a b : ℝ≥0∞) : (a / b).to_nnreal = a.to_nnreal / b.to_nnreal :=
by rw [div_eq_mul_inv, to_nnreal_mul, to_nnreal_inv, div_eq_mul_inv]

/-- `ennreal.to_real` as a `monoid_hom`. -/
def to_real_hom : ℝ≥0∞ →* ℝ :=
(nnreal.to_real_hom : ℝ≥0 →* ℝ).comp to_nnreal_hom

lemma to_real_mul : (a * b).to_real = a.to_real * b.to_real :=
to_real_hom.map_mul a b

lemma to_real_pow (a : ℝ≥0∞) (n : ℕ) : (a ^ n).to_real = a.to_real ^ n :=
to_real_hom.map_pow a n

lemma to_real_prod {ι : Type*} {s : finset ι} {f : ι → ℝ≥0∞} :
  (∏ i in s, f i).to_real = ∏ i in s, (f i).to_real :=
to_real_hom.map_prod _ _

lemma to_real_inv (a : ℝ≥0∞) : (a⁻¹).to_real = (a.to_real)⁻¹ :=
by { simp_rw ennreal.to_real, norm_cast, exact to_nnreal_inv a, }

lemma to_real_div (a b : ℝ≥0∞) : (a / b).to_real = a.to_real / b.to_real :=
by rw [div_eq_mul_inv, to_real_mul, to_real_inv, div_eq_mul_inv]

lemma of_real_prod_of_nonneg {s : finset α} {f : α → ℝ} (hf : ∀ i, i ∈ s → 0 ≤ f i) :
  ennreal.of_real (∏ i in s, f i) = ∏ i in s, ennreal.of_real (f i) :=
begin
  simp_rw [ennreal.of_real, ←coe_finset_prod, coe_eq_coe],
  exact real.to_nnreal_prod_of_nonneg hf,
end

@[simp] lemma to_nnreal_bit0 {x : ℝ≥0∞} : (bit0 x).to_nnreal = bit0 (x.to_nnreal) :=
begin
  by_cases hx_top : x = ∞,
  { simp [hx_top, bit0_eq_top_iff.mpr rfl], },
  exact to_nnreal_add hx_top hx_top,
end

@[simp] lemma to_nnreal_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) :
  (bit1 x).to_nnreal = bit1 (x.to_nnreal) :=
by simp [bit1, bit1, to_nnreal_add (by rwa [ne.def, bit0_eq_top_iff]) ennreal.one_ne_top]

@[simp] lemma to_real_bit0 {x : ℝ≥0∞} : (bit0 x).to_real = bit0 (x.to_real) :=
by simp [ennreal.to_real]

@[simp] lemma to_real_bit1 {x : ℝ≥0∞} (hx_top : x ≠ ∞) :
  (bit1 x).to_real = bit1 (x.to_real) :=
by simp [ennreal.to_real, hx_top]

@[simp] lemma of_real_bit0 {r : ℝ} (hr : 0 ≤ r) :
  ennreal.of_real (bit0 r) = bit0 (ennreal.of_real r) :=
of_real_add hr hr

@[simp] lemma of_real_bit1 {r : ℝ} (hr : 0 ≤ r) :
  ennreal.of_real (bit1 r) = bit1 (ennreal.of_real r) :=
(of_real_add (by simp [hr]) zero_le_one).trans (by simp [real.to_nnreal_one, bit1, hr])

end real

section infi
variables {ι : Sort*} {f g : ι → ℝ≥0∞}

lemma infi_add : infi f + a = ⨅i, f i + a :=
le_antisymm
  (le_infi $ assume i, add_le_add (infi_le _ _) $ le_rfl)
  (tsub_le_iff_right.1 $ le_infi $ assume i, tsub_le_iff_right.2 $ infi_le _ _)

lemma supr_sub : (⨆i, f i) - a = (⨆i, f i - a) :=
le_antisymm
  (tsub_le_iff_right.2 $ supr_le $ assume i, tsub_le_iff_right.1 $ le_supr _ i)
  (supr_le $ assume i, tsub_le_tsub (le_supr _ _) (le_refl a))

lemma sub_infi : a - (⨅i, f i) = (⨆i, a - f i) :=
begin
  refine (eq_of_forall_ge_iff $ λ c, _),
  rw [tsub_le_iff_right, add_comm, infi_add],
  simp [tsub_le_iff_right, sub_eq_add_neg, add_comm],
end

lemma Inf_add {s : set ℝ≥0∞} : Inf s + a = ⨅b∈s, b + a :=
by simp [Inf_eq_infi, infi_add]

lemma add_infi {a : ℝ≥0∞} : a + infi f = ⨅b, a + f b :=
by rw [add_comm, infi_add]; simp [add_comm]

lemma infi_add_infi (h : ∀i j, ∃k, f k + g k ≤ f i + g j) : infi f + infi g = (⨅a, f a + g a) :=
suffices (⨅a, f a + g a) ≤ infi f + infi g,
  from le_antisymm (le_infi $ assume a, add_le_add (infi_le _ _) (infi_le _ _)) this,
calc (⨅a, f a + g a) ≤ (⨅ a a', f a + g a') :
    le_infi $ assume a, le_infi $ assume a',
      let ⟨k, h⟩ := h a a' in infi_le_of_le k h
  ... = infi f + infi g :
    by simp [add_infi, infi_add]

lemma infi_sum {f : ι → α → ℝ≥0∞} {s : finset α} [nonempty ι]
  (h : ∀(t : finset α) (i j : ι), ∃k, ∀a∈t, f k a ≤ f i a ∧ f k a ≤ f j a) :
  (⨅i, ∑ a in s, f i a) = ∑ a in s, ⨅i, f i a :=
finset.induction_on s (by simp) $ assume a s ha ih,
  have ∀ (i j : ι), ∃ (k : ι), f k a + ∑ b in s, f k b ≤ f i a + ∑ b in s, f j b,
    from assume i j,
    let ⟨k, hk⟩ := h (insert a s) i j in
    ⟨k, add_le_add (hk a (finset.mem_insert_self _ _)).left $ finset.sum_le_sum $
      assume a ha, (hk _ $ finset.mem_insert_of_mem ha).right⟩,
  by simp [ha, ih.symm, infi_add_infi this]

/-- If `x ≠ 0` and `x ≠ ∞`, then right multiplication by `x` maps infimum to infimum.
See also `ennreal.infi_mul` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
lemma infi_mul_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
  infi f * x = ⨅ i, f i * x :=
le_antisymm
  mul_right_mono.map_infi_le
  ((div_le_iff_le_mul (or.inl h0) $ or.inl h).mp $ le_infi $
    λ i, (div_le_iff_le_mul (or.inl h0) $ or.inl h).mpr $ infi_le _ _)

/-- If `x ≠ ∞`, then right multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.infi_mul_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
lemma infi_mul {ι} [nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
  infi f * x = ⨅ i, f i * x :=
begin
  by_cases h0 : x = 0,
  { simp only [h0, mul_zero, infi_const] },
  { exact infi_mul_of_ne h0 h }
end

/-- If `x ≠ ∞`, then left multiplication by `x` maps infimum over a nonempty type to infimum. See
also `ennreal.mul_infi_of_ne` that assumes `x ≠ 0` but does not require `[nonempty ι]`. -/
lemma mul_infi {ι} [nonempty ι] {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h : x ≠ ∞) :
  x * infi f = ⨅ i, x * f i :=
by simpa only [mul_comm] using infi_mul h

/-- If `x ≠ 0` and `x ≠ ∞`, then left multiplication by `x` maps infimum to infimum.
See also `ennreal.mul_infi` that assumes `[nonempty ι]` but does not require `x ≠ 0`. -/
lemma mul_infi_of_ne {ι} {f : ι → ℝ≥0∞} {x : ℝ≥0∞} (h0 : x ≠ 0) (h : x ≠ ∞) :
  x * infi f = ⨅ i, x * f i :=
by simpa only [mul_comm] using infi_mul_of_ne h0 h

/-! `supr_mul`, `mul_supr` and variants are in `topology.instances.ennreal`. -/

end infi

section supr

@[simp] lemma supr_eq_zero {ι : Sort*} {f : ι → ℝ≥0∞} : (⨆ i, f i) = 0 ↔ ∀ i, f i = 0 :=
supr_eq_bot

@[simp] lemma supr_zero_eq_zero {ι : Sort*} : (⨆ i : ι, (0 : ℝ≥0∞)) = 0 :=
by simp

lemma sup_eq_zero {a b : ℝ≥0∞} : a ⊔ b = 0 ↔ a = 0 ∧ b = 0 := sup_eq_bot_iff

lemma supr_coe_nat : (⨆n:ℕ, (n : ℝ≥0∞)) = ∞ :=
(supr_eq_top _).2 $ assume b hb, ennreal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

end supr

end ennreal
