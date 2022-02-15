/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.order.field
import data.nat.basic

/-!
# Cast of naturals

This file defines the *canonical* homomorphism from the natural numbers into a type `α` with `0`,
`1` and `+` (typically an `add_monoid` with one).

## Main declarations

* `cast`: Canonical homomorphism `ℕ → α` where `α` has a `0`, `1` and `+`.
* `bin_cast`: Binary representation version of `cast`.
* `cast_add_monoid_hom`: `cast` bundled as an `add_monoid_hom`.
* `cast_ring_hom`: `cast` bundled as a `ring_hom`.

## Implementation note

Setting up the coercions priorities is tricky. See Note [coercion into rings].
-/

namespace nat
variables {α : Type*}

section
variables [has_zero α] [has_one α] [has_add α]

/-- Canonical homomorphism from `ℕ` to a type `α` with `0`, `1` and `+`. -/
protected def cast : ℕ → α
| 0     := 0
| (n+1) := cast n + 1

/-- Computationally friendlier cast than `nat.cast`, using binary representation. -/
protected def bin_cast (n : ℕ) : α :=
@nat.binary_rec (λ _, α) 0 (λ odd k a, cond odd (a + a + 1) (a + a)) n

/--
Coercions such as `nat.cast_coe` that go from a concrete structure such as
`ℕ` to an arbitrary ring `α` should be set up as follows:
```lean
@[priority 900] instance : has_coe_t ℕ α := ⟨...⟩
```

It needs to be `has_coe_t` instead of `has_coe` because otherwise type-class
inference would loop when constructing the transitive coercion `ℕ → ℕ → ℕ → ...`.
The reduced priority is necessary so that it doesn't conflict with instances
such as `has_coe_t α (option α)`.

For this to work, we reduce the priority of the `coe_base` and `coe_trans`
instances because we want the instances for `has_coe_t` to be tried in the
following order:

 1. `has_coe_t` instances declared in mathlib (such as `has_coe_t α (with_top α)`, etc.)
 2. `coe_base`, which contains instances such as `has_coe (fin n) n`
 3. `nat.cast_coe : has_coe_t ℕ α` etc.
 4. `coe_trans`

If `coe_trans` is tried first, then `nat.cast_coe` doesn't get a chance to apply.
-/
library_note "coercion into rings"
attribute [instance, priority 950] coe_base
attribute [instance, priority 500] coe_trans

-- see note [coercion into rings]
@[priority 900] instance cast_coe : has_coe_t ℕ α := ⟨nat.cast⟩

@[simp, norm_cast] theorem cast_zero : ((0 : ℕ) : α) = 0 := rfl

theorem cast_add_one (n : ℕ) : ((n + 1 : ℕ) : α) = n + 1 := rfl

@[simp, norm_cast, priority 500]
theorem cast_succ (n : ℕ) : ((succ n : ℕ) : α) = n + 1 := rfl

@[simp, norm_cast] theorem cast_ite (P : Prop) [decidable P] (m n : ℕ) :
  (((ite P m n) : ℕ) : α) = ite P (m : α) (n : α) :=
by { split_ifs; refl, }

end

@[simp, norm_cast] theorem cast_one [add_zero_class α] [has_one α] : ((1 : ℕ) : α) = 1 := zero_add _

@[simp, norm_cast] theorem cast_add [add_monoid α] [has_one α] (m) : ∀ n, ((m + n : ℕ) : α) = m + n
| 0     := (add_zero _).symm
| (n+1) := show ((m + n : ℕ) : α) + 1 = m + (n + 1), by rw [cast_add n, add_assoc]

@[simp] lemma bin_cast_eq [add_monoid α] [has_one α] (n : ℕ) :
  (nat.bin_cast n : α) = ((n : ℕ) : α) :=
begin
  rw nat.bin_cast,
  apply binary_rec _ _ n,
  { rw [binary_rec_zero, cast_zero] },
  { intros b k h,
    rw [binary_rec_eq, h],
    { cases b; simp [bit, bit0, bit1] },
    { simp } },
end

/-- `coe : ℕ → α` as an `add_monoid_hom`. -/
def cast_add_monoid_hom (α : Type*) [add_monoid α] [has_one α] : ℕ →+ α :=
{ to_fun := coe,
  map_add' := cast_add,
  map_zero' := cast_zero }

@[simp] lemma coe_cast_add_monoid_hom [add_monoid α] [has_one α] :
  (cast_add_monoid_hom α : ℕ → α) = coe := rfl

@[simp, norm_cast] theorem cast_bit0 [add_monoid α] [has_one α] (n : ℕ) :
  ((bit0 n : ℕ) : α) = bit0 n := cast_add _ _

@[simp, norm_cast] theorem cast_bit1 [add_monoid α] [has_one α] (n : ℕ) :
  ((bit1 n : ℕ) : α) = bit1 n :=
by rw [bit1, cast_add_one, cast_bit0]; refl

lemma cast_two {α : Type*} [add_zero_class α] [has_one α] : ((2 : ℕ) : α) = 2 :=
by rw [cast_add_one, cast_one, bit0]

@[simp, norm_cast] theorem cast_pred [add_group α] [has_one α] :
  ∀ {n}, 0 < n → ((n - 1 : ℕ) : α) = n - 1
| (n+1) h := (add_sub_cancel (n:α) 1).symm

@[simp, norm_cast] theorem cast_sub [add_group α] [has_one α] {m n} (h : m ≤ n) :
  ((n - m : ℕ) : α) = n - m :=
eq_sub_of_add_eq $ by rw [← cast_add, tsub_add_cancel_of_le h]

@[simp, norm_cast] theorem cast_mul [non_assoc_semiring α] (m) : ∀ n, ((m * n : ℕ) : α) = m * n
| 0     := (mul_zero _).symm
| (n+1) := (cast_add _ _).trans $
show ((m * n : ℕ) : α) + m = m * (n + 1), by rw [cast_mul n, left_distrib, mul_one]

@[simp] theorem cast_dvd {α : Type*} [field α] {m n : ℕ} (n_dvd : n ∣ m) (n_nonzero : (n:α) ≠ 0) :
  ((m / n : ℕ) : α) = m / n :=
begin
  rcases n_dvd with ⟨k, rfl⟩,
  have : n ≠ 0, {rintro rfl, simpa using n_nonzero},
  rw nat.mul_div_cancel_left _ (pos_iff_ne_zero.2 this),
  rw [nat.cast_mul, mul_div_cancel_left _ n_nonzero],
end

/-- `coe : ℕ → α` as a `ring_hom` -/
def cast_ring_hom (α : Type*) [non_assoc_semiring α] : ℕ →+* α :=
{ to_fun := coe,
  map_one' := cast_one,
  map_mul' := cast_mul,
  .. cast_add_monoid_hom α }

@[simp] lemma coe_cast_ring_hom [non_assoc_semiring α] : (cast_ring_hom α : ℕ → α) = coe := rfl

lemma cast_commute [non_assoc_semiring α] (n : ℕ) (x : α) : commute ↑n x :=
nat.rec_on n (commute.zero_left x) $ λ n ihn, ihn.add_left $ commute.one_left x

lemma cast_comm [non_assoc_semiring α] (n : ℕ) (x : α) : (n : α) * x = x * n :=
(cast_commute n x).eq

lemma commute_cast [non_assoc_semiring α] (x : α) (n : ℕ) : commute x n :=
(n.cast_commute x).symm

section

variables [ordered_semiring α]

@[simp] theorem cast_nonneg : ∀ n : ℕ, 0 ≤ (n : α)
| 0     := le_rfl
| (n+1) := add_nonneg (cast_nonneg n) zero_le_one

@[mono] theorem mono_cast : monotone (coe : ℕ → α) :=
λ m n h, let ⟨k, hk⟩ := le_iff_exists_add.1 h in by simp [hk]

variable [nontrivial α]

theorem strict_mono_cast : strict_mono (coe : ℕ → α) :=
λ m n h, nat.le_induction (lt_add_of_pos_right _ zero_lt_one)
  (λ n _ h, lt_add_of_lt_of_pos' h zero_lt_one) _ h

@[simp, norm_cast] theorem cast_le {m n : ℕ} :
  (m : α) ≤ n ↔ m ≤ n :=
strict_mono_cast.le_iff_le

@[simp, norm_cast, mono] theorem cast_lt {m n : ℕ} : (m : α) < n ↔ m < n :=
strict_mono_cast.lt_iff_lt

@[simp] theorem cast_pos {n : ℕ} : (0 : α) < n ↔ 0 < n :=
by rw [← cast_zero, cast_lt]

lemma cast_add_one_pos (n : ℕ) : 0 < (n : α) + 1 :=
  add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

@[simp, norm_cast] theorem one_lt_cast {n : ℕ} : 1 < (n : α) ↔ 1 < n :=
by rw [← cast_one, cast_lt]

@[simp, norm_cast] theorem one_le_cast {n : ℕ} : 1 ≤ (n : α) ↔ 1 ≤ n :=
by rw [← cast_one, cast_le]

@[simp, norm_cast] theorem cast_lt_one {n : ℕ} : (n : α) < 1 ↔ n = 0 :=
by rw [← cast_one, cast_lt, lt_succ_iff, le_zero_iff]

@[simp, norm_cast] theorem cast_le_one {n : ℕ} : (n : α) ≤ 1 ↔ n ≤ 1 :=
by rw [← cast_one, cast_le]

end

@[simp, norm_cast] theorem cast_min [linear_ordered_semiring α] {a b : ℕ} :
  (↑(min a b) : α) = min a b :=
(@mono_cast α _).map_min

@[simp, norm_cast] theorem cast_max [linear_ordered_semiring α] {a b : ℕ} :
  (↑(max a b) : α) = max a b :=
(@mono_cast α _).map_max

@[simp, norm_cast] theorem abs_cast [linear_ordered_ring α] (a : ℕ) :
  |(a : α)| = a :=
abs_of_nonneg (cast_nonneg a)

lemma coe_nat_dvd [semiring α] {m n : ℕ} (h : m ∣ n) : (m : α) ∣ (n : α) :=
(nat.cast_ring_hom α).map_dvd h

alias coe_nat_dvd ← has_dvd.dvd.nat_cast

section linear_ordered_field
variables [linear_ordered_field α]

/-- Natural division is always less than division in the field. -/
lemma cast_div_le {m n : ℕ} : ((m / n : ℕ) : α) ≤ m / n :=
begin
  cases n,
  { rw [cast_zero, div_zero, nat.div_zero, cast_zero] },
  rwa [le_div_iff, ←nat.cast_mul],
  exact nat.cast_le.2 (nat.div_mul_le_self m n.succ),
  { exact nat.cast_pos.2 n.succ_pos }
end

lemma inv_pos_of_nat {n : ℕ} : 0 < ((n : α) + 1)⁻¹ :=
inv_pos.2 $ add_pos_of_nonneg_of_pos n.cast_nonneg zero_lt_one

lemma one_div_pos_of_nat {n : ℕ} : 0 < 1 / ((n : α) + 1) :=
by { rw one_div, exact inv_pos_of_nat }

lemma one_div_le_one_div {n m : ℕ} (h : n ≤ m) : 1 / ((m : α) + 1) ≤ 1 / ((n : α) + 1) :=
by { refine one_div_le_one_div_of_le _ _, exact nat.cast_add_one_pos _, simpa }

lemma one_div_lt_one_div {n m : ℕ} (h : n < m) : 1 / ((m : α) + 1) < 1 / ((n : α) + 1) :=
by { refine one_div_lt_one_div_of_lt _ _, exact nat.cast_add_one_pos _, simpa }

end linear_ordered_field

end nat

namespace prod

variables {α : Type*} {β : Type*} [has_zero α] [has_one α] [has_add α]
  [has_zero β] [has_one β] [has_add β]

@[simp] lemma fst_nat_cast (n : ℕ) : (n : α × β).fst = n :=
by induction n; simp *

@[simp] lemma snd_nat_cast (n : ℕ) : (n : α × β).snd = n :=
by induction n; simp *

end prod

section add_monoid_hom_class

variables {A B F : Type*} [add_monoid A] [add_monoid B] [has_one B]

lemma ext_nat' [add_monoid_hom_class F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
fun_like.ext f g $ begin
  apply nat.rec,
  { simp only [nat.nat_zero_eq_zero, map_zero] },
  simp [nat.succ_eq_add_one, h] {contextual := tt}
end

@[ext] lemma add_monoid_hom.ext_nat : ∀ {f g : ℕ →+ A}, ∀ h : f 1 = g 1, f = g := ext_nat'

variable [has_one A]

-- these versions are primed so that the `ring_hom_class` versions aren't
lemma eq_nat_cast' [add_monoid_hom_class F ℕ A] (f : F) (h1 : f 1 = 1) :
  ∀ n : ℕ, f n = n
| 0     := by simp
| (n+1) := by rw [map_add, h1, eq_nat_cast' n, nat.cast_add_one]

lemma map_nat_cast' [add_monoid_hom_class F A B] (f : F) (h : f 1 = 1) : ∀ (n : ℕ), f n = n
| 0     := by simp
| (n+1) := by rw [nat.cast_add, map_add, nat.cast_add, map_nat_cast', nat.cast_one, h, nat.cast_one]

end add_monoid_hom_class

section monoid_with_zero_hom_class

variables {A F : Type*} [monoid_with_zero A]

/-- If two `monoid_with_zero_hom`s agree on the positive naturals they are equal. -/
theorem ext_nat'' [monoid_with_zero_hom_class F ℕ A] (f g : F)
  (h_pos : ∀ {n : ℕ}, 0 < n → f n = g n) : f = g :=
begin
  apply fun_like.ext,
  rintro (_|n),
  { simp },
  exact h_pos n.succ_pos
end

@[ext] theorem monoid_with_zero_hom.ext_nat :
  ∀ {f g : ℕ →*₀ A}, (∀ {n : ℕ}, 0 < n → f n = g n) → f = g := ext_nat''

end monoid_with_zero_hom_class

section ring_hom_class

variables {R S F : Type*} [non_assoc_semiring R] [non_assoc_semiring S]

@[simp] lemma eq_nat_cast [ring_hom_class F ℕ R] (f : F) : ∀ n, f n = n :=
eq_nat_cast' f $ map_one f

@[simp] lemma map_nat_cast [ring_hom_class F R S] (f : F) : ∀ n : ℕ, f (n : R) = n :=
map_nat_cast' f $ map_one f

lemma ext_nat [ring_hom_class F ℕ R] (f g : F) : f = g :=
ext_nat' f g $ by simp only [map_one]

end ring_hom_class

@[simp, norm_cast] theorem nat.cast_id (n : ℕ) : ↑n = n :=
(eq_nat_cast (ring_hom.id ℕ) n).symm

@[simp] theorem nat.cast_with_bot : ∀ (n : ℕ),
  @coe ℕ (with_bot ℕ) (@coe_to_lift _ _ nat.cast_coe) n = n
| 0     := rfl
| (n+1) := by rw [with_bot.coe_add, nat.cast_add, nat.cast_with_bot n]; refl

-- I don't think `ring_hom_class` is good here, because of the `subsingleton` TC slowness
instance nat.subsingleton_ring_hom {R : Type*} [non_assoc_semiring R] : subsingleton (ℕ →+* R) :=
⟨ext_nat⟩

namespace with_top
variables {α : Type*}

variables [has_zero α] [has_one α] [has_add α]

@[simp, norm_cast] lemma coe_nat : ∀ (n : ℕ), ((n : α) : with_top α) = n
| 0     := rfl
| (n+1) := by { push_cast, rw [coe_nat n] }

@[simp] lemma nat_ne_top (n : nat) : (n : with_top α) ≠ ⊤ :=
by { rw [←coe_nat n], apply coe_ne_top }

@[simp] lemma top_ne_nat (n : nat) : (⊤ : with_top α) ≠ n :=
by { rw [←coe_nat n], apply top_ne_coe }

lemma add_one_le_of_lt {i n : with_top ℕ} (h : i < n) : i + 1 ≤ n :=
begin
  cases n, { exact le_top },
  cases i, { exact (not_le_of_lt h le_top).elim },
  exact with_top.coe_le_coe.2 (with_top.coe_lt_coe.1 h)
end

lemma one_le_iff_pos {n : with_top ℕ} : 1 ≤ n ↔ 0 < n :=
⟨lt_of_lt_of_le (coe_lt_coe.mpr zero_lt_one),
  λ h, by simpa only [zero_add] using add_one_le_of_lt h⟩

@[elab_as_eliminator]
lemma nat_induction {P : with_top ℕ → Prop} (a : with_top ℕ)
  (h0 : P 0) (hsuc : ∀n:ℕ, P n → P n.succ) (htop : (∀n : ℕ, P n) → P ⊤) : P a :=
begin
  have A : ∀n:ℕ, P n := λ n, nat.rec_on n h0 hsuc,
  cases a,
  { exact htop A },
  { exact A a }
end

end with_top

namespace pi

variables {α β : Type*}

lemma nat_apply [has_zero β] [has_one β] [has_add β] :
  ∀ (n : ℕ) (a : α), (n : α → β) a = n
| 0     a := rfl
| (n+1) a := by rw [nat.cast_succ, nat.cast_succ, add_apply, nat_apply, one_apply]

@[simp] lemma coe_nat [has_zero β] [has_one β] [has_add β] (n : ℕ) :
  (n : α → β) = λ _, n :=
by { ext, rw pi.nat_apply }

end pi
