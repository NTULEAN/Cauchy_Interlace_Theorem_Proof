/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import algebra.group.with_one
import algebra.group.type_tags
import algebra.group.prod
import algebra.order.monoid_lemmas
import order.bounded_order
import order.min_max
import order.hom.basic

/-!
# Ordered monoids

This file develops the basics of ordered monoids.

## Implementation details

Unfortunately, the number of `'` appended to lemmas in this file
may differ between the multiplicative and the additive version of a lemma.
The reason is that we did not want to change existing names in the library.
-/

set_option old_structure_cmd true
open function

universe u
variable {α : Type u}

/-- An ordered commutative monoid is a commutative monoid
with a partial order such that `a ≤ b → c * a ≤ c * b` (multiplication is monotone)
-/
@[protect_proj, ancestor comm_monoid partial_order]
class ordered_comm_monoid (α : Type*) extends comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)

/-- An ordered (additive) commutative monoid is a commutative monoid
  with a partial order such that `a ≤ b → c + a ≤ c + b` (addition is monotone)
-/
@[protect_proj, ancestor add_comm_monoid partial_order]
class ordered_add_comm_monoid (α : Type*) extends add_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)

attribute [to_additive] ordered_comm_monoid

section ordered_instances

@[to_additive]
instance ordered_comm_monoid.to_covariant_class_left (M : Type*) [ordered_comm_monoid M] :
  covariant_class M M (*) (≤) :=
{ elim := λ a b c bc, ordered_comm_monoid.mul_le_mul_left _ _ bc a }

/- This instance can be proven with `by apply_instance`.  However, `with_bot ℕ` does not
pick up a `covariant_class M M (function.swap (*)) (≤)` instance without it (see PR #7940). -/
@[to_additive]
instance ordered_comm_monoid.to_covariant_class_right (M : Type*) [ordered_comm_monoid M] :
  covariant_class M M (swap (*)) (≤) :=
covariant_swap_mul_le_of_covariant_mul_le M

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`left_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (*) (≤)`
implies `covariant_class M M (*) (<)` . -/
@[to_additive] lemma has_mul.to_covariant_class_left
  (M : Type*) [has_mul M] [linear_order M] [covariant_class M M (*) (<)] :
  covariant_class M M (*) (≤) :=
{ elim := λ a b c bc, by
  { rcases eq_or_lt_of_le bc with rfl | bc,
    { exact rfl.le },
    { exact (mul_lt_mul_left' bc a).le } } }

/- This is not an instance, to avoid creating a loop in the type-class system: in a
`right_cancel_semigroup` with a `partial_order`, assuming `covariant_class M M (swap (*)) (<)`
implies `covariant_class M M (swap (*)) (≤)` . -/
@[to_additive] lemma has_mul.to_covariant_class_right
  (M : Type*) [has_mul M] [linear_order M] [covariant_class M M (swap (*)) (<)] :
  covariant_class M M (swap (*)) (≤) :=
{ elim := λ a b c bc, by
  { rcases eq_or_lt_of_le bc with rfl | bc,
    { exact rfl.le },
    { exact (mul_lt_mul_right' bc a).le } } }

end ordered_instances

/-- An `ordered_comm_monoid` with one-sided 'division' in the sense that
if `a ≤ b`, there is some `c` for which `a * c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_monoid`. -/
class has_exists_mul_of_le (α : Type u) [ordered_comm_monoid α] : Prop :=
(exists_mul_of_le : ∀ {a b : α}, a ≤ b → ∃ (c : α), b = a * c)

/-- An `ordered_add_comm_monoid` with one-sided 'subtraction' in the sense that
if `a ≤ b`, then there is some `c` for which `a + c = b`. This is a weaker version
of the condition on canonical orderings defined by `canonically_ordered_add_monoid`. -/
class has_exists_add_of_le (α : Type u) [ordered_add_comm_monoid α] : Prop :=
(exists_add_of_le : ∀ {a b : α}, a ≤ b → ∃ (c : α), b = a + c)

attribute [to_additive] has_exists_mul_of_le

export has_exists_mul_of_le (exists_mul_of_le)

export has_exists_add_of_le (exists_add_of_le)

/-- A linearly ordered additive commutative monoid. -/
@[protect_proj, ancestor linear_order ordered_add_comm_monoid]
class linear_ordered_add_comm_monoid (α : Type*)
  extends linear_order α, ordered_add_comm_monoid α.

/-- A linearly ordered commutative monoid. -/
@[protect_proj, ancestor linear_order ordered_comm_monoid, to_additive]
class linear_ordered_comm_monoid (α : Type*)
  extends linear_order α, ordered_comm_monoid α.

/-- A linearly ordered commutative monoid with a zero element. -/
class linear_ordered_comm_monoid_with_zero (α : Type*)
  extends linear_ordered_comm_monoid α, comm_monoid_with_zero α :=
(zero_le_one : (0 : α) ≤ 1)

/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined.` -/
@[protect_proj, ancestor linear_ordered_add_comm_monoid has_top]
class linear_ordered_add_comm_monoid_with_top (α : Type*)
  extends linear_ordered_add_comm_monoid α, has_top α :=
(le_top : ∀ x : α, x ≤ ⊤)
(top_add' : ∀ x : α, ⊤ + x = ⊤)

@[priority 100]    -- see Note [lower instance priority]
instance linear_ordered_add_comm_monoid_with_top.to_order_top (α : Type u)
  [h : linear_ordered_add_comm_monoid_with_top α] : order_top α :=
{ ..h }

section linear_ordered_add_comm_monoid_with_top
variables [linear_ordered_add_comm_monoid_with_top α] {a b : α}

@[simp]
lemma top_add (a : α) : ⊤ + a = ⊤ := linear_ordered_add_comm_monoid_with_top.top_add' a

@[simp]
lemma add_top (a : α) : a + ⊤ = ⊤ :=
trans (add_comm _ _) (top_add _)

end linear_ordered_add_comm_monoid_with_top

/-- Pullback an `ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.ordered_comm_monoid [ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_comm_monoid β :=
{ mul_le_mul_left := λ a b ab c, show f (c * a) ≤ f (c * b), by
  { rw [mul, mul], apply mul_le_mul_left', exact ab },
  ..partial_order.lift f hf,
  ..hf.comm_monoid f one mul }

/-- Pullback a `linear_ordered_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_add_comm_monoid
"Pullback an `ordered_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_comm_monoid [linear_ordered_comm_monoid α] {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  linear_ordered_comm_monoid β :=
{ .. hf.ordered_comm_monoid f one mul,
  .. linear_order.lift f hf }

lemma bit0_pos [ordered_add_comm_monoid α] {a : α} (h : 0 < a) : 0 < bit0 a :=
add_pos h h

namespace units

@[to_additive]
instance [monoid α] [preorder α] : preorder αˣ :=
preorder.lift (coe : αˣ → α)

@[simp, norm_cast, to_additive]
theorem coe_le_coe [monoid α] [preorder α] {a b : αˣ} :
  (a : α) ≤ b ↔ a ≤ b := iff.rfl

@[simp, norm_cast, to_additive]
theorem coe_lt_coe [monoid α] [preorder α] {a b : αˣ} :
  (a : α) < b ↔ a < b := iff.rfl

@[to_additive]
instance [monoid α] [partial_order α] : partial_order αˣ :=
partial_order.lift coe units.ext

@[to_additive]
instance [monoid α] [linear_order α] : linear_order αˣ :=
linear_order.lift coe units.ext

@[simp, norm_cast, to_additive]
theorem max_coe [monoid α] [linear_order α] {a b : αˣ} :
  (↑(max a b) : α) = max a b :=
by by_cases b ≤ a; simp [max_def, h]

@[simp, norm_cast, to_additive]
theorem min_coe [monoid α] [linear_order α] {a b : αˣ} :
  (↑(min a b) : α) = min a b :=
by by_cases a ≤ b; simp [min_def, h]

end units

namespace with_zero

local attribute [semireducible] with_zero

instance [preorder α] : preorder (with_zero α) := with_bot.preorder

instance [partial_order α] : partial_order (with_zero α) := with_bot.partial_order

instance [partial_order α] : order_bot (with_zero α) := with_bot.order_bot

lemma zero_le [partial_order α] (a : with_zero α) : 0 ≤ a := order_bot.bot_le a

lemma zero_lt_coe [preorder α] (a : α) : (0 : with_zero α) < a := with_bot.bot_lt_coe a

@[simp, norm_cast] lemma coe_lt_coe [partial_order α] {a b : α} : (a : with_zero α) < b ↔ a < b :=
with_bot.coe_lt_coe

@[simp, norm_cast] lemma coe_le_coe [partial_order α] {a b : α} : (a : with_zero α) ≤ b ↔ a ≤ b :=
with_bot.coe_le_coe

instance [lattice α] : lattice (with_zero α) := with_bot.lattice

instance [linear_order α] : linear_order (with_zero α) := with_bot.linear_order

lemma mul_le_mul_left {α : Type u} [has_mul α] [preorder α]
  [covariant_class α α (*) (≤)] :
  ∀ (a b : with_zero α),
    a ≤ b → ∀ (c : with_zero α), c * a ≤ c * b :=
begin
  rintro (_ | a) (_ | b) h (_ | c);
  try { exact λ f hf, option.no_confusion hf },
  { exact false.elim (not_lt_of_le h (with_zero.zero_lt_coe a))},
  { simp_rw [some_eq_coe] at h ⊢,
    norm_cast at h ⊢,
    exact covariant_class.elim _ h }
end

lemma lt_of_mul_lt_mul_left {α : Type u} [has_mul α] [partial_order α]
  [contravariant_class α α (*) (<)] :
  ∀ (a b c : with_zero α), a * b < a * c → b < c :=
begin
  rintro (_ | a) (_ | b) (_ | c) h;
  try { exact false.elim (lt_irrefl none h) },
  { exact with_zero.zero_lt_coe c },
  { exact false.elim (not_le_of_lt h (with_zero.zero_le _)) },
  { simp_rw [some_eq_coe] at h ⊢,
    norm_cast at h ⊢,
    apply lt_of_mul_lt_mul_left' h }
end

instance [ordered_comm_monoid α] : ordered_comm_monoid (with_zero α) :=
{ mul_le_mul_left := with_zero.mul_le_mul_left,
  ..with_zero.comm_monoid_with_zero,
  ..with_zero.partial_order }

/-
Note 1 : the below is not an instance because it requires `zero_le`. It seems
like a rather pathological definition because α already has a zero.
Note 2 : there is no multiplicative analogue because it does not seem necessary.
Mathematicians might be more likely to use the order-dual version, where all
elements are ≤ 1 and then 1 is the top element.
-/

/--
If `0` is the least element in `α`, then `with_zero α` is an `ordered_add_comm_monoid`.
-/
def ordered_add_comm_monoid [ordered_add_comm_monoid α]
  (zero_le : ∀ a : α, 0 ≤ a) : ordered_add_comm_monoid (with_zero α) :=
begin
  suffices, refine
  { add_le_add_left := this,
    ..with_zero.partial_order,
    ..with_zero.add_comm_monoid, .. },
  { intros a b h c ca h₂,
    cases b with b,
    { rw le_antisymm h bot_le at h₂,
      exact ⟨_, h₂, le_rfl⟩ },
    cases a with a,
    { change c + 0 = some ca at h₂,
      simp at h₂, simp [h₂],
      exact ⟨_, rfl, by simpa using add_le_add_left (zero_le b) _⟩ },
    { simp at h,
      cases c with c; change some _ = _ at h₂;
        simp [-add_comm] at h₂; subst ca; refine ⟨_, rfl, _⟩,
      { exact h },
      { exact add_le_add_left h _ } } }
end

end with_zero

namespace with_top

section has_one

variables [has_one α]

@[to_additive] instance : has_one (with_top α) := ⟨(1 : α)⟩

@[simp, norm_cast, to_additive] lemma coe_one : ((1 : α) : with_top α) = 1 := rfl

@[simp, norm_cast, to_additive] lemma coe_eq_one {a : α} : (a : with_top α) = 1 ↔ a = 1 :=
coe_eq_coe

@[simp, norm_cast, to_additive] theorem one_eq_coe {a : α} : 1 = (a : with_top α) ↔ a = 1 :=
trans eq_comm coe_eq_one

@[simp, to_additive] theorem top_ne_one : ⊤ ≠ (1 : with_top α) .
@[simp, to_additive] theorem one_ne_top : (1 : with_top α) ≠ ⊤ .

end has_one

instance [has_add α] : has_add (with_top α) :=
⟨λ o₁ o₂, o₁.bind (λ a, o₂.map (λ b, a + b))⟩

@[norm_cast] lemma coe_add [has_add α] {a b : α} : ((a + b : α) : with_top α) = a + b := rfl

@[norm_cast] lemma coe_bit0 [has_add α] {a : α} : ((bit0 a : α) : with_top α) = bit0 a := rfl

@[norm_cast]
lemma coe_bit1 [has_add α] [has_one α] {a : α} : ((bit1 a : α) : with_top α) = bit1 a := rfl

@[simp] lemma add_top [has_add α] : ∀{a : with_top α}, a + ⊤ = ⊤
| none := rfl
| (some a) := rfl

@[simp] lemma top_add [has_add α] {a : with_top α} : ⊤ + a = ⊤ := rfl

lemma add_eq_top [has_add α] {a b : with_top α} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by cases a; cases b; simp [none_eq_top, some_eq_coe, ←with_top.coe_add, ←with_zero.coe_add]

lemma add_lt_top [has_add α] [partial_order α] {a b : with_top α} : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ :=
by simp [lt_top_iff_ne_top, add_eq_top, not_or_distrib]

lemma add_eq_coe [has_add α] : ∀ {a b : with_top α} {c : α},
  a + b = c ↔ ∃ (a' b' : α), ↑a' = a ∧ ↑b' = b ∧ a' + b' = c
| none b c := by simp [none_eq_top]
| (some a) none c := by simp [none_eq_top]
| (some a) (some b) c :=
    by simp only [some_eq_coe, ← coe_add, coe_eq_coe, exists_and_distrib_left, exists_eq_left]

@[simp] lemma add_coe_eq_top_iff [has_add α] {x : with_top α} {y : α} : x + y = ⊤ ↔ x = ⊤ :=
by { induction x using with_top.rec_top_coe; simp [← coe_add, -with_zero.coe_add] }

@[simp] lemma coe_add_eq_top_iff [has_add α] {x : α} {y : with_top α} : ↑x + y = ⊤ ↔ y = ⊤ :=
by { induction y using with_top.rec_top_coe; simp [← coe_add, -with_zero.coe_add] }

instance [add_semigroup α] : add_semigroup (with_top α) :=
{ add_assoc := begin
    repeat { refine with_top.rec_top_coe _ _; try { intro }};
    simp [←with_top.coe_add, add_assoc]
  end,
  ..with_top.has_add }

instance [add_comm_semigroup α] : add_comm_semigroup (with_top α) :=
{ add_comm :=
  begin
    repeat { refine with_top.rec_top_coe _ _; try { intro }};
    simp [←with_top.coe_add, add_comm]
  end,
  ..with_top.add_semigroup }

instance [add_monoid α] : add_monoid (with_top α) :=
{ zero_add :=
  begin
    refine with_top.rec_top_coe _ _,
    { simpa },
    { intro,
      rw [←with_top.coe_zero, ←with_top.coe_add, zero_add] }
  end,
  add_zero :=
  begin
    refine with_top.rec_top_coe _ _,
    { simpa },
    { intro,
      rw [←with_top.coe_zero, ←with_top.coe_add, add_zero] }
  end,
  ..with_top.has_zero,
  ..with_top.add_semigroup }

instance [add_comm_monoid α] : add_comm_monoid (with_top α) :=
{ ..with_top.add_monoid, ..with_top.add_comm_semigroup }

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_top α) :=
{ add_le_add_left :=
    begin
      rintros a b h (_|c), { simp [none_eq_top] },
      rcases b with (_|b), { simp [none_eq_top] },
      rcases le_coe_iff.1 h with ⟨a, rfl, h⟩,
      simp only [some_eq_coe, ← coe_add, coe_le_coe] at h ⊢,
      exact add_le_add_left h c
    end,
  ..with_top.partial_order, ..with_top.add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] :
  linear_ordered_add_comm_monoid_with_top (with_top α) :=
{ top_add' := λ x, with_top.top_add,
  ..with_top.order_top,
  ..with_top.linear_order,
  ..with_top.ordered_add_comm_monoid,
  ..option.nontrivial }

/-- Coercion from `α` to `with_top α` as an `add_monoid_hom`. -/
def coe_add_hom [add_monoid α] : α →+ with_top α :=
⟨coe, rfl, λ _ _, rfl⟩

@[simp] lemma coe_coe_add_hom [add_monoid α] : ⇑(coe_add_hom : α →+ with_top α) = coe := rfl

@[simp] lemma zero_lt_top [ordered_add_comm_monoid α] : (0 : with_top α) < ⊤ :=
coe_lt_top 0

@[simp, norm_cast] lemma zero_lt_coe [ordered_add_comm_monoid α] (a : α) :
  (0 : with_top α) < a ↔ 0 < a :=
coe_lt_coe

end with_top

namespace with_bot

instance [has_zero α] : has_zero (with_bot α) := with_top.has_zero
instance [has_one α] : has_one (with_bot α) := with_top.has_one
instance [add_semigroup α] : add_semigroup (with_bot α) := with_top.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (with_bot α) := with_top.add_comm_semigroup
instance [add_monoid α] : add_monoid (with_bot α) := with_top.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (with_bot α) :=  with_top.add_comm_monoid

instance [ordered_add_comm_monoid α] : ordered_add_comm_monoid (with_bot α) :=
begin
  suffices, refine
  { add_le_add_left := this,
    ..with_bot.partial_order,
    ..with_bot.add_comm_monoid, ..},
  { intros a b h c ca h₂,
    cases c with c, {cases h₂},
    cases a with a; cases h₂,
    cases b with b, {cases le_antisymm h bot_le},
    simp at h,
    exact ⟨_, rfl, add_le_add_left h _⟩, }
end

instance [linear_ordered_add_comm_monoid α] : linear_ordered_add_comm_monoid (with_bot α) :=
{ ..with_bot.linear_order,
  ..with_bot.ordered_add_comm_monoid }

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_zero [has_zero α] : ((0 : α) : with_bot α) = 0 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_one [has_one α] : ((1 : α) : with_bot α) = 1 := rfl

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_eq_zero {α : Type*}
  [add_monoid α] {a : α} : (a : with_bot α) = 0 ↔ a = 0 :=
by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_add [add_semigroup α] (a b : α) : ((a + b : α) : with_bot α) = a + b := by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_bit0 [add_semigroup α] {a : α} : ((bit0 a : α) : with_bot α) = bit0 a :=
by norm_cast

-- `by norm_cast` proves this lemma, so I did not tag it with `norm_cast`
lemma coe_bit1 [add_semigroup α] [has_one α] {a : α} : ((bit1 a : α) : with_bot α) = bit1 a :=
by norm_cast

@[simp] lemma bot_add [add_semigroup α] (a : with_bot α) : ⊥ + a = ⊥ := rfl

@[simp] lemma add_bot [add_semigroup α] (a : with_bot α) : a + ⊥ = ⊥ := by cases a; refl

@[simp] lemma add_eq_bot [add_semigroup α] {m n : with_bot α} :
  m + n = ⊥ ↔ m = ⊥ ∨ n = ⊥ :=
with_top.add_eq_top

end with_bot

/-- A canonically ordered additive monoid is an ordered commutative additive monoid
  in which the ordering coincides with the subtractibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a + c`.
  This is satisfied by the natural numbers, for example, but not
  the integers or other nontrivial `ordered_add_comm_group`s. -/
@[protect_proj, ancestor ordered_add_comm_monoid has_bot]
class canonically_ordered_add_monoid (α : Type*) extends ordered_add_comm_monoid α, has_bot α :=
(bot_le : ∀ x : α, ⊥ ≤ x)
(le_iff_exists_add : ∀ a b : α, a ≤ b ↔ ∃ c, b = a + c)

@[priority 100]  -- see Note [lower instance priority]
instance canonically_ordered_add_monoid.to_order_bot (α : Type u)
  [h : canonically_ordered_add_monoid α] : order_bot α :=
{ ..h }

/-- A canonically ordered monoid is an ordered commutative monoid
  in which the ordering coincides with the divisibility relation,
  which is to say, `a ≤ b` iff there exists `c` with `b = a * c`.
  Examples seem rare; it seems more likely that the `order_dual`
  of a naturally-occurring lattice satisfies this than the lattice
  itself (for example, dual of the lattice of ideals of a PID or
  Dedekind domain satisfy this; collections of all things ≤ 1 seem to
  be more natural that collections of all things ≥ 1).
-/
@[protect_proj, ancestor ordered_comm_monoid has_bot, to_additive]
class canonically_ordered_monoid (α : Type*) extends ordered_comm_monoid α, has_bot α :=
(bot_le : ∀ x : α, ⊥ ≤ x)
(le_iff_exists_mul : ∀ a b : α, a ≤ b ↔ ∃ c, b = a * c)

@[priority 100, to_additive]  -- see Note [lower instance priority]
instance canonically_ordered_monoid.to_order_bot (α : Type u)
  [h : canonically_ordered_monoid α] : order_bot α :=
{ ..h }

section canonically_ordered_monoid

variables [canonically_ordered_monoid α] {a b c d : α}

@[to_additive]
lemma le_iff_exists_mul : a ≤ b ↔ ∃c, b = a * c :=
canonically_ordered_monoid.le_iff_exists_mul a b

@[to_additive]
lemma self_le_mul_right (a b : α) : a ≤ a * b :=
le_iff_exists_mul.mpr ⟨b, rfl⟩

@[to_additive]
lemma self_le_mul_left (a b : α) : a ≤ b * a :=
by { rw [mul_comm], exact self_le_mul_right a b }

@[simp, to_additive zero_le] lemma one_le (a : α) : 1 ≤ a :=
le_iff_exists_mul.mpr ⟨a, (one_mul _).symm⟩

@[simp, to_additive] lemma bot_eq_one : (⊥ : α) = 1 :=
le_antisymm bot_le (one_le ⊥)

@[simp, to_additive] lemma mul_eq_one_iff : a * b = 1 ↔ a = 1 ∧ b = 1 :=
mul_eq_one_iff' (one_le _) (one_le _)

@[simp, to_additive] lemma le_one_iff_eq_one : a ≤ 1 ↔ a = 1 :=
iff.intro
  (assume h, le_antisymm h (one_le a))
  (assume h, h ▸ le_refl a)

@[to_additive] lemma one_lt_iff_ne_one : 1 < a ↔ a ≠ 1 :=
iff.intro ne_of_gt $ assume hne, lt_of_le_of_ne (one_le _) hne.symm

@[to_additive] lemma exists_pos_mul_of_lt (h : a < b) : ∃ c > 1, a * c = b :=
begin
  obtain ⟨c, hc⟩ := le_iff_exists_mul.1 h.le,
  refine ⟨c, one_lt_iff_ne_one.2 _, hc.symm⟩,
  rintro rfl,
  simpa [hc, lt_irrefl] using h
end

@[to_additive] lemma le_mul_left (h : a ≤ c) : a ≤ b * c :=
calc a = 1 * a : by simp
  ... ≤ b * c : mul_le_mul' (one_le _) h

@[to_additive] lemma le_mul_self : a ≤ b * a :=
le_mul_left (le_refl a)

@[to_additive] lemma le_mul_right (h : a ≤ b) : a ≤ b * c :=
calc a = a * 1 : by simp
  ... ≤ b * c : mul_le_mul' h (one_le _)

@[to_additive] lemma le_self_mul : a ≤ a * c :=
le_mul_right (le_refl a)

@[to_additive]
lemma lt_iff_exists_mul [covariant_class α α (*) (<)] : a < b ↔ ∃ c > 1, b = a * c :=
begin
  simp_rw [lt_iff_le_and_ne, and_comm, le_iff_exists_mul, ← exists_and_distrib_left, exists_prop],
  apply exists_congr, intro c,
  rw [and.congr_left_iff, gt_iff_lt], rintro rfl,
  split,
  { rw [one_lt_iff_ne_one], apply mt, rintro rfl, rw [mul_one] },
  { rw [← (self_le_mul_right a c).lt_iff_ne], apply lt_mul_of_one_lt_right' }
end

-- This instance looks absurd: a monoid already has a zero
/-- Adding a new zero to a canonically ordered additive monoid produces another one. -/
instance with_zero.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] :
  canonically_ordered_add_monoid (with_zero α) :=
{ le_iff_exists_add := λ a b, begin
    apply with_zero.cases_on a,
    { exact iff_of_true bot_le ⟨b, (zero_add b).symm⟩ },
    apply with_zero.cases_on b,
    { intro b',
      refine iff_of_false (mt (le_antisymm bot_le) (by simp)) (not_exists.mpr (λ c, _)),
      apply with_zero.cases_on c;
      simp [←with_zero.coe_add] },
    { simp only [le_iff_exists_add, with_zero.coe_le_coe],
      intros,
      split; rintro ⟨c, h⟩,
      { exact ⟨c, congr_arg coe h⟩ },
      { induction c using with_zero.cases_on,
        { refine ⟨0, _⟩,
          simpa using h },
        { refine ⟨c, _⟩,
          simpa [←with_zero.coe_add] using h } } }
  end,
  .. with_zero.order_bot,
  .. with_zero.ordered_add_comm_monoid zero_le }

instance with_top.canonically_ordered_add_monoid {α : Type u} [canonically_ordered_add_monoid α] :
  canonically_ordered_add_monoid (with_top α) :=
{ le_iff_exists_add := assume a b,
  match a, b with
  | a, none     := show a ≤ ⊤ ↔ ∃c, ⊤ = a + c, by simp; refine ⟨⊤, _⟩; cases a; refl
  | (some a), (some b) := show (a:with_top α) ≤ ↑b ↔ ∃c:with_top α, ↑b = ↑a + c,
    begin
      simp [canonically_ordered_add_monoid.le_iff_exists_add, -add_comm],
      split,
      { rintro ⟨c, rfl⟩, refine ⟨c, _⟩, norm_cast },
      { exact assume h, match b, h with _, ⟨some c, rfl⟩ := ⟨_, rfl⟩ end }
    end
  | none, some b := show (⊤ : with_top α) ≤ b ↔ ∃c:with_top α, ↑b = ⊤ + c, by simp
  end,
  .. with_top.order_bot,
  .. with_top.ordered_add_comm_monoid }

@[priority 100, to_additive]
instance canonically_ordered_monoid.has_exists_mul_of_le (α : Type u)
  [canonically_ordered_monoid α] : has_exists_mul_of_le α :=
{ exists_mul_of_le := λ a b hab, le_iff_exists_mul.mp hab }

end canonically_ordered_monoid

lemma pos_of_gt {M : Type*} [canonically_ordered_add_monoid M] {n m : M} (h : n < m) : 0 < m :=
lt_of_le_of_lt (zero_le _) h

/-- A canonically linear-ordered additive monoid is a canonically ordered additive monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor canonically_ordered_add_monoid linear_order]
class canonically_linear_ordered_add_monoid (α : Type*)
      extends canonically_ordered_add_monoid α, linear_order α

/-- A canonically linear-ordered monoid is a canonically ordered monoid
    whose ordering is a linear order. -/
@[protect_proj, ancestor canonically_ordered_monoid linear_order, to_additive]
class canonically_linear_ordered_monoid (α : Type*)
      extends canonically_ordered_monoid α, linear_order α

section canonically_linear_ordered_monoid
variables [canonically_linear_ordered_monoid α]

@[priority 100, to_additive]  -- see Note [lower instance priority]
instance canonically_linear_ordered_monoid.semilattice_sup : semilattice_sup α :=
{ ..linear_order.to_lattice }

instance with_top.canonically_linear_ordered_add_monoid
  (α : Type*) [canonically_linear_ordered_add_monoid α] :
    canonically_linear_ordered_add_monoid (with_top α) :=
{ .. (infer_instance : canonically_ordered_add_monoid (with_top α)),
  .. (infer_instance : linear_order (with_top α)) }

@[to_additive]
lemma min_mul_distrib (a b c : α) : min a (b * c) = min a (min a b * min a c) :=
begin
  cases le_total a b with hb hb,
  { simp [hb, le_mul_right] },
  { cases le_total a c with hc hc,
    { simp [hc, le_mul_left] },
    { simp [hb, hc] } }
end

@[to_additive]
lemma min_mul_distrib' (a b c : α) : min (a * b) c = min (min a c * min b c) c :=
by simpa [min_comm _ c] using min_mul_distrib c a b

@[simp, to_additive]
lemma one_min (a : α) : min 1 a = 1 :=
min_eq_left (one_le a)

@[simp, to_additive]
lemma min_one (a : α) : min a 1 = 1 :=
min_eq_right (one_le a)

end canonically_linear_ordered_monoid

/-- An ordered cancellative additive commutative monoid
is an additive commutative monoid with a partial order,
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor add_cancel_comm_monoid partial_order]
class ordered_cancel_add_comm_monoid (α : Type u)
      extends add_cancel_comm_monoid α, partial_order α :=
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

/-- An ordered cancellative commutative monoid
is a commutative monoid with a partial order,
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor cancel_comm_monoid partial_order, to_additive]
class ordered_cancel_comm_monoid (α : Type u)
      extends cancel_comm_monoid α, partial_order α :=
(mul_le_mul_left       : ∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b)
(le_of_mul_le_mul_left : ∀ a b c : α, a * b ≤ a * c → b ≤ c)

section ordered_cancel_comm_monoid
variables [ordered_cancel_comm_monoid α] {a b c d : α}

@[to_additive]
lemma ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left : ∀ a b c : α, a * b < a * c → b < c :=
λ a b c h, lt_of_le_not_le
  (ordered_cancel_comm_monoid.le_of_mul_le_mul_left a b c h.le) $
  mt (λ h, ordered_cancel_comm_monoid.mul_le_mul_left _ _ h _) (not_le_of_gt h)

@[to_additive]
instance ordered_cancel_comm_monoid.to_contravariant_class_left
  (M : Type*) [ordered_cancel_comm_monoid M] :
  contravariant_class M M (*) (<) :=
{ elim := λ a b c, ordered_cancel_comm_monoid.lt_of_mul_lt_mul_left _ _ _ }

/- This instance can be proven with `by apply_instance`.  However, by analogy with the
instance `ordered_cancel_comm_monoid.to_covariant_class_right` above, I imagine that without
this instance, some Type would not have a `contravariant_class M M (function.swap (*)) (<)`
instance. -/
@[to_additive]
instance ordered_cancel_comm_monoid.to_contravariant_class_right
  (M : Type*) [ordered_cancel_comm_monoid M] :
  contravariant_class M M (swap (*)) (<) :=
contravariant_swap_mul_lt_of_contravariant_mul_lt M

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance ordered_cancel_comm_monoid.to_ordered_comm_monoid : ordered_comm_monoid α :=
{ ..‹ordered_cancel_comm_monoid α› }

/-- Pullback an `ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.ordered_cancel_add_comm_monoid
"Pullback an `ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.ordered_cancel_comm_monoid {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  ordered_cancel_comm_monoid β :=
{ le_of_mul_le_mul_left := λ a b c (bc : f (a * b) ≤ f (a * c)),
    (mul_le_mul_iff_left (f a)).mp (by rwa [← mul, ← mul]),
  ..hf.left_cancel_semigroup f mul,
  ..hf.ordered_comm_monoid f one mul }

end ordered_cancel_comm_monoid

/-! Some lemmas about types that have an ordering and a binary operation, with no
  rules relating them. -/
@[to_additive]
lemma fn_min_mul_fn_max {β} [linear_order α] [comm_semigroup β] (f : α → β) (n m : α) :
  f (min n m) * f (max n m) = f n * f m :=
by { cases le_total n m with h h; simp [h, mul_comm] }

@[to_additive]
lemma min_mul_max [linear_order α] [comm_semigroup α] (n m : α) :
  min n m * max n m = n * m :=
fn_min_mul_fn_max id n m

/-- A linearly ordered cancellative additive commutative monoid
is an additive commutative monoid with a decidable linear order
in which addition is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_add_comm_monoid linear_ordered_add_comm_monoid]
class linear_ordered_cancel_add_comm_monoid (α : Type u)
  extends ordered_cancel_add_comm_monoid α, linear_ordered_add_comm_monoid α

/-- A linearly ordered cancellative commutative monoid
is a commutative monoid with a linear order
in which multiplication is cancellative and monotone. -/
@[protect_proj, ancestor ordered_cancel_comm_monoid linear_ordered_comm_monoid, to_additive]
class linear_ordered_cancel_comm_monoid (α : Type u)
  extends ordered_cancel_comm_monoid α, linear_ordered_comm_monoid α

section covariant_class_mul_le
variables [linear_order α]

section has_mul
variable [has_mul α]

section left
variable [covariant_class α α (*) (≤)]

@[to_additive] lemma min_mul_mul_left (a b c : α) : min (a * b) (a * c) = a * min b c :=
(monotone_id.const_mul' a).map_min.symm

@[to_additive]
lemma max_mul_mul_left (a b c : α) : max (a * b) (a * c) = a * max b c :=
(monotone_id.const_mul' a).map_max.symm

end left

section right
variable [covariant_class α α (function.swap (*)) (≤)]

@[to_additive]
lemma min_mul_mul_right (a b c : α) : min (a * c) (b * c) = min a b * c :=
(monotone_id.mul_const' c).map_min.symm

@[to_additive]
lemma max_mul_mul_right (a b c : α) : max (a * c) (b * c) = max a b * c :=
(monotone_id.mul_const' c).map_max.symm

end right

end has_mul

variable [monoid α]

@[to_additive]
lemma min_le_mul_of_one_le_right [covariant_class α α (*) (≤)] {a b : α} (hb : 1 ≤ b) :
  min a b ≤ a * b :=
min_le_iff.2 $ or.inl $ le_mul_of_one_le_right' hb

@[to_additive]
lemma min_le_mul_of_one_le_left [covariant_class α α (function.swap (*)) (≤)] {a b : α}
  (ha : 1 ≤ a) : min a b ≤ a * b :=
min_le_iff.2 $ or.inr $ le_mul_of_one_le_left' ha

@[to_additive]
lemma max_le_mul_of_one_le [covariant_class α α (*) (≤)]
  [covariant_class α α (function.swap (*)) (≤)] {a b : α} (ha : 1 ≤ a) (hb : 1 ≤ b) :
  max a b ≤ a * b :=
max_le_iff.2 ⟨le_mul_of_one_le_right' hb, le_mul_of_one_le_left' ha⟩

end covariant_class_mul_le

section linear_ordered_cancel_comm_monoid
variables [linear_ordered_cancel_comm_monoid α]

/-- Pullback a `linear_ordered_cancel_comm_monoid` under an injective map.
See note [reducible non-instances]. -/
@[reducible, to_additive function.injective.linear_ordered_cancel_add_comm_monoid
"Pullback a `linear_ordered_cancel_add_comm_monoid` under an injective map."]
def function.injective.linear_ordered_cancel_comm_monoid {β : Type*}
  [has_one β] [has_mul β]
  (f : β → α) (hf : function.injective f) (one : f 1 = 1)
  (mul : ∀ x y, f (x * y) = f x * f y) :
  linear_ordered_cancel_comm_monoid β :=
{ ..hf.linear_ordered_comm_monoid f one mul,
  ..hf.ordered_cancel_comm_monoid f one mul }

end linear_ordered_cancel_comm_monoid

namespace order_dual

@[to_additive] instance [h : has_mul α] : has_mul (order_dual α) := h
@[to_additive] instance [h : has_one α] : has_one (order_dual α) := h
@[to_additive] instance [h : monoid α] : monoid (order_dual α) := h
@[to_additive] instance [h : comm_monoid α] : comm_monoid (order_dual α) := h
@[to_additive] instance [h : cancel_comm_monoid α] : cancel_comm_monoid (order_dual α) := h

@[to_additive]
instance contravariant_class_mul_le [has_le α] [has_mul α] [c : contravariant_class α α (*) (≤)] :
  contravariant_class (order_dual α) (order_dual α) (*) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_le [has_le α] [has_mul α] [c : covariant_class α α (*) (≤)] :
  covariant_class (order_dual α) (order_dual α) (*) (≤) :=
⟨c.1.flip⟩

@[to_additive] instance contravariant_class_swap_mul_le [has_le α] [has_mul α]
  [c : contravariant_class α α (swap (*)) (≤)] :
  contravariant_class (order_dual α) (order_dual α) (swap (*)) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_le [has_le α] [has_mul α]
  [c : covariant_class α α (swap (*)) (≤)] :
  covariant_class (order_dual α) (order_dual α) (swap (*)) (≤) :=
⟨c.1.flip⟩

@[to_additive]
instance contravariant_class_mul_lt [has_lt α] [has_mul α] [c : contravariant_class α α (*) (<)] :
  contravariant_class (order_dual α) (order_dual α) (*) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_mul_lt [has_lt α] [has_mul α] [c : covariant_class α α (*) (<)] :
  covariant_class (order_dual α) (order_dual α) (*) (<) :=
⟨c.1.flip⟩

@[to_additive] instance contravariant_class_swap_mul_lt [has_lt α] [has_mul α]
  [c : contravariant_class α α (swap (*)) (<)] :
  contravariant_class (order_dual α) (order_dual α) (swap (*)) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance covariant_class_swap_mul_lt [has_lt α] [has_mul α]
  [c : covariant_class α α (swap (*)) (<)] :
  covariant_class (order_dual α) (order_dual α) (swap (*)) (<) :=
⟨c.1.flip⟩

@[to_additive]
instance [ordered_comm_monoid α] : ordered_comm_monoid (order_dual α) :=
{ mul_le_mul_left := λ a b h c, mul_le_mul_left' h c,
  .. order_dual.partial_order α,
  .. order_dual.comm_monoid }

@[to_additive ordered_cancel_add_comm_monoid.to_contravariant_class]
instance ordered_cancel_comm_monoid.to_contravariant_class [ordered_cancel_comm_monoid α] :
  contravariant_class (order_dual α) (order_dual α) has_mul.mul has_le.le :=
{ elim := λ a b c bc, (ordered_cancel_comm_monoid.le_of_mul_le_mul_left a c b (dual_le.mp bc)) }

@[to_additive]
instance [ordered_cancel_comm_monoid α] : ordered_cancel_comm_monoid (order_dual α) :=
{ le_of_mul_le_mul_left := λ a b c : α, le_of_mul_le_mul_left',
  .. order_dual.ordered_comm_monoid, .. order_dual.cancel_comm_monoid }

@[to_additive]
instance [linear_ordered_cancel_comm_monoid α] :
  linear_ordered_cancel_comm_monoid (order_dual α) :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_cancel_comm_monoid }

@[to_additive]
instance [linear_ordered_comm_monoid α] :
  linear_ordered_comm_monoid (order_dual α) :=
{ .. order_dual.linear_order α,
  .. order_dual.ordered_comm_monoid }

end order_dual

section linear_ordered_cancel_add_comm_monoid
variables [linear_ordered_cancel_add_comm_monoid α]

lemma lt_or_lt_of_add_lt_add {a b m n : α} (h : m + n < a + b) : m < a ∨ n < b :=
by { contrapose! h, exact add_le_add h.1 h.2 }

end linear_ordered_cancel_add_comm_monoid

section ordered_cancel_add_comm_monoid

variable [ordered_cancel_add_comm_monoid α]

namespace with_top

lemma add_lt_add_iff_left {a b c : with_top α} (ha : a ≠ ⊤) : a + b < a + c ↔ b < c :=
begin
  lift a to α using ha,
  cases b; cases c,
  { simp [none_eq_top] },
  { simp [some_eq_coe, none_eq_top, coe_lt_top] },
  { simp [some_eq_coe, none_eq_top, ← coe_add, coe_lt_top] },
  { simp [some_eq_coe, ← coe_add, coe_lt_coe] }
end

lemma add_lt_add_iff_right {a b c : with_top α} (ha : a ≠ ⊤) : (c + a < b + a ↔ c < b) :=
by simp only [← add_comm a, add_lt_add_iff_left ha]

instance contravariant_class_add_lt : contravariant_class (with_top α) (with_top α) (+) (<) :=
begin
  refine ⟨λ a b c h, _⟩,
  cases a,
  { rw [none_eq_top, top_add, top_add] at h, exact (lt_irrefl ⊤ h).elim },
  { exact (add_lt_add_iff_left coe_ne_top).1 h }
end

end with_top

namespace with_bot

lemma add_lt_add_iff_left {a b c : with_bot α} (ha : a ≠ ⊥) : a + b < a + c ↔ b < c :=
@with_top.add_lt_add_iff_left (order_dual α) _ a c b ha

lemma add_lt_add_iff_right {a b c : with_bot α} (ha : a ≠ ⊥) : b + a < c + a ↔ b < c :=
@with_top.add_lt_add_iff_right (order_dual α) _ _ _ _ ha

instance contravariant_class_add_lt : contravariant_class (with_bot α) (with_bot α) (+) (<) :=
@order_dual.contravariant_class_add_lt (with_top $ order_dual α) _ _ _

end with_bot

end ordered_cancel_add_comm_monoid

namespace prod

variables {M N : Type*}

@[to_additive]
instance [ordered_cancel_comm_monoid M] [ordered_cancel_comm_monoid N] :
  ordered_cancel_comm_monoid (M × N) :=
{ mul_le_mul_left := λ a b h c, ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩,
  le_of_mul_le_mul_left := λ a b c h, ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩,
 .. prod.cancel_comm_monoid, .. prod.partial_order M N }

end prod

section type_tags

instance : Π [preorder α], preorder (multiplicative α) := id
instance : Π [preorder α], preorder (additive α) := id
instance : Π [partial_order α], partial_order (multiplicative α) := id
instance : Π [partial_order α], partial_order (additive α) := id
instance : Π [linear_order α], linear_order (multiplicative α) := id
instance : Π [linear_order α], linear_order (additive α) := id

instance [ordered_add_comm_monoid α] : ordered_comm_monoid (multiplicative α) :=
{ mul_le_mul_left := @ordered_add_comm_monoid.add_le_add_left α _,
  ..multiplicative.partial_order,
  ..multiplicative.comm_monoid }

instance [ordered_comm_monoid α] : ordered_add_comm_monoid (additive α) :=
{ add_le_add_left := @ordered_comm_monoid.mul_le_mul_left α _,
  ..additive.partial_order,
  ..additive.add_comm_monoid }

instance [ordered_cancel_add_comm_monoid α] : ordered_cancel_comm_monoid (multiplicative α) :=
{ le_of_mul_le_mul_left := @ordered_cancel_add_comm_monoid.le_of_add_le_add_left α _,
  ..multiplicative.left_cancel_semigroup,
  ..multiplicative.ordered_comm_monoid }

instance [ordered_cancel_comm_monoid α] : ordered_cancel_add_comm_monoid (additive α) :=
{ le_of_add_le_add_left := @ordered_cancel_comm_monoid.le_of_mul_le_mul_left α _,
  ..additive.add_left_cancel_semigroup,
  ..additive.ordered_add_comm_monoid }

instance [linear_ordered_add_comm_monoid α] : linear_ordered_comm_monoid (multiplicative α) :=
{ ..multiplicative.linear_order,
  ..multiplicative.ordered_comm_monoid }

instance [linear_ordered_comm_monoid α] : linear_ordered_add_comm_monoid (additive α) :=
{ ..additive.linear_order,
  ..additive.ordered_add_comm_monoid }

end type_tags

/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `order_iso.mul_left` when working in an ordered group. -/
@[to_additive "The order embedding sending `b` to `a + b`, for some fixed `a`.
  See also `order_iso.add_left` when working in an additive ordered group.", simps]
def order_embedding.mul_left
  {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (*) (<)] (m : α) : α ↪o α :=
order_embedding.of_strict_mono (λ n, m * n) (λ a b w, mul_lt_mul_left' w m)

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `order_iso.mul_right` when working in an ordered group. -/
@[to_additive "The order embedding sending `b` to `b + a`, for some fixed `a`.
  See also `order_iso.add_right` when working in an additive ordered group.", simps]
def order_embedding.mul_right
  {α : Type*} [has_mul α] [linear_order α] [covariant_class α α (swap (*)) (<)] (m : α) :
  α ↪o α :=
order_embedding.of_strict_mono (λ n, n * m) (λ a b w, mul_lt_mul_right' w m)
