/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import algebra.group.defs
import algebra.group.hom
import algebra.group.type_tags
import algebra.opposites
import logic.embedding

/-!
# Definitions of group actions

This file defines a hierarchy of group action type-classes on top of the previously defined
notation classes `has_scalar` and its additive version `has_vadd`:

* `mul_action M α` and its additive version `add_action G P` are typeclasses used for
  actions of multiplicative and additive monoids and groups; they extend notation classes
  `has_scalar` and `has_vadd` that are defined in `algebra.group.defs`;
* `distrib_mul_action M A` is a typeclass for an action of a multiplicative monoid on
  an additive monoid such that `a • (b + c) = a • b + a • c` and `a • 0 = 0`.

The hierarchy is extended further by `module`, defined elsewhere.

Also provided are typeclasses for faithful and transitive actions, and typeclasses regarding the
interaction of different group actions,

* `smul_comm_class M N α` and its additive version `vadd_comm_class M N α`;
* `is_scalar_tower M N α` (no additive version).
* `is_central_scalar M α` (no additive version).

## Notation

- `a • b` is used as notation for `has_scalar.smul a b`.
- `a +ᵥ b` is used as notation for `has_vadd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `group_theory`, to avoid import cycles.
More sophisticated lemmas belong in `group_theory.group_action`.

## Tags

group action
-/

variables {M N G A B α β γ : Type*}

open function

/-!
### Faithful actions
-/

/-- Typeclass for faithful actions. -/
class has_faithful_vadd (G : Type*) (P : Type*) [has_vadd G P] : Prop :=
(eq_of_vadd_eq_vadd : ∀ {g₁ g₂ : G}, (∀ p : P, g₁ +ᵥ p = g₂ +ᵥ p) → g₁ = g₂)

/-- Typeclass for faithful actions. -/
@[to_additive has_faithful_vadd]
class has_faithful_scalar (M : Type*) (α : Type*) [has_scalar M α] : Prop :=
(eq_of_smul_eq_smul : ∀ {m₁ m₂ : M}, (∀ a : α, m₁ • a = m₂ • a) → m₁ = m₂)

export has_faithful_scalar (eq_of_smul_eq_smul) has_faithful_vadd (eq_of_vadd_eq_vadd)

@[to_additive]
lemma smul_left_injective' [has_scalar M α] [has_faithful_scalar M α] :
  function.injective ((•) : M → α → α) :=
λ m₁ m₂ h, has_faithful_scalar.eq_of_smul_eq_smul (congr_fun h)

/-- See also `monoid.to_mul_action` and `mul_zero_class.to_smul_with_zero`. -/
@[priority 910, to_additive] -- see Note [lower instance priority]
instance has_mul.to_has_scalar (α : Type*) [has_mul α] : has_scalar α α := ⟨(*)⟩

@[simp, to_additive] lemma smul_eq_mul (α : Type*) [has_mul α] {a a' : α} : a • a' = a * a' := rfl

/-- Type class for additive monoid actions. -/
@[ext, protect_proj] class add_action (G : Type*) (P : Type*) [add_monoid G] extends has_vadd G P :=
(zero_vadd : ∀ p : P, (0 : G) +ᵥ p = p)
(add_vadd : ∀ (g₁ g₂ : G) (p : P), (g₁ + g₂) +ᵥ p = g₁ +ᵥ (g₂ +ᵥ p))

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[ext, protect_proj, to_additive]
class mul_action (α : Type*) (β : Type*) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

/-!
### (Pre)transitive action

`M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y` (or `g +ᵥ x = y`
for an additive action). A transitive action should furthermore have `α` nonempty.

In this section we define typeclasses `mul_action.is_pretransitive` and
`add_action.is_pretransitive` and provide `mul_action.exists_smul_eq`/`add_action.exists_vadd_eq`,
`mul_action.surjective_smul`/`add_action.surjective_vadd` as public interface to access this
property. We do not provide typeclasses `*_action.is_transitive`; users should assume
`[mul_action.is_pretransitive M α] [nonempty α]` instead. -/

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g +ᵥ x = y`.
  A transitive action should furthermore have `α` nonempty. -/
class add_action.is_pretransitive (M α : Type*) [has_vadd M α] : Prop :=
(exists_vadd_eq : ∀ x y : α, ∃ g : M, g +ᵥ x = y)

/-- `M` acts pretransitively on `α` if for any `x y` there is `g` such that `g • x = y`.
  A transitive action should furthermore have `α` nonempty. -/
@[to_additive] class mul_action.is_pretransitive (M α : Type*) [has_scalar M α] : Prop :=
(exists_smul_eq : ∀ x y : α, ∃ g : M, g • x = y)

namespace mul_action

variables (M) {α} [has_scalar M α] [is_pretransitive M α]

@[to_additive] lemma exists_smul_eq (x y : α) : ∃ m : M, m • x = y :=
is_pretransitive.exists_smul_eq x y

@[to_additive] lemma surjective_smul (x : α) : surjective (λ c : M, c • x) := exists_smul_eq M x

/-- The regular action of a group on itself is transitive. -/
@[to_additive] instance regular.is_pretransitive [group G] : is_pretransitive G G :=
⟨λ x y, ⟨y * x⁻¹, inv_mul_cancel_right _ _⟩⟩

end mul_action

/-!
### Scalar tower and commuting actions
-/

/-- A typeclass mixin saying that two additive actions on the same space commute. -/
class vadd_comm_class (M N α : Type*) [has_vadd M α] [has_vadd N α] : Prop :=
(vadd_comm : ∀ (m : M) (n : N) (a : α), m +ᵥ (n +ᵥ a) = n +ᵥ (m +ᵥ a))

/-- A typeclass mixin saying that two multiplicative actions on the same space commute. -/
@[to_additive] class smul_comm_class (M N α : Type*) [has_scalar M α] [has_scalar N α] : Prop :=
(smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a)

export mul_action (mul_smul) add_action (add_vadd) smul_comm_class (smul_comm)
  vadd_comm_class (vadd_comm)

/--
Frequently, we find ourselves wanting to express a bilinear map `M →ₗ[R] N →ₗ[R] P` or an
equivalence between maps `(M →ₗ[R] N) ≃ₗ[R] (M' →ₗ[R] N')` where the maps have an associated ring
`R`. Unfortunately, using definitions like these requires that `R` satisfy `comm_semiring R`, and
not just `semiring R`. Using `M →ₗ[R] N →+ P` and `(M →ₗ[R] N) ≃+ (M' →ₗ[R] N')` avoids this
problem, but throws away structure that is useful for when we _do_ have a commutative (semi)ring.

To avoid making this compromise, we instead state these definitions as `M →ₗ[R] N →ₗ[S] P` or
`(M →ₗ[R] N) ≃ₗ[S] (M' →ₗ[R] N')` and require `smul_comm_class S R` on the appropriate modules. When
the caller has `comm_semiring R`, they can set `S = R` and `smul_comm_class_self` will populate the
instance. If the caller only has `semiring R` they can still set either `R = ℕ` or `S = ℕ`, and
`add_comm_monoid.nat_smul_comm_class` or `add_comm_monoid.nat_smul_comm_class'` will populate
the typeclass, which is still sufficient to recover a `≃+` or `→+` structure.

An example of where this is used is `linear_map.prod_equiv`.
-/
library_note "bundled maps over different rings"

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
@[to_additive] lemma smul_comm_class.symm (M N α : Type*) [has_scalar M α] [has_scalar N α]
  [smul_comm_class M N α] : smul_comm_class N M α :=
⟨λ a' a b, (smul_comm a a' b).symm⟩

/-- Commutativity of additive actions is a symmetric relation. This lemma can't be an instance
because this would cause a loop in the instance search graph. -/
add_decl_doc vadd_comm_class.symm

@[to_additive] instance smul_comm_class_self (M α : Type*) [comm_monoid M] [mul_action M α] :
  smul_comm_class M M α :=
⟨λ a a' b, by rw [← mul_smul, mul_comm, mul_smul]⟩

/-- An instance of `is_scalar_tower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
class is_scalar_tower (M N α : Type*) [has_scalar M N] [has_scalar N α] [has_scalar M α] : Prop :=
(smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • (y • z))

@[simp] lemma smul_assoc {M N} [has_scalar M N] [has_scalar N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : N) (z : α) :
  (x • y) • z = x • y • z :=
is_scalar_tower.smul_assoc x y z

instance semigroup.is_scalar_tower [semigroup α] : is_scalar_tower α α α := ⟨mul_assoc⟩

/-- A typeclass indicating that the right (aka `mul_opposite`) and left actions by `M` on `α` are
equal, that is that `M` acts centrally on `α`. This can be thought of as a version of commutativity
for `•`. -/
class is_central_scalar (M α : Type*) [has_scalar M α] [has_scalar Mᵐᵒᵖ α] : Prop :=
(op_smul_eq_smul : ∀ (m : M) (a : α), mul_opposite.op m • a = m • a)

lemma is_central_scalar.unop_smul_eq_smul {M α : Type*} [has_scalar M α] [has_scalar Mᵐᵒᵖ α]
  [is_central_scalar M α] (m : Mᵐᵒᵖ) (a : α) : (mul_opposite.unop m) • a = m • a :=
mul_opposite.rec (by exact λ m, (is_central_scalar.op_smul_eq_smul _ _).symm) m

export is_central_scalar (op_smul_eq_smul unop_smul_eq_smul)

-- these instances are very low priority, as there is usually a faster way to find these instances

@[priority 50]
instance smul_comm_class.op_left [has_scalar M α] [has_scalar Mᵐᵒᵖ α]
  [is_central_scalar M α] [has_scalar N α] [smul_comm_class M N α] : smul_comm_class Mᵐᵒᵖ N α :=
⟨λ m n a, by rw [←unop_smul_eq_smul m (n • a), ←unop_smul_eq_smul m a, smul_comm]⟩

@[priority 50]
instance smul_comm_class.op_right [has_scalar M α] [has_scalar N α] [has_scalar Nᵐᵒᵖ α]
  [is_central_scalar N α] [smul_comm_class M N α] : smul_comm_class M Nᵐᵒᵖ α :=
⟨λ m n a, by rw [←unop_smul_eq_smul n (m • a), ←unop_smul_eq_smul n a, smul_comm]⟩

@[priority 50]
instance is_scalar_tower.op_left
  [has_scalar M α] [has_scalar Mᵐᵒᵖ α] [is_central_scalar M α]
  [has_scalar M N] [has_scalar Mᵐᵒᵖ N] [is_central_scalar M N]
  [has_scalar N α] [is_scalar_tower M N α] : is_scalar_tower Mᵐᵒᵖ N α :=
⟨λ m n a, by rw [←unop_smul_eq_smul m (n • a), ←unop_smul_eq_smul m n, smul_assoc]⟩

@[priority 50]
instance is_scalar_tower.op_right [has_scalar M α] [has_scalar M N]
  [has_scalar N α] [has_scalar Nᵐᵒᵖ α] [is_central_scalar N α]
  [is_scalar_tower M N α] : is_scalar_tower M Nᵐᵒᵖ α :=
⟨λ m n a, by rw [←unop_smul_eq_smul n a, ←unop_smul_eq_smul (m • n) a, mul_opposite.unop_smul,
                 smul_assoc]⟩

namespace has_scalar
variables [has_scalar M α]

/-- Auxiliary definition for `has_scalar.comp`, `mul_action.comp_hom`,
`distrib_mul_action.comp_hom`, `module.comp_hom`, etc. -/
@[simp, to_additive  /-" Auxiliary definition for `has_vadd.comp`, `add_action.comp_hom`, etc. "-/]
def comp.smul (g : N → M) (n : N) (a : α) : α :=
g n • a

variables (α)

/-- An action of `M` on `α` and a function `N → M` induces an action of `N` on `α`.

See note [reducible non-instances]. Since this is reducible, we make sure to go via
`has_scalar.comp.smul` to prevent typeclass inference unfolding too far. -/
@[reducible, to_additive /-" An additive action of `M` on `α` and a function `N → M` induces
  an additive action of `N` on `α` "-/]
def comp (g : N → M) : has_scalar N α :=
{ smul := has_scalar.comp.smul g }

variables {α}

/-- Given a tower of scalar actions `M → α → β`, if we use `has_scalar.comp`
to pull back both of `M`'s actions by a map `g : N → M`, then we obtain a new
tower of scalar actions `N → α → β`.

This cannot be an instance because it can cause infinite loops whenever the `has_scalar` arguments
are still metavariables.
-/
@[priority 100]
lemma comp.is_scalar_tower [has_scalar M β] [has_scalar α β] [is_scalar_tower M α β]
  (g : N → M) :
  (by haveI := comp α g; haveI := comp β g; exact is_scalar_tower N α β) :=
by exact {smul_assoc := λ n, @smul_assoc _ _ _ _ _ _ _ (g n) }

/--
This cannot be an instance because it can cause infinite loops whenever the `has_scalar` arguments
are still metavariables.
-/
@[priority 100]
lemma comp.smul_comm_class [has_scalar β α] [smul_comm_class M β α] (g : N → M) :
  (by haveI := comp α g; exact smul_comm_class N β α) :=
by exact {smul_comm := λ n, @smul_comm _ _ _ _ _ _ (g n) }

/--
This cannot be an instance because it can cause infinite loops whenever the `has_scalar` arguments
are still metavariables.
-/
@[priority 100]
lemma comp.smul_comm_class' [has_scalar β α] [smul_comm_class β M α] (g : N → M) :
  (by haveI := comp α g; exact smul_comm_class β N α) :=
by exact {smul_comm := λ _ n, @smul_comm _ _ _ _ _ _ _ (g n) }

end has_scalar

section ite
variables [has_scalar M α] (p : Prop) [decidable p]

@[to_additive] lemma ite_smul (a₁ a₂ : M) (b : α) : (ite p a₁ a₂) • b = ite p (a₁ • b) (a₂ • b) :=
by split_ifs; refl

@[to_additive] lemma smul_ite (a : M) (b₁ b₂ : α) : a • (ite p b₁ b₂) = ite p (a • b₁) (a • b₂) :=
by split_ifs; refl

end ite

section
variables [monoid M] [mul_action M α]

@[to_additive] lemma smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b :=
(mul_smul _ _ _).symm

variable (M)
@[simp, to_additive] theorem one_smul (b : α) : (1 : M) • b = b := mul_action.one_smul _

/-- `has_scalar` version of `one_mul_eq_id` -/
@[to_additive]
lemma one_smul_eq_id : ((•) (1 : M) : α → α) = id := funext $ one_smul _

/-- `has_scalar` version of `comp_mul_left` -/
@[to_additive]
lemma comp_smul_left (a₁ a₂ : M) : (•) a₁ ∘ (•) a₂ = ((•) (a₁ * a₂) : α → α) :=
funext $ λ _, (mul_smul _ _ _).symm

variables {M}

/-- Pullback a multiplicative action along an injective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pullback an additive action along an injective map respecting `+ᵥ`."]
protected def function.injective.mul_action [has_scalar M β] (f : β → α)
  (hf : injective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  mul_action M β :=
{ smul := (•),
  one_smul := λ x, hf $ (smul _ _).trans $ one_smul _ (f x),
  mul_smul := λ c₁ c₂ x, hf $ by simp only [smul, mul_smul] }

/-- Pushforward a multiplicative action along a surjective map respecting `•`.
See note [reducible non-instances]. -/
@[reducible, to_additive "Pushforward an additive action along a surjective map respecting `+ᵥ`."]
protected def function.surjective.mul_action [has_scalar M β] (f : α → β) (hf : surjective f)
  (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  mul_action M β :=
{ smul := (•),
  one_smul := λ y, by { rcases hf y with ⟨x, rfl⟩, rw [← smul, one_smul] },
  mul_smul := λ c₁ c₂ y, by { rcases hf y with ⟨x, rfl⟩, simp only [← smul, mul_smul] } }

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `function.surjective.distrib_mul_action_left` and `function.surjective.module_left`.
-/
@[reducible, to_additive "Push forward the action of `R` on `M` along a compatible
surjective map `f : R →+ S`."]
def function.surjective.mul_action_left {R S M : Type*} [monoid R] [mul_action R M]
  [monoid S] [has_scalar S M]
  (f : R →* S) (hf : function.surjective f) (hsmul : ∀ c (x : M), f c • x = c • x) :
  mul_action S M :=
{ smul := (•),
  one_smul := λ b, by rw [← f.map_one, hsmul, one_smul],
  mul_smul := hf.forall₂.mpr $ λ a b x, by simp only [← f.map_mul, hsmul, mul_smul] }

section

variables (M)

/-- The regular action of a monoid on itself by left multiplication.

This is promoted to a module by `semiring.to_module`. -/
@[priority 910, to_additive] -- see Note [lower instance priority]
instance monoid.to_mul_action : mul_action M M :=
{ smul := (*),
  one_smul := one_mul,
  mul_smul := mul_assoc }

/-- The regular action of a monoid on itself by left addition.

This is promoted to an `add_torsor` by `add_group_is_add_torsor`. -/
add_decl_doc add_monoid.to_add_action

instance is_scalar_tower.left : is_scalar_tower M M α :=
⟨λ x y z, mul_smul x y z⟩

variables {M}

/-- Note that the `smul_comm_class α β β` typeclass argument is usually satisfied by `algebra α β`.
-/
@[to_additive]
lemma mul_smul_comm [has_mul β] [has_scalar α β] [smul_comm_class α β β] (s : α) (x y : β) :
  x * (s • y) = s • (x * y) :=
(smul_comm s x y).symm

/-- Note that the `is_scalar_tower α β β` typeclass argument is usually satisfied by `algebra α β`.
-/
lemma smul_mul_assoc [has_mul β] [has_scalar α β] [is_scalar_tower α β β] (r : α) (x y : β)  :
  (r • x) * y = r • (x * y) :=
smul_assoc r x y

/-- Note that the `is_scalar_tower M α α` and `smul_comm_class M α α` typeclass arguments are
usually satisfied by `algebra M α`. -/
lemma smul_mul_smul [has_mul α] (r s : M) (x y : α)
  [is_scalar_tower M α α] [smul_comm_class M α α] :
  (r • x) * (s • y) = (r * s) • (x * y) :=
by rw [smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]

end

namespace mul_action

variables (M α)

/-- Embedding of `α` into functions `M → α` induced by a multiplicative action of `M` on `α`. -/
@[to_additive] def to_fun : α ↪ (M → α) :=
⟨λ y x, x • y, λ y₁ y₂ H, one_smul M y₁ ▸ one_smul M y₂ ▸ by convert congr_fun H 1⟩

/-- Embedding of `α` into functions `M → α` induced by an additive action of `M` on `α`. -/
add_decl_doc add_action.to_fun

variables {M α}

@[simp, to_additive] lemma to_fun_apply (x : M) (y : α) : mul_action.to_fun M α y x = x • y :=
rfl

variable (α)

/-- A multiplicative action of `M` on `α` and a monoid homomorphism `N → M` induce
a multiplicative action of `N` on `α`.

See note [reducible non-instances]. -/
@[reducible, to_additive] def comp_hom [monoid N] (g : N →* M) :
  mul_action N α :=
{ smul := has_scalar.comp.smul g,
  one_smul := by simp [g.map_one, mul_action.one_smul],
  mul_smul := by simp [g.map_mul, mul_action.mul_smul] }

/-- An additive action of `M` on `α` and an additive monoid homomorphism `N → M` induce
an additive action of `N` on `α`.

See note [reducible non-instances]. -/
add_decl_doc add_action.comp_hom

end mul_action

end

section compatible_scalar

@[simp] lemma smul_one_smul {M} (N) [monoid N] [has_scalar M N] [mul_action N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : α) :
  (x • (1 : N)) • y = x • y :=
by rw [smul_assoc, one_smul]

@[simp] lemma smul_one_mul {M N} [monoid N] [has_scalar M N] [is_scalar_tower M N N] (x : M)
  (y : N) : (x • 1) * y = x • y :=
smul_one_smul N x y

@[simp, to_additive] lemma mul_smul_one {M N} [monoid N] [has_scalar M N] [smul_comm_class M N N]
  (x : M) (y : N) :
  y * (x • 1) = x • y :=
by rw [← smul_eq_mul, ← smul_comm, smul_eq_mul, mul_one]

lemma is_scalar_tower.of_smul_one_mul {M N} [monoid N] [has_scalar M N]
  (h : ∀ (x : M) (y : N), (x • (1 : N)) * y = x • y) :
  is_scalar_tower M N N :=
⟨λ x y z, by rw [← h, smul_eq_mul, mul_assoc, h, smul_eq_mul]⟩

@[to_additive] lemma smul_comm_class.of_mul_smul_one {M N} [monoid N] [has_scalar M N]
  (H : ∀ (x : M) (y : N), y * (x • (1 : N)) = x • y) : smul_comm_class M N N :=
⟨λ x y z, by rw [← H x z, smul_eq_mul, ← H, smul_eq_mul, mul_assoc]⟩

end compatible_scalar

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
@[ext] class distrib_mul_action (M : Type*) (A : Type*) [monoid M] [add_monoid A]
  extends mul_action M A :=
(smul_add : ∀(r : M) (x y : A), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : M), r • (0 : A) = 0)

section
variables [monoid M] [add_monoid A] [distrib_mul_action M A]

theorem smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : M) : a • (0 : A) = 0 :=
distrib_mul_action.smul_zero _

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.distrib_mul_action [add_monoid B] [has_scalar M B] (f : B →+ A)
  (hf : injective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  distrib_mul_action M B :=
{ smul := (•),
  smul_add := λ c x y, hf $ by simp only [smul, f.map_add, smul_add],
  smul_zero := λ c, hf $ by simp only [smul, f.map_zero, smul_zero],
  .. hf.mul_action f smul }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.distrib_mul_action [add_monoid B] [has_scalar M B] (f : A →+ B)
  (hf : surjective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  distrib_mul_action M B :=
{ smul := (•),
  smul_add := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [smul_add, ← smul, ← f.map_add] },
  smul_zero := λ c, by simp only [← f.map_zero, ← smul, smul_zero],
  .. hf.mul_action f smul }

/-- Push forward the action of `R` on `M` along a compatible surjective map `f : R →* S`.

See also `function.surjective.mul_action_left` and `function.surjective.module_left`.
-/
@[reducible]
def function.surjective.distrib_mul_action_left {R S M : Type*} [monoid R] [add_monoid M]
  [distrib_mul_action R M] [monoid S] [has_scalar S M]
  (f : R →* S) (hf : function.surjective f) (hsmul : ∀ c (x : M), f c • x = c • x) :
  distrib_mul_action S M :=
{ smul := (•),
  smul_zero := hf.forall.mpr $ λ c, by rw [hsmul, smul_zero],
  smul_add := hf.forall.mpr $ λ c x y, by simp only [hsmul, smul_add],
  .. hf.mul_action_left f hsmul }

variable (A)

/-- Compose a `distrib_mul_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible] def distrib_mul_action.comp_hom [monoid N] (f : N →* M) :
  distrib_mul_action N A :=
{ smul := has_scalar.comp.smul f,
  smul_zero := λ x, smul_zero (f x),
  smul_add := λ x, smul_add (f x),
  .. mul_action.comp_hom A f }

/-- Each element of the monoid defines a additive monoid homomorphism. -/
@[simps]
def distrib_mul_action.to_add_monoid_hom (x : M) : A →+ A :=
{ to_fun := (•) x,
  map_zero' := smul_zero x,
  map_add' := smul_add x }

variables (M)

/-- Each element of the monoid defines an additive monoid homomorphism. -/
@[simps]
def distrib_mul_action.to_add_monoid_End : M →* add_monoid.End A :=
{ to_fun := distrib_mul_action.to_add_monoid_hom A,
  map_one' := add_monoid_hom.ext $ one_smul M,
  map_mul' := λ x y, add_monoid_hom.ext $ mul_smul x y }

end

section
variables [monoid M] [add_group A] [distrib_mul_action M A]

@[simp] theorem smul_neg (r : M) (x : A) : r • (-x) = -(r • x) :=
eq_neg_of_add_eq_zero $ by rw [← smul_add, neg_add_self, smul_zero]

theorem smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end

/-- Typeclass for multiplicative actions on multiplicative structures. This generalizes
conjugation actions. -/
@[ext] class mul_distrib_mul_action (M : Type*) (A : Type*) [monoid M] [monoid A]
  extends mul_action M A :=
(smul_mul : ∀ (r : M) (x y : A), r • (x * y) = (r • x) * (r • y))
(smul_one : ∀ (r : M), r • (1 : A) = 1)

export mul_distrib_mul_action (smul_one)

section
variables [monoid M] [monoid A] [mul_distrib_mul_action M A]

theorem smul_mul' (a : M) (b₁ b₂ : A) : a • (b₁ * b₂) = (a • b₁) * (a • b₂) :=
mul_distrib_mul_action.smul_mul _ _ _

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.injective.mul_distrib_mul_action [monoid B] [has_scalar M B] (f : B →* A)
  (hf : injective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  mul_distrib_mul_action M B :=
{ smul := (•),
  smul_mul := λ c x y, hf $ by simp only [smul, f.map_mul, smul_mul'],
  smul_one := λ c, hf $ by simp only [smul, f.map_one, smul_one],
  .. hf.mul_action f smul }

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
@[reducible]
protected def function.surjective.mul_distrib_mul_action [monoid B] [has_scalar M B] (f : A →* B)
  (hf : surjective f) (smul : ∀ (c : M) x, f (c • x) = c • f x) :
  mul_distrib_mul_action M B :=
{ smul := (•),
  smul_mul := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [smul_mul', ← smul, ← f.map_mul] },
  smul_one := λ c, by simp only [← f.map_one, ← smul, smul_one],
  .. hf.mul_action f smul }

variable (A)

/-- Compose a `mul_distrib_mul_action` with a `monoid_hom`, with action `f r' • m`.
See note [reducible non-instances]. -/
@[reducible] def mul_distrib_mul_action.comp_hom [monoid N] (f : N →* M) :
  mul_distrib_mul_action N A :=
{ smul := has_scalar.comp.smul f,
  smul_one := λ x, smul_one (f x),
  smul_mul := λ x, smul_mul' (f x),
  .. mul_action.comp_hom A f }

/-- Scalar multiplication by `r` as a `monoid_hom`. -/
def mul_distrib_mul_action.to_monoid_hom (r : M) : A →* A :=
{ to_fun := (•) r,
  map_one' := smul_one r,
  map_mul' := smul_mul' r }

variable {A}

@[simp] lemma mul_distrib_mul_action.to_monoid_hom_apply (r : M) (x : A) :
  mul_distrib_mul_action.to_monoid_hom A r x = r • x := rfl

variables (M A)

/-- Each element of the monoid defines a monoid homomorphism. -/
@[simps]
def mul_distrib_mul_action.to_monoid_End : M →* monoid.End A :=
{ to_fun := mul_distrib_mul_action.to_monoid_hom A,
  map_one' := monoid_hom.ext $ one_smul M,
  map_mul' := λ x y, monoid_hom.ext $ mul_smul x y }

end

section
variables [monoid M] [group A] [mul_distrib_mul_action M A]

@[simp] theorem smul_inv' (r : M) (x : A) : r • (x⁻¹) = (r • x)⁻¹ :=
(mul_distrib_mul_action.to_monoid_hom A r).map_inv x

theorem smul_div' (r : M) (x y : A) : r • (x / y) = (r • x) / (r • y) :=
(mul_distrib_mul_action.to_monoid_hom A r).map_div x y

end

variable (α)

/-- The monoid of endomorphisms.

Note that this is generalized by `category_theory.End` to categories other than `Type u`. -/
protected def function.End := α → α

instance : monoid (function.End α) :=
{ one := id,
  mul := (∘),
  mul_assoc := λ f g h, rfl,
  mul_one := λ f, rfl,
  one_mul := λ f, rfl, }

instance : inhabited (function.End α) := ⟨1⟩

variable {α}

/-- The tautological action by `function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `equiv.perm.apply_mul_action`
* `add_monoid.End.apply_distrib_mul_action`
* `add_aut.apply_distrib_mul_action`
* `mul_aut.apply_mul_distrib_mul_action`
* `ring_hom.apply_distrib_mul_action`
* `linear_equiv.apply_distrib_mul_action`
* `linear_map.apply_module`
* `ring_hom.apply_mul_semiring_action`
* `alg_equiv.apply_mul_semiring_action`
-/
instance function.End.apply_mul_action : mul_action (function.End α) α :=
{ smul := ($),
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] lemma function.End.smul_def (f : function.End α) (a : α) : f • a = f a := rfl

/-- `function.End.apply_mul_action` is faithful. -/
instance function.End.apply_has_faithful_scalar : has_faithful_scalar (function.End α) α :=
⟨λ x y, funext⟩

/-- The tautological action by `add_monoid.End α` on `α`.

This generalizes `function.End.apply_mul_action`. -/
instance add_monoid.End.apply_distrib_mul_action [add_monoid α] :
  distrib_mul_action (add_monoid.End α) α :=
{ smul := ($),
  smul_zero := add_monoid_hom.map_zero,
  smul_add := add_monoid_hom.map_add,
  one_smul := λ _, rfl,
  mul_smul := λ _ _ _, rfl }

@[simp] lemma add_monoid.End.smul_def [add_monoid α] (f : add_monoid.End α) (a : α) :
  f • a = f a := rfl

/-- `add_monoid.End.apply_distrib_mul_action` is faithful. -/
instance add_monoid.End.apply_has_faithful_scalar [add_monoid α] :
  has_faithful_scalar (add_monoid.End α) α :=
⟨add_monoid_hom.ext⟩

/-- The monoid hom representing a monoid action.

When `M` is a group, see `mul_action.to_perm_hom`. -/
def mul_action.to_End_hom [monoid M] [mul_action M α] : M →* function.End α :=
{ to_fun := (•),
  map_one' := funext (one_smul M),
  map_mul' := λ x y, funext (mul_smul x y) }

/-- The monoid action induced by a monoid hom to `function.End α`

See note [reducible non-instances]. -/
@[reducible]
def mul_action.of_End_hom [monoid M] (f : M →* function.End α) : mul_action M α :=
mul_action.comp_hom α f

/-- The tautological additive action by `additive (function.End α)` on `α`. -/
instance add_action.function_End : add_action (additive (function.End α)) α :=
{ vadd := ($),
  zero_vadd := λ _, rfl,
  add_vadd := λ _ _ _, rfl }

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `add_action.to_perm_hom`. -/
def add_action.to_End_hom [add_monoid M] [add_action M α] : M →+ additive (function.End α) :=
{ to_fun := (+ᵥ),
  map_zero' := funext (zero_vadd M),
  map_add' := λ x y, funext (add_vadd x y) }

/-- The additive action induced by a hom to `additive (function.End α)`

See note [reducible non-instances]. -/
@[reducible]
def add_action.of_End_hom [add_monoid M] (f : M →+ additive (function.End α)) : add_action M α :=
add_action.comp_hom α f
