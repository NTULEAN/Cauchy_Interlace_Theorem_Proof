/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import measure_theory.measure.mutually_singular
import measure_theory.constructions.borel_space
import algebra.indicator_function
import algebra.support
import dynamics.ergodic.measure_preserving

/-!
# Lebesgue integral for `ℝ≥0∞`-valued functions

We define simple functions and show that each Borel measurable function on `ℝ≥0∞` can be
approximated by a sequence of simple functions.

To prove something for an arbitrary measurable function into `ℝ≥0∞`, the theorem
`measurable.ennreal_induction` shows that is it sufficient to show that the property holds for
(multiples of) characteristic functions and is closed under addition and supremum of increasing
sequences of functions.

## Notation

We introduce the following notation for the lower Lebesgue integral of a function `f : α → ℝ≥0∞`.

* `∫⁻ x, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` with respect to a measure `μ`;
* `∫⁻ x, f x`: integral of a function `f : α → ℝ≥0∞` with respect to the canonical measure
  `volume` on `α`;
* `∫⁻ x in s, f x ∂μ`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to a measure `μ`, defined as `∫⁻ x, f x ∂(μ.restrict s)`;
* `∫⁻ x in s, f x`: integral of a function `f : α → ℝ≥0∞` over a set `s` with respect
  to the canonical measure `volume`, defined as `∫⁻ x, f x ∂(volume.restrict s)`.

-/

noncomputable theory
open set (hiding restrict restrict_apply) filter ennreal function (support)
open_locale classical topological_space big_operators nnreal ennreal measure_theory

namespace measure_theory

variables {α β γ δ : Type*}

/-- A function `f` from a measurable space to any type is called *simple*,
if every preimage `f ⁻¹' {x}` is measurable, and the range is finite. This structure bundles
a function with these properties. -/
structure {u v} simple_func (α : Type u) [measurable_space α] (β : Type v) :=
(to_fun : α → β)
(measurable_set_fiber' : ∀ x, measurable_set (to_fun ⁻¹' {x}))
(finite_range' : (set.range to_fun).finite)

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section measurable
variables [measurable_space α]
instance has_coe_to_fun : has_coe_to_fun (α →ₛ β) (λ _, α → β) := ⟨to_fun⟩

lemma coe_injective ⦃f g : α →ₛ β⦄ (H : (f : α → β) = g) : f = g :=
by cases f; cases g; congr; exact H

@[ext] theorem ext {f g : α →ₛ β} (H : ∀ a, f a = g a) : f = g :=
coe_injective $ funext H

lemma finite_range (f : α →ₛ β) : (set.range f).finite := f.finite_range'

lemma measurable_set_fiber (f : α →ₛ β) (x : β) : measurable_set (f ⁻¹' {x}) :=
f.measurable_set_fiber' x

/-- Range of a simple function `α →ₛ β` as a `finset β`. -/
protected def range (f : α →ₛ β) : finset β := f.finite_range.to_finset

@[simp] theorem mem_range {f : α →ₛ β} {b} : b ∈ f.range ↔ b ∈ range f :=
finite.mem_to_finset _

theorem mem_range_self (f : α →ₛ β) (x : α) : f x ∈ f.range := mem_range.2 ⟨x, rfl⟩

@[simp] lemma coe_range (f : α →ₛ β) : (↑f.range : set β) = set.range f :=
f.finite_range.coe_to_finset

theorem mem_range_of_measure_ne_zero {f : α →ₛ β} {x : β} {μ : measure α} (H : μ (f ⁻¹' {x}) ≠ 0) :
  x ∈ f.range :=
let ⟨a, ha⟩ := nonempty_of_measure_ne_zero H in
mem_range.2 ⟨a, ha⟩

lemma forall_range_iff {f : α →ₛ β} {p : β → Prop} :
  (∀ y ∈ f.range, p y) ↔ ∀ x, p (f x) :=
by simp only [mem_range, set.forall_range_iff]

lemma exists_range_iff {f : α →ₛ β} {p : β → Prop} :
  (∃ y ∈ f.range, p y) ↔ ∃ x, p (f x) :=
by simpa only [mem_range, exists_prop] using set.exists_range_iff

lemma preimage_eq_empty_iff (f : α →ₛ β) (b : β) : f ⁻¹' {b} = ∅ ↔ b ∉ f.range :=
preimage_singleton_eq_empty.trans $ not_congr mem_range.symm

lemma exists_forall_le [nonempty β] [preorder β] [is_directed β (≤)] (f : α →ₛ β) :
  ∃ C, ∀ x, f x ≤ C :=
f.range.exists_le.imp $ λ C, forall_range_iff.1

/-- Constant function as a `simple_func`. -/
def const (α) {β} [measurable_space α] (b : β) : α →ₛ β :=
⟨λ a, b, λ x, measurable_set.const _, finite_range_const⟩

instance [inhabited β] : inhabited (α →ₛ β) := ⟨const _ default⟩

theorem const_apply (a : α) (b : β) : (const α b) a = b := rfl

@[simp] theorem coe_const (b : β) : ⇑(const α b) = function.const α b := rfl

@[simp] lemma range_const (α) [measurable_space α] [nonempty α] (b : β) :
  (const α b).range = {b} :=
finset.coe_injective $ by simp

lemma range_const_subset (α) [measurable_space α] (b : β) :
  (const α b).range ⊆ {b} :=
finset.coe_subset.1 $ by simp

lemma measurable_set_cut (r : α → β → Prop) (f : α →ₛ β)
  (h : ∀b, measurable_set {a | r a b}) : measurable_set {a | r a (f a)} :=
begin
  have : {a | r a (f a)} = ⋃ b ∈ range f, {a | r a b} ∩ f ⁻¹' {b},
  { ext a,
    suffices : r a (f a) ↔ ∃ i, r a (f i) ∧ f a = f i, by simpa,
    exact ⟨λ h, ⟨a, ⟨h, rfl⟩⟩, λ ⟨a', ⟨h', e⟩⟩, e.symm ▸ h'⟩ },
  rw this,
  exact measurable_set.bUnion f.finite_range.countable
    (λ b _, measurable_set.inter (h b) (f.measurable_set_fiber _))
end

@[measurability]
theorem measurable_set_preimage (f : α →ₛ β) (s) : measurable_set (f ⁻¹' s) :=
measurable_set_cut (λ _ b, b ∈ s) f (λ b, measurable_set.const (b ∈ s))

/-- A simple function is measurable -/
@[measurability]
protected theorem measurable [measurable_space β] (f : α →ₛ β) : measurable f :=
λ s _, measurable_set_preimage f s

@[measurability]
protected theorem ae_measurable [measurable_space β] {μ : measure α} (f : α →ₛ β) :
  ae_measurable f μ :=
f.measurable.ae_measurable

protected lemma sum_measure_preimage_singleton (f : α →ₛ β) {μ : measure α} (s : finset β) :
  ∑ y in s, μ (f ⁻¹' {y}) = μ (f ⁻¹' ↑s) :=
sum_measure_preimage_singleton _ (λ _ _, f.measurable_set_fiber _)

lemma sum_range_measure_preimage_singleton (f : α →ₛ β) (μ : measure α) :
  ∑ y in f.range, μ (f ⁻¹' {y}) = μ univ :=
by rw [f.sum_measure_preimage_singleton, coe_range, preimage_range]

/-- If-then-else as a `simple_func`. -/
def piecewise (s : set α) (hs : measurable_set s) (f g : α →ₛ β) : α →ₛ β :=
⟨s.piecewise f g,
 λ x, by letI : measurable_space β := ⊤; exact
   f.measurable.piecewise hs g.measurable trivial,
 (f.finite_range.union g.finite_range).subset range_ite_subset⟩

@[simp] theorem coe_piecewise {s : set α} (hs : measurable_set s) (f g : α →ₛ β) :
  ⇑(piecewise s hs f g) = s.piecewise f g :=
rfl

theorem piecewise_apply {s : set α} (hs : measurable_set s) (f g : α →ₛ β) (a) :
  piecewise s hs f g a = if a ∈ s then f a else g a :=
rfl

@[simp] lemma piecewise_compl {s : set α} (hs : measurable_set sᶜ) (f g : α →ₛ β) :
  piecewise sᶜ hs f g = piecewise s hs.of_compl g f :=
coe_injective $ by simp [hs]

@[simp] lemma piecewise_univ (f g : α →ₛ β) : piecewise univ measurable_set.univ f g = f :=
coe_injective $ by simp

@[simp] lemma piecewise_empty (f g : α →ₛ β) : piecewise ∅ measurable_set.empty f g = g :=
coe_injective $ by simp

lemma support_indicator [has_zero β] {s : set α} (hs : measurable_set s) (f : α →ₛ β) :
  function.support (f.piecewise s hs (simple_func.const α 0)) = s ∩ function.support f :=
set.support_indicator

lemma range_indicator {s : set α} (hs : measurable_set s)
  (hs_nonempty : s.nonempty) (hs_ne_univ : s ≠ univ) (x y : β) :
  (piecewise s hs (const α x) (const α y)).range = {x, y} :=
begin
  ext1 z,
  rw [mem_range, set.mem_range, finset.mem_insert, finset.mem_singleton],
  simp_rw piecewise_apply,
  split; intro h,
  { obtain ⟨a, haz⟩ := h,
    by_cases has : a ∈ s,
    { left,
      simp only [has, function.const_apply, if_true, coe_const] at haz,
      exact haz.symm, },
    { right,
      simp only [has, function.const_apply, if_false, coe_const] at haz,
      exact haz.symm, }, },
  { cases h,
    { obtain ⟨a, has⟩ : ∃ a, a ∈ s, from hs_nonempty,
      exact ⟨a, by simpa [has] using h.symm⟩, },
    { obtain ⟨a, has⟩ : ∃ a, a ∉ s,
      { by_contra' h,
        refine hs_ne_univ _,
        ext1 a,
        simp [h a], },
      exact ⟨a, by simpa [has] using h.symm⟩, }, },
end

lemma measurable_bind [measurable_space γ] (f : α →ₛ β) (g : β → α → γ)
  (hg : ∀ b, measurable (g b)) : measurable (λ a, g (f a) a) :=
λ s hs, f.measurable_set_cut (λ a b, g b a ∈ s) $ λ b, hg b hs

/-- If `f : α →ₛ β` is a simple function and `g : β → α →ₛ γ` is a family of simple functions,
then `f.bind g` binds the first argument of `g` to `f`. In other words, `f.bind g a = g (f a) a`. -/
def bind (f : α →ₛ β) (g : β → α →ₛ γ) : α →ₛ γ :=
⟨λa, g (f a) a,
 λ c, f.measurable_set_cut (λ a b, g b a = c) $ λ b, (g b).measurable_set_preimage {c},
 (f.finite_range.bUnion (λ b _, (g b).finite_range)).subset $
 by rintro _ ⟨a, rfl⟩; simp; exact ⟨a, a, rfl⟩⟩

@[simp] theorem bind_apply (f : α →ₛ β) (g : β → α →ₛ γ) (a) :
  f.bind g a = g (f a) a := rfl

/-- Given a function `g : β → γ` and a simple function `f : α →ₛ β`, `f.map g` return the simple
    function `g ∘ f : α →ₛ γ` -/
def map (g : β → γ) (f : α →ₛ β) : α →ₛ γ := bind f (const α ∘ g)

theorem map_apply (g : β → γ) (f : α →ₛ β) (a) : f.map g a = g (f a) := rfl

theorem map_map (g : β → γ) (h: γ → δ) (f : α →ₛ β) : (f.map g).map h = f.map (h ∘ g) := rfl

@[simp] theorem coe_map (g : β → γ) (f : α →ₛ β) : (f.map g : α → γ) = g ∘ f := rfl

@[simp] theorem range_map [decidable_eq γ] (g : β → γ) (f : α →ₛ β) :
  (f.map g).range = f.range.image g :=
finset.coe_injective $ by simp only [coe_range, coe_map, finset.coe_image, range_comp]

@[simp] theorem map_const (g : β → γ) (b : β) : (const α b).map g = const α (g b) := rfl

lemma map_preimage (f : α →ₛ β) (g : β → γ) (s : set γ) :
  (f.map g) ⁻¹' s = f ⁻¹' ↑(f.range.filter (λb, g b ∈ s)) :=
by { simp only [coe_range, sep_mem_eq, set.mem_range, function.comp_app, coe_map, finset.coe_filter,
  ← mem_preimage, inter_comm, preimage_inter_range], apply preimage_comp }

lemma map_preimage_singleton (f : α →ₛ β) (g : β → γ) (c : γ) :
  (f.map g) ⁻¹' {c} = f ⁻¹' ↑(f.range.filter (λ b, g b = c)) :=
map_preimage _ _ _

/-- Composition of a `simple_fun` and a measurable function is a `simple_func`. -/
def comp [measurable_space β] (f : β →ₛ γ) (g : α → β) (hgm : measurable g) : α →ₛ γ :=
{ to_fun := f ∘ g,
  finite_range' := f.finite_range.subset $ set.range_comp_subset_range _ _,
  measurable_set_fiber' := λ z, hgm (f.measurable_set_fiber z) }

@[simp] lemma coe_comp [measurable_space β] (f : β →ₛ γ) {g : α → β} (hgm : measurable g) :
  ⇑(f.comp g hgm) = f ∘ g :=
rfl

lemma range_comp_subset_range [measurable_space β] (f : β →ₛ γ) {g : α → β} (hgm : measurable g) :
  (f.comp g hgm).range ⊆ f.range :=
finset.coe_subset.1 $ by simp only [coe_range, coe_comp, set.range_comp_subset_range]

/-- Extend a `simple_func` along a measurable embedding: `f₁.extend g hg f₂` is the function
`F : β →ₛ γ` such that `F ∘ g = f₁` and `F y = f₂ y` whenever `y ∉ range g`. -/
def extend [measurable_space β] (f₁ : α →ₛ γ) (g : α → β)
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) : β →ₛ γ :=
{ to_fun := function.extend g f₁ f₂,
  finite_range' := (f₁.finite_range.union $ f₂.finite_range.subset
    (image_subset_range _ _)).subset (range_extend_subset _ _ _),
  measurable_set_fiber' :=
    begin
      letI : measurable_space γ := ⊤, haveI : measurable_singleton_class γ := ⟨λ _, trivial⟩,
      exact λ x, hg.measurable_extend f₁.measurable f₂.measurable (measurable_set_singleton _)
    end }

@[simp] lemma extend_apply [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) (x : α) : (f₁.extend g hg f₂) (g x) = f₁ x :=
function.extend_apply hg.injective _ _ _

@[simp] lemma extend_comp_eq' [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) : (f₁.extend g hg f₂) ∘ g = f₁ :=
funext $ λ x, extend_apply _ _ _ _

@[simp] lemma extend_comp_eq [measurable_space β] (f₁ : α →ₛ γ) {g : α → β}
  (hg : measurable_embedding g) (f₂ : β →ₛ γ) : (f₁.extend g hg f₂).comp g hg.measurable = f₁ :=
coe_injective $ extend_comp_eq' _ _ _

/-- If `f` is a simple function taking values in `β → γ` and `g` is another simple function
with the same domain and codomain `β`, then `f.seq g = f a (g a)`. -/
def seq (f : α →ₛ (β → γ)) (g : α →ₛ β) : α →ₛ γ := f.bind (λf, g.map f)

@[simp] lemma seq_apply (f : α →ₛ (β → γ)) (g : α →ₛ β) (a : α) : f.seq g a = f a (g a) := rfl

/-- Combine two simple functions `f : α →ₛ β` and `g : α →ₛ β`
into `λ a, (f a, g a)`. -/
def pair (f : α →ₛ β) (g : α →ₛ γ) : α →ₛ (β × γ) := (f.map prod.mk).seq g

@[simp] lemma pair_apply (f : α →ₛ β) (g : α →ₛ γ) (a) : pair f g a = (f a, g a) := rfl

lemma pair_preimage (f : α →ₛ β) (g : α →ₛ γ) (s : set β) (t : set γ) :
  (pair f g) ⁻¹' (s ×ˢ t) = (f ⁻¹' s) ∩ (g ⁻¹' t) := rfl

/- A special form of `pair_preimage` -/
lemma pair_preimage_singleton (f : α →ₛ β) (g : α →ₛ γ) (b : β) (c : γ) :
  (pair f g) ⁻¹' {(b, c)} = (f ⁻¹' {b}) ∩ (g ⁻¹' {c}) :=
by { rw ← singleton_prod_singleton, exact pair_preimage _ _ _ _ }

theorem bind_const (f : α →ₛ β) : f.bind (const α) = f := by ext; simp

@[to_additive] instance [has_one β] : has_one (α →ₛ β) := ⟨const α 1⟩
@[to_additive] instance [has_mul β] : has_mul (α →ₛ β) := ⟨λf g, (f.map (*)).seq g⟩
@[to_additive] instance [has_div β] : has_div (α →ₛ β) := ⟨λf g, (f.map (/)).seq g⟩
@[to_additive] instance [has_inv β] : has_inv (α →ₛ β) := ⟨λf, f.map (has_inv.inv)⟩
instance [has_sup β] : has_sup (α →ₛ β) := ⟨λf g, (f.map (⊔)).seq g⟩
instance [has_inf β] : has_inf (α →ₛ β) := ⟨λf g, (f.map (⊓)).seq g⟩
instance [has_le β] : has_le (α →ₛ β) := ⟨λf g, ∀a, f a ≤ g a⟩

@[simp, to_additive] lemma const_one [has_one β] : const α (1 : β) = 1 := rfl

@[simp, norm_cast, to_additive] lemma coe_one [has_one β] : ⇑(1 : α →ₛ β) = 1 := rfl
@[simp, norm_cast, to_additive] lemma coe_mul [has_mul β] (f g : α →ₛ β) : ⇑(f * g) = f * g := rfl
@[simp, norm_cast, to_additive] lemma coe_inv [has_inv β] (f : α →ₛ β) : ⇑(f⁻¹) = f⁻¹ := rfl
@[simp, norm_cast, to_additive] lemma coe_div [has_div β] (f g : α →ₛ β) : ⇑(f / g) = f / g := rfl
@[simp, norm_cast] lemma coe_le [preorder β] {f g : α →ₛ β} : (f : α → β) ≤ g ↔ f ≤ g := iff.rfl

@[to_additive] lemma mul_apply [has_mul β] (f g : α →ₛ β) (a : α) : (f * g) a = f a * g a := rfl
@[to_additive] lemma div_apply [has_div β] (f g : α →ₛ β) (x : α) : (f / g) x = f x / g x := rfl
@[to_additive] lemma inv_apply [has_inv β] (f : α →ₛ β) (x : α) : f⁻¹ x = (f x)⁻¹ := rfl
lemma sup_apply [has_sup β] (f g : α →ₛ β) (a : α) : (f ⊔ g) a = f a ⊔ g a := rfl
lemma inf_apply [has_inf β] (f g : α →ₛ β) (a : α) : (f ⊓ g) a = f a ⊓ g a := rfl

@[simp, to_additive] lemma range_one [nonempty α] [has_one β] : (1 : α →ₛ β).range = {1} :=
finset.ext $ λ x, by simp [eq_comm]

@[simp] lemma range_eq_empty_of_is_empty {β} [hα : is_empty α] (f : α →ₛ β) :
  f.range = ∅ :=
begin
  rw ← finset.not_nonempty_iff_eq_empty,
  by_contra,
  obtain ⟨y, hy_mem⟩ := h,
  rw [simple_func.mem_range, set.mem_range] at hy_mem,
  obtain ⟨x, hxy⟩ := hy_mem,
  rw is_empty_iff at hα,
  exact hα x,
end

lemma eq_zero_of_mem_range_zero [has_zero β] : ∀ {y : β}, y ∈ (0 : α →ₛ β).range → y = 0 :=
forall_range_iff.2 $ λ x, rfl

@[to_additive]
lemma mul_eq_map₂ [has_mul β] (f g : α →ₛ β) : f * g = (pair f g).map (λp:β×β, p.1 * p.2) := rfl

lemma sup_eq_map₂ [has_sup β] (f g : α →ₛ β) : f ⊔ g = (pair f g).map (λp:β×β, p.1 ⊔ p.2) := rfl

@[to_additive]
lemma const_mul_eq_map [has_mul β] (f : α →ₛ β) (b : β) : const α b * f = f.map (λa, b * a) := rfl

@[to_additive]
theorem map_mul [has_mul β] [has_mul γ] {g : β → γ}
  (hg : ∀ x y, g (x * y) = g x * g y) (f₁ f₂ : α →ₛ β) : (f₁ * f₂).map g = f₁.map g * f₂.map g :=
ext $ λ x, hg _ _

@[to_additive] instance [monoid β] : monoid (α →ₛ β) :=
function.injective.monoid (λ f, show α → β, from f) coe_injective coe_one coe_mul

@[to_additive] instance comm_monoid [comm_monoid β] : comm_monoid (α →ₛ β) :=
function.injective.comm_monoid (λ f, show α → β, from f) coe_injective coe_one coe_mul

@[to_additive] instance [group β] : group (α →ₛ β) :=
function.injective.group (λ f, show α → β, from f) coe_injective
  coe_one coe_mul coe_inv coe_div

@[to_additive] instance [comm_group β] : comm_group (α →ₛ β) :=
function.injective.comm_group (λ f, show α → β, from f) coe_injective
  coe_one coe_mul coe_inv coe_div

variables {K : Type*}

instance [has_scalar K β] : has_scalar K (α →ₛ β) := ⟨λk f, f.map ((•) k)⟩

@[simp] lemma coe_smul [has_scalar K β] (c : K) (f : α →ₛ β) : ⇑(c • f) = c • f := rfl

lemma smul_apply [has_scalar K β] (k : K) (f : α →ₛ β) (a : α) : (k • f) a = k • f a := rfl

instance [semiring K] [add_comm_monoid β] [module K β] : module K (α →ₛ β) :=
function.injective.module K ⟨λ f, show α → β, from f, coe_zero, coe_add⟩
  coe_injective coe_smul

lemma smul_eq_map [has_scalar K β] (k : K) (f : α →ₛ β) : k • f = f.map ((•) k) := rfl

instance [preorder β] : preorder (α →ₛ β) :=
{ le_refl := λf a, le_rfl,
  le_trans := λf g h hfg hgh a, le_trans (hfg _) (hgh a),
  .. simple_func.has_le }

instance [partial_order β] : partial_order (α →ₛ β) :=
{ le_antisymm := assume f g hfg hgf, ext $ assume a, le_antisymm (hfg a) (hgf a),
  .. simple_func.preorder }

instance [has_le β] [order_bot β] : order_bot (α →ₛ β) :=
{ bot := const α ⊥, bot_le := λf a, bot_le }

instance [has_le β] [order_top β] : order_top (α →ₛ β) :=
{ top := const α ⊤, le_top := λf a, le_top }

instance [semilattice_inf β] : semilattice_inf (α →ₛ β) :=
{ inf := (⊓),
  inf_le_left := assume f g a, inf_le_left,
  inf_le_right := assume f g a, inf_le_right,
  le_inf := assume f g h hfh hgh a, le_inf (hfh a) (hgh a),
  .. simple_func.partial_order }

instance [semilattice_sup β] : semilattice_sup (α →ₛ β) :=
{ sup := (⊔),
  le_sup_left := assume f g a, le_sup_left,
  le_sup_right := assume f g a, le_sup_right,
  sup_le := assume f g h hfh hgh a, sup_le (hfh a) (hgh a),
  .. simple_func.partial_order }

instance [lattice β] : lattice (α →ₛ β) :=
{ .. simple_func.semilattice_sup,.. simple_func.semilattice_inf }

instance [has_le β] [bounded_order β] : bounded_order (α →ₛ β) :=
{ .. simple_func.order_bot, .. simple_func.order_top }

lemma finset_sup_apply [semilattice_sup β] [order_bot β] {f : γ → α →ₛ β} (s : finset γ) (a : α) :
  s.sup f a = s.sup (λc, f c a) :=
begin
  refine finset.induction_on s rfl _,
  assume a s hs ih,
  rw [finset.sup_insert, finset.sup_insert, sup_apply, ih]
end

section restrict

variables [has_zero β]

/-- Restrict a simple function `f : α →ₛ β` to a set `s`. If `s` is measurable,
then `f.restrict s a = if a ∈ s then f a else 0`, otherwise `f.restrict s = const α 0`. -/
def restrict (f : α →ₛ β) (s : set α) : α →ₛ β :=
if hs : measurable_set s then piecewise s hs f 0 else 0

theorem restrict_of_not_measurable {f : α →ₛ β} {s : set α}
  (hs : ¬measurable_set s) :
  restrict f s = 0 :=
dif_neg hs

@[simp] theorem coe_restrict (f : α →ₛ β) {s : set α} (hs : measurable_set s) :
  ⇑(restrict f s) = indicator s f :=
by { rw [restrict, dif_pos hs], refl }

@[simp] theorem restrict_univ (f : α →ₛ β) : restrict f univ = f :=
by simp [restrict]

@[simp] theorem restrict_empty (f : α →ₛ β) : restrict f ∅ = 0 :=
by simp [restrict]

theorem map_restrict_of_zero [has_zero γ] {g : β → γ} (hg : g 0 = 0) (f : α →ₛ β) (s : set α) :
  (f.restrict s).map g = (f.map g).restrict s :=
ext $ λ x,
if hs : measurable_set s then by simp [hs, set.indicator_comp_of_zero hg]
else by simp [restrict_of_not_measurable hs, hg]

theorem map_coe_ennreal_restrict (f : α →ₛ ℝ≥0) (s : set α) :
  (f.restrict s).map (coe : ℝ≥0 → ℝ≥0∞) = (f.map coe).restrict s :=
map_restrict_of_zero ennreal.coe_zero _ _

theorem map_coe_nnreal_restrict (f : α →ₛ ℝ≥0) (s : set α) :
  (f.restrict s).map (coe : ℝ≥0 → ℝ) = (f.map coe).restrict s :=
map_restrict_of_zero nnreal.coe_zero _ _

theorem restrict_apply (f : α →ₛ β) {s : set α} (hs : measurable_set s) (a) :
  restrict f s a = indicator s f a :=
by simp only [f.coe_restrict hs]

theorem restrict_preimage (f : α →ₛ β) {s : set α} (hs : measurable_set s)
  {t : set β} (ht : (0:β) ∉ t) : restrict f s ⁻¹' t = s ∩ f ⁻¹' t :=
by simp [hs, indicator_preimage_of_not_mem _ _ ht, inter_comm]

theorem restrict_preimage_singleton (f : α →ₛ β) {s : set α} (hs : measurable_set s)
  {r : β} (hr : r ≠ 0) : restrict f s ⁻¹' {r} = s ∩ f ⁻¹' {r} :=
f.restrict_preimage hs hr.symm

lemma mem_restrict_range {r : β} {s : set α} {f : α →ₛ β} (hs : measurable_set s) :
  r ∈ (restrict f s).range ↔ (r = 0 ∧ s ≠ univ) ∨ (r ∈ f '' s) :=
by rw [← finset.mem_coe, coe_range, coe_restrict _ hs, mem_range_indicator]

lemma mem_image_of_mem_range_restrict {r : β} {s : set α} {f : α →ₛ β}
  (hr : r ∈ (restrict f s).range) (h0 : r ≠ 0) :
  r ∈ f '' s :=
if hs : measurable_set s then by simpa [mem_restrict_range hs, h0] using hr
else by { rw [restrict_of_not_measurable hs] at hr,
  exact (h0 $ eq_zero_of_mem_range_zero hr).elim }

@[mono] lemma restrict_mono [preorder β] (s : set α) {f g : α →ₛ β} (H : f ≤ g) :
  f.restrict s ≤ g.restrict s :=
if hs : measurable_set s then λ x, by simp only [coe_restrict _ hs, indicator_le_indicator (H x)]
else by simp only [restrict_of_not_measurable hs, le_refl]

end restrict

section approx

section
variables [semilattice_sup β] [order_bot β] [has_zero β]

/-- Fix a sequence `i : ℕ → β`. Given a function `α → β`, its `n`-th approximation
by simple functions is defined so that in case `β = ℝ≥0∞` it sends each `a` to the supremum
of the set `{i k | k ≤ n ∧ i k ≤ f a}`, see `approx_apply` and `supr_approx_apply` for details. -/
def approx (i : ℕ → β) (f : α → β) (n : ℕ) : α →ₛ β :=
(finset.range n).sup (λk, restrict (const α (i k)) {a:α | i k ≤ f a})

lemma approx_apply [topological_space β] [order_closed_topology β] [measurable_space β]
  [opens_measurable_space β] {i : ℕ → β} {f : α → β} {n : ℕ} (a : α) (hf : measurable f) :
  (approx i f n : α →ₛ β) a = (finset.range n).sup (λk, if i k ≤ f a then i k else 0) :=
begin
  dsimp only [approx],
  rw [finset_sup_apply],
  congr,
  funext k,
  rw [restrict_apply],
  refl,
  exact (hf measurable_set_Ici)
end

lemma monotone_approx (i : ℕ → β) (f : α → β) : monotone (approx i f) :=
assume n m h, finset.sup_mono $ finset.range_subset.2 h

lemma approx_comp [topological_space β] [order_closed_topology β] [measurable_space β]
  [opens_measurable_space β] [measurable_space γ]
  {i : ℕ → β} {f : γ → β} {g : α → γ} {n : ℕ} (a : α)
  (hf : measurable f) (hg : measurable g) :
  (approx i (f ∘ g) n : α →ₛ β) a = (approx i f n : γ →ₛ β) (g a) :=
by rw [approx_apply _ hf, approx_apply _ (hf.comp hg)]

end

lemma supr_approx_apply [topological_space β] [complete_lattice β] [order_closed_topology β]
  [has_zero β] [measurable_space β] [opens_measurable_space β]
  (i : ℕ → β) (f : α → β) (a : α) (hf : measurable f) (h_zero : (0 : β) = ⊥) :
  (⨆n, (approx i f n : α →ₛ β) a) = (⨆k (h : i k ≤ f a), i k) :=
begin
  refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume k, supr_le $ assume hk, _),
  { rw [approx_apply a hf, h_zero],
    refine finset.sup_le (assume k hk, _),
    split_ifs,
    exact le_supr_of_le k (le_supr _ h),
    exact bot_le },
  { refine le_supr_of_le (k+1) _,
    rw [approx_apply a hf],
    have : k ∈ finset.range (k+1) := finset.mem_range.2 (nat.lt_succ_self _),
    refine le_trans (le_of_eq _) (finset.le_sup this),
    rw [if_pos hk] }
end

end approx

section eapprox

/-- A sequence of `ℝ≥0∞`s such that its range is the set of non-negative rational numbers. -/
def ennreal_rat_embed (n : ℕ) : ℝ≥0∞ :=
ennreal.of_real ((encodable.decode ℚ n).get_or_else (0 : ℚ))

lemma ennreal_rat_embed_encode (q : ℚ) :
  ennreal_rat_embed (encodable.encode q) = real.to_nnreal q :=
by rw [ennreal_rat_embed, encodable.encodek]; refl

/-- Approximate a function `α → ℝ≥0∞` by a sequence of simple functions. -/
def eapprox : (α → ℝ≥0∞) → ℕ → α →ₛ ℝ≥0∞ :=
approx ennreal_rat_embed

lemma eapprox_lt_top (f : α → ℝ≥0∞) (n : ℕ) (a : α) : eapprox f n a < ∞ :=
begin
  simp only [eapprox, approx, finset_sup_apply, finset.sup_lt_iff, with_top.zero_lt_top,
    finset.mem_range, ennreal.bot_eq_zero, restrict],
  assume b hb,
  split_ifs,
  { simp only [coe_zero, coe_piecewise, piecewise_eq_indicator, coe_const],
    calc {a : α | ennreal_rat_embed b ≤ f a}.indicator (λ x, ennreal_rat_embed b) a
        ≤ ennreal_rat_embed b : indicator_le_self _ _ a
    ... < ⊤ : ennreal.coe_lt_top },
  { exact with_top.zero_lt_top },
end

@[mono] lemma monotone_eapprox (f : α → ℝ≥0∞) : monotone (eapprox f) :=
monotone_approx _ f

lemma supr_eapprox_apply (f : α → ℝ≥0∞) (hf : measurable f) (a : α) :
  (⨆n, (eapprox f n : α →ₛ ℝ≥0∞) a) = f a :=
begin
  rw [eapprox, supr_approx_apply ennreal_rat_embed f a hf rfl],
  refine le_antisymm (supr_le $ assume i, supr_le $ assume hi, hi) (le_of_not_gt _),
  assume h,
  rcases ennreal.lt_iff_exists_rat_btwn.1 h with ⟨q, hq, lt_q, q_lt⟩,
  have : (real.to_nnreal q : ℝ≥0∞) ≤
      (⨆ (k : ℕ) (h : ennreal_rat_embed k ≤ f a), ennreal_rat_embed k),
  { refine le_supr_of_le (encodable.encode q) _,
    rw [ennreal_rat_embed_encode q],
    refine le_supr_of_le (le_of_lt q_lt) _,
    exact le_rfl },
  exact lt_irrefl _ (lt_of_le_of_lt this lt_q)
end

lemma eapprox_comp [measurable_space γ] {f : γ → ℝ≥0∞} {g : α → γ} {n : ℕ}
  (hf : measurable f) (hg : measurable g) :
  (eapprox (f ∘ g) n : α → ℝ≥0∞) = (eapprox f n : γ →ₛ ℝ≥0∞) ∘ g :=
funext $ assume a, approx_comp a hf hg

/-- Approximate a function `α → ℝ≥0∞` by a series of simple functions taking their values
in `ℝ≥0`. -/
def eapprox_diff (f : α → ℝ≥0∞) : ∀ (n : ℕ), α →ₛ ℝ≥0
| 0 := (eapprox f 0).map ennreal.to_nnreal
| (n+1) := (eapprox f (n+1) - eapprox f n).map ennreal.to_nnreal

lemma sum_eapprox_diff (f : α → ℝ≥0∞) (n : ℕ) (a : α) :
  (∑ k in finset.range (n+1), (eapprox_diff f k a : ℝ≥0∞)) = eapprox f n a :=
begin
  induction n with n IH,
  { simp only [nat.nat_zero_eq_zero, finset.sum_singleton, finset.range_one], refl },
  { rw [finset.sum_range_succ, nat.succ_eq_add_one, IH, eapprox_diff, coe_map, function.comp_app,
        coe_sub, pi.sub_apply, ennreal.coe_to_nnreal,
        add_tsub_cancel_of_le (monotone_eapprox f (nat.le_succ _) _)],
    apply (lt_of_le_of_lt _ (eapprox_lt_top f (n+1) a)).ne,
    rw tsub_le_iff_right,
    exact le_self_add },
end

lemma tsum_eapprox_diff (f : α → ℝ≥0∞) (hf : measurable f) (a : α) :
  (∑' n, (eapprox_diff f n a : ℝ≥0∞)) = f a :=
by simp_rw [ennreal.tsum_eq_supr_nat' (tendsto_add_at_top_nat 1), sum_eapprox_diff,
  supr_eapprox_apply f hf a]

end eapprox

end measurable

section measure
variables {m : measurable_space α} {μ ν : measure α}

/-- Integral of a simple function whose codomain is `ℝ≥0∞`. -/
def lintegral {m : measurable_space α} (f : α →ₛ ℝ≥0∞) (μ : measure α) : ℝ≥0∞ :=
∑ x in f.range, x * μ (f ⁻¹' {x})

lemma lintegral_eq_of_subset (f : α →ₛ ℝ≥0∞) {s : finset ℝ≥0∞}
  (hs : ∀ x, f x ≠ 0 → μ (f ⁻¹' {f x}) ≠ 0 → f x ∈ s) :
  f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
begin
  refine finset.sum_bij_ne_zero (λr _ _, r) _ _ _ _,
  { simpa only [forall_range_iff, mul_ne_zero_iff, and_imp] },
  { intros, assumption },
  { intros b _ hb,
    refine ⟨b, _, hb, rfl⟩,
    rw [mem_range, ← preimage_singleton_nonempty],
    exact nonempty_of_measure_ne_zero (mul_ne_zero_iff.1 hb).2 },
  { intros, refl }
end

lemma lintegral_eq_of_subset' (f : α →ₛ ℝ≥0∞) {s : finset ℝ≥0∞}
  (hs : f.range \ {0} ⊆ s) :
  f.lintegral μ = ∑ x in s, x * μ (f ⁻¹' {x}) :=
f.lintegral_eq_of_subset $ λ x hfx _, hs $
  finset.mem_sdiff.2 ⟨f.mem_range_self x, mt finset.mem_singleton.1 hfx⟩

/-- Calculate the integral of `(g ∘ f)`, where `g : β → ℝ≥0∞` and `f : α →ₛ β`.  -/
lemma map_lintegral (g : β → ℝ≥0∞) (f : α →ₛ β) :
  (f.map g).lintegral μ = ∑ x in f.range, g x * μ (f ⁻¹' {x}) :=
begin
  simp only [lintegral, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  rw [map_preimage_singleton, ← f.sum_measure_preimage_singleton, finset.mul_sum],
  refine finset.sum_congr _ _,
  { congr },
  { assume x, simp only [finset.mem_filter], rintro ⟨_, h⟩, rw h },
end

lemma add_lintegral (f g : α →ₛ ℝ≥0∞) : (f + g).lintegral μ = f.lintegral μ + g.lintegral μ :=
calc (f + g).lintegral μ =
      ∑ x in (pair f g).range, (x.1 * μ (pair f g ⁻¹' {x}) + x.2 * μ (pair f g ⁻¹' {x})) :
    by rw [add_eq_map₂, map_lintegral]; exact finset.sum_congr rfl (assume a ha, add_mul _ _ _)
  ... = ∑ x in (pair f g).range, x.1 * μ (pair f g ⁻¹' {x}) +
      ∑ x in (pair f g).range, x.2 * μ (pair f g ⁻¹' {x}) : by rw [finset.sum_add_distrib]
  ... = ((pair f g).map prod.fst).lintegral μ + ((pair f g).map prod.snd).lintegral μ :
    by rw [map_lintegral, map_lintegral]
  ... = lintegral f μ + lintegral g μ : rfl

lemma const_mul_lintegral (f : α →ₛ ℝ≥0∞) (x : ℝ≥0∞) :
  (const α x * f).lintegral μ = x * f.lintegral μ :=
calc (f.map (λa, x * a)).lintegral μ = ∑ r in f.range, x * r * μ (f ⁻¹' {r}) :
    map_lintegral _ _
  ... = ∑ r in f.range, x * (r * μ (f ⁻¹' {r})) :
    finset.sum_congr rfl (assume a ha, mul_assoc _ _ _)
  ... = x * f.lintegral μ :
    finset.mul_sum.symm

/-- Integral of a simple function `α →ₛ ℝ≥0∞` as a bilinear map. -/
def lintegralₗ {m : measurable_space α} : (α →ₛ ℝ≥0∞) →ₗ[ℝ≥0∞] measure α →ₗ[ℝ≥0∞] ℝ≥0∞ :=
{ to_fun := λ f,
  { to_fun := lintegral f,
    map_add' := by simp [lintegral, mul_add, finset.sum_add_distrib],
    map_smul' := λ c μ, by simp [lintegral, mul_left_comm _ c, finset.mul_sum] },
  map_add' := λ f g, linear_map.ext (λ μ, add_lintegral f g),
  map_smul' := λ c f, linear_map.ext (λ μ, const_mul_lintegral f c) }

@[simp] lemma zero_lintegral : (0 : α →ₛ ℝ≥0∞).lintegral μ = 0 :=
linear_map.ext_iff.1 lintegralₗ.map_zero μ

lemma lintegral_add {ν} (f : α →ₛ ℝ≥0∞) : f.lintegral (μ + ν) = f.lintegral μ + f.lintegral ν :=
(lintegralₗ f).map_add μ ν

lemma lintegral_smul (f : α →ₛ ℝ≥0∞) (c : ℝ≥0∞) :
  f.lintegral (c • μ) = c • f.lintegral μ :=
(lintegralₗ f).map_smul c μ

@[simp] lemma lintegral_zero [measurable_space α] (f : α →ₛ ℝ≥0∞) :
  f.lintegral 0 = 0 :=
(lintegralₗ f).map_zero

lemma lintegral_sum {m : measurable_space α} {ι} (f : α →ₛ ℝ≥0∞) (μ : ι → measure α) :
  f.lintegral (measure.sum μ) = ∑' i, f.lintegral (μ i) :=
begin
  simp only [lintegral, measure.sum_apply, f.measurable_set_preimage, ← finset.tsum_subtype,
    ← ennreal.tsum_mul_left],
  apply ennreal.tsum_comm
end

lemma restrict_lintegral (f : α →ₛ ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  (restrict f s).lintegral μ = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :=
calc (restrict f s).lintegral μ = ∑ r in f.range, r * μ (restrict f s ⁻¹' {r}) :
  lintegral_eq_of_subset _ $ λ x hx, if hxs : x ∈ s
    then λ _, by simp only [f.restrict_apply hs, indicator_of_mem hxs, mem_range_self]
    else false.elim $ hx $ by simp [*]
... = ∑ r in f.range, r * μ (f ⁻¹' {r} ∩ s) :
  finset.sum_congr rfl $ forall_range_iff.2 $ λ b, if hb : f b = 0 then by simp only [hb, zero_mul]
    else by rw [restrict_preimage_singleton _ hs hb, inter_comm]

lemma lintegral_restrict {m : measurable_space α} (f : α →ₛ ℝ≥0∞) (s : set α) (μ : measure α) :
  f.lintegral (μ.restrict s) = ∑ y in f.range, y * μ (f ⁻¹' {y} ∩ s) :=
by simp only [lintegral, measure.restrict_apply, f.measurable_set_preimage]

lemma restrict_lintegral_eq_lintegral_restrict (f : α →ₛ ℝ≥0∞) {s : set α}
  (hs : measurable_set s) :
  (restrict f s).lintegral μ = f.lintegral (μ.restrict s) :=
by rw [f.restrict_lintegral hs, lintegral_restrict]

lemma const_lintegral (c : ℝ≥0∞) : (const α c).lintegral μ = c * μ univ :=
begin
  rw [lintegral],
  casesI is_empty_or_nonempty α,
  { simp [μ.eq_zero_of_is_empty] },
  { simp [preimage_const_of_mem] },
end

lemma const_lintegral_restrict (c : ℝ≥0∞) (s : set α) :
  (const α c).lintegral (μ.restrict s) = c * μ s :=
by rw [const_lintegral, measure.restrict_apply measurable_set.univ, univ_inter]

lemma restrict_const_lintegral (c : ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  ((const α c).restrict s).lintegral μ = c * μ s :=
by rw [restrict_lintegral_eq_lintegral_restrict _ hs, const_lintegral_restrict]

lemma le_sup_lintegral (f g : α →ₛ ℝ≥0∞) : f.lintegral μ ⊔ g.lintegral μ ≤ (f ⊔ g).lintegral μ :=
calc f.lintegral μ ⊔ g.lintegral μ =
      ((pair f g).map prod.fst).lintegral μ ⊔ ((pair f g).map prod.snd).lintegral μ : rfl
  ... ≤ ∑ x in (pair f g).range, (x.1 ⊔ x.2) * μ (pair f g ⁻¹' {x}) :
  begin
    rw [map_lintegral, map_lintegral],
    refine sup_le _ _;
      refine finset.sum_le_sum (λ a _, mul_le_mul_right' _ _),
    exact le_sup_left,
    exact le_sup_right
  end
  ... = (f ⊔ g).lintegral μ : by rw [sup_eq_map₂, map_lintegral]

/-- `simple_func.lintegral` is monotone both in function and in measure. -/
@[mono] lemma lintegral_mono {f g : α →ₛ ℝ≥0∞} (hfg : f ≤ g) (hμν : μ ≤ ν) :
  f.lintegral μ ≤ g.lintegral ν :=
calc f.lintegral μ ≤ f.lintegral μ ⊔ g.lintegral μ : le_sup_left
  ... ≤ (f ⊔ g).lintegral μ : le_sup_lintegral _ _
  ... = g.lintegral μ : by rw [sup_of_le_right hfg]
  ... ≤ g.lintegral ν : finset.sum_le_sum $ λ y hy, ennreal.mul_left_mono $
                          hμν _ (g.measurable_set_preimage _)

/-- `simple_func.lintegral` depends only on the measures of `f ⁻¹' {y}`. -/
lemma lintegral_eq_of_measure_preimage [measurable_space β] {f : α →ₛ ℝ≥0∞} {g : β →ₛ ℝ≥0∞}
  {ν : measure β} (H : ∀ y, μ (f ⁻¹' {y}) = ν (g ⁻¹' {y})) :
  f.lintegral μ = g.lintegral ν :=
begin
  simp only [lintegral, ← H],
  apply lintegral_eq_of_subset,
  simp only [H],
  intros,
  exact mem_range_of_measure_ne_zero ‹_›
end

/-- If two simple functions are equal a.e., then their `lintegral`s are equal. -/
lemma lintegral_congr {f g : α →ₛ ℝ≥0∞} (h : f =ᵐ[μ] g) :
  f.lintegral μ = g.lintegral μ :=
lintegral_eq_of_measure_preimage $ λ y, measure_congr $
  eventually.set_eq $ h.mono $ λ x hx, by simp [hx]

lemma lintegral_map' {β} [measurable_space β] {μ' : measure β} (f : α →ₛ ℝ≥0∞) (g : β →ₛ ℝ≥0∞)
  (m' : α → β) (eq : ∀ a, f a = g (m' a)) (h : ∀s, measurable_set s → μ' s = μ (m' ⁻¹' s)) :
  f.lintegral μ = g.lintegral μ' :=
lintegral_eq_of_measure_preimage $ λ y,
by { simp only [preimage, eq], exact (h (g ⁻¹' {y}) (g.measurable_set_preimage _)).symm }

lemma lintegral_map {β} [measurable_space β] (g : β →ₛ ℝ≥0∞) {f : α → β} (hf : measurable f) :
  g.lintegral (measure.map f μ) = (g.comp f hf).lintegral μ :=
eq.symm $ lintegral_map' _ _ f (λ a, rfl) (λ s hs, measure.map_apply hf hs)

end measure

section fin_meas_supp

open finset function

lemma support_eq [measurable_space α] [has_zero β] (f : α →ₛ β) :
  support f = ⋃ y ∈ f.range.filter (λ y, y ≠ 0), f ⁻¹' {y} :=
set.ext $ λ x, by simp only [mem_support, set.mem_preimage, mem_filter, mem_range_self, true_and,
  exists_prop, mem_Union, set.mem_range, mem_singleton_iff, exists_eq_right']

variables {m : measurable_space α} [has_zero β] [has_zero γ] {μ : measure α} {f : α →ₛ β}

lemma measurable_set_support [measurable_space α] (f : α →ₛ β) : measurable_set (support f) :=
by { rw f.support_eq, exact finset.measurable_set_bUnion _ (λ y hy, measurable_set_fiber _ _), }

/-- A `simple_func` has finite measure support if it is equal to `0` outside of a set of finite
measure. -/
protected def fin_meas_supp {m : measurable_space α} (f : α →ₛ β) (μ : measure α) : Prop :=
f =ᶠ[μ.cofinite] 0

lemma fin_meas_supp_iff_support : f.fin_meas_supp μ ↔ μ (support f) < ∞ := iff.rfl

lemma fin_meas_supp_iff : f.fin_meas_supp μ ↔ ∀ y ≠ 0, μ (f ⁻¹' {y}) < ∞ :=
begin
  split,
  { refine λ h y hy, lt_of_le_of_lt (measure_mono _) h,
    exact λ x hx (H : f x = 0), hy $ H ▸ eq.symm hx },
  { intro H,
    rw [fin_meas_supp_iff_support, support_eq],
    refine lt_of_le_of_lt (measure_bUnion_finset_le _ _) (sum_lt_top _),
    exact λ y hy, (H y (finset.mem_filter.1 hy).2).ne }
end

namespace fin_meas_supp

lemma meas_preimage_singleton_ne_zero (h : f.fin_meas_supp μ) {y : β} (hy : y ≠ 0) :
  μ (f ⁻¹' {y}) < ∞ :=
fin_meas_supp_iff.1 h y hy

protected lemma map {g : β → γ} (hf : f.fin_meas_supp μ) (hg : g 0 = 0) :
  (f.map g).fin_meas_supp μ :=
flip lt_of_le_of_lt hf (measure_mono $ support_comp_subset hg f)

lemma of_map {g : β → γ} (h : (f.map g).fin_meas_supp μ) (hg : ∀b, g b = 0 → b = 0) :
  f.fin_meas_supp μ :=
flip lt_of_le_of_lt h $ measure_mono $ support_subset_comp hg _

lemma map_iff {g : β → γ} (hg : ∀ {b}, g b = 0 ↔ b = 0) :
  (f.map g).fin_meas_supp μ ↔ f.fin_meas_supp μ :=
⟨λ h, h.of_map $ λ b, hg.1, λ h, h.map $ hg.2 rfl⟩

protected lemma pair {g : α →ₛ γ} (hf : f.fin_meas_supp μ) (hg : g.fin_meas_supp μ) :
  (pair f g).fin_meas_supp μ :=
calc μ (support $ pair f g) = μ (support f ∪ support g) : congr_arg μ $ support_prod_mk f g
... ≤ μ (support f) + μ (support g) : measure_union_le _ _
... < _ : add_lt_top.2 ⟨hf, hg⟩

protected lemma map₂ [has_zero δ] (hf : f.fin_meas_supp μ)
  {g : α →ₛ γ} (hg : g.fin_meas_supp μ) {op : β → γ → δ} (H : op 0 0 = 0) :
  ((pair f g).map (function.uncurry op)).fin_meas_supp μ :=
(hf.pair hg).map H

protected lemma add {β} [add_monoid β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f + g).fin_meas_supp μ :=
by { rw [add_eq_map₂], exact hf.map₂ hg (zero_add 0) }

protected lemma mul {β} [monoid_with_zero β] {f g : α →ₛ β} (hf : f.fin_meas_supp μ)
  (hg : g.fin_meas_supp μ) :
  (f * g).fin_meas_supp μ :=
by { rw [mul_eq_map₂], exact hf.map₂ hg (zero_mul 0) }

lemma lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hm : f.fin_meas_supp μ) (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
  f.lintegral μ < ∞ :=
begin
  refine sum_lt_top (λ a ha, _),
  rcases eq_or_ne a ∞ with rfl|ha,
  { simp only [ae_iff, ne.def, not_not] at hf,
    simp [set.preimage, hf] },
  { by_cases ha0 : a = 0,
    { subst a, rwa [zero_mul] },
    { exact mul_ne_top ha (fin_meas_supp_iff.1 hm _ ha0).ne } }
end

lemma of_lintegral_ne_top {f : α →ₛ ℝ≥0∞} (h : f.lintegral μ ≠ ∞) : f.fin_meas_supp μ :=
begin
  refine fin_meas_supp_iff.2 (λ b hb, _),
  rw [f.lintegral_eq_of_subset' (finset.subset_insert b _)] at h,
  refine ennreal.lt_top_of_mul_ne_top_right _ hb,
  exact (lt_top_of_sum_ne_top h (finset.mem_insert_self _ _)).ne
end

lemma iff_lintegral_lt_top {f : α →ₛ ℝ≥0∞} (hf : ∀ᵐ a ∂μ, f a ≠ ∞) :
  f.fin_meas_supp μ ↔ f.lintegral μ < ∞ :=
⟨λ h, h.lintegral_lt_top hf, λ h, of_lintegral_ne_top h.ne⟩

end fin_meas_supp

end fin_meas_supp

/-- To prove something for an arbitrary simple function, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under
addition (of functions with disjoint support).

It is possible to make the hypotheses in `h_add` a bit stronger, and such conditions can be added
once we need them (for example it is only necessary to consider the case where `g` is a multiple
of a characteristic function, and that this multiple doesn't appear in the image of `f`) -/
@[elab_as_eliminator]
protected lemma induction {α γ} [measurable_space α] [add_monoid γ] {P : simple_func α γ → Prop}
  (h_ind : ∀ c {s} (hs : measurable_set s),
    P (simple_func.piecewise s hs (simple_func.const _ c) (simple_func.const _ 0)))
  (h_add : ∀ ⦃f g : simple_func α γ⦄, disjoint (support f) (support g) → P f → P g → P (f + g))
  (f : simple_func α γ) : P f :=
begin
  generalize' h : f.range \ {0} = s,
  rw [← finset.coe_inj, finset.coe_sdiff, finset.coe_singleton, simple_func.coe_range] at h,
  revert s f h, refine finset.induction _ _,
  { intros f hf, rw [finset.coe_empty, diff_eq_empty, range_subset_singleton] at hf,
    convert h_ind 0 measurable_set.univ, ext x, simp [hf] },
  { intros x s hxs ih f hf,
    have mx := f.measurable_set_preimage {x},
    let g := simple_func.piecewise (f ⁻¹' {x}) mx 0 f,
    have Pg : P g,
    { apply ih, simp only [g, simple_func.coe_piecewise, range_piecewise],
      rw [image_compl_preimage, union_diff_distrib, diff_diff_comm, hf, finset.coe_insert,
        insert_diff_self_of_not_mem, diff_eq_empty.mpr, set.empty_union],
      { rw [set.image_subset_iff], convert set.subset_univ _,
        exact preimage_const_of_mem (mem_singleton _) },
      { rwa [finset.mem_coe] }},
    convert h_add _ Pg (h_ind x mx),
    { ext1 y, by_cases hy : y ∈ f ⁻¹' {x}; [simpa [hy], simp [hy]] },
    rintro y, by_cases hy : y ∈ f ⁻¹' {x}; simp [hy] }
end

end simple_func

section lintegral
open simple_func
variables {m : measurable_space α} {μ ν : measure α}

/-- The **lower Lebesgue integral** of a function `f` with respect to a measure `μ`. -/
@[irreducible] def lintegral {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞) : ℝ≥0∞ :=
⨆ (g : α →ₛ ℝ≥0∞) (hf : ⇑g ≤ f), g.lintegral μ

/-! In the notation for integrals, an expression like `∫⁻ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫⁻ x, f x = 0` will be parsed incorrectly. -/
notation `∫⁻` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := lintegral μ r
notation `∫⁻` binders `, ` r:(scoped:60 f, lintegral volume f) := r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 :=
  lintegral (measure.restrict μ s) r
notation `∫⁻` binders ` in ` s `, ` r:(scoped:60 f, lintegral (measure.restrict volume s) f) := r

theorem simple_func.lintegral_eq_lintegral {m : measurable_space α} (f : α →ₛ ℝ≥0∞)
  (μ : measure α) :
  ∫⁻ a, f a ∂ μ = f.lintegral μ :=
begin
  rw lintegral,
  exact le_antisymm
    (bsupr_le $ λ g hg, lintegral_mono hg $ le_rfl)
    (le_supr_of_le f $ le_supr_of_le le_rfl le_rfl)
end

@[mono] lemma lintegral_mono' {m : measurable_space α} ⦃μ ν : measure α⦄ (hμν : μ ≤ ν)
  ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂ν :=
begin
  rw [lintegral, lintegral],
  exact supr_le_supr (λ φ, supr_le_supr2 $ λ hφ, ⟨le_trans hφ hfg, lintegral_mono (le_refl φ) hμν⟩)
end

lemma lintegral_mono ⦃f g : α → ℝ≥0∞⦄ (hfg : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
lintegral_mono' (le_refl μ) hfg

lemma lintegral_mono_nnreal {f g : α → ℝ≥0} (h : f ≤ g) :
  ∫⁻ a, f a ∂μ ≤ ∫⁻ a, g a ∂μ :=
begin
  refine lintegral_mono _,
  intro a,
  rw ennreal.coe_le_coe,
  exact h a,
end

lemma supr_lintegral_measurable_le_eq_lintegral (f : α → ℝ≥0∞) :
  (⨆ (g : α → ℝ≥0∞) (g_meas : measurable g) (hg : g ≤ f), ∫⁻ a, g a ∂μ) = ∫⁻ a, f a ∂μ :=
begin
  apply le_antisymm,
  { exact supr_le (λ i, supr_le (λ hi, supr_le (λ h'i, lintegral_mono h'i))) },
  { rw lintegral,
    refine bsupr_le (λ i hi, le_supr_of_le i (le_supr_of_le i.measurable (le_supr_of_le hi _))),
    exact le_of_eq (i.lintegral_eq_lintegral _).symm },
end

lemma lintegral_mono_set {m : measurable_space α} ⦃μ : measure α⦄
  {s t : set α} {f : α → ℝ≥0∞} (hst : s ⊆ t) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
lintegral_mono' (measure.restrict_mono hst (le_refl μ)) (le_refl f)

lemma lintegral_mono_set' {m : measurable_space α} ⦃μ : measure α⦄
  {s t : set α} {f : α → ℝ≥0∞} (hst : s ≤ᵐ[μ] t) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in t, f x ∂μ :=
lintegral_mono' (measure.restrict_mono' hst (le_refl μ)) (le_refl f)

lemma monotone_lintegral {m : measurable_space α} (μ : measure α) : monotone (lintegral μ) :=
lintegral_mono

@[simp] lemma lintegral_const (c : ℝ≥0∞) : ∫⁻ a, c ∂μ = c * μ univ :=
by rw [← simple_func.const_lintegral, ← simple_func.lintegral_eq_lintegral, simple_func.coe_const]

@[simp] lemma lintegral_one : ∫⁻ a, (1 : ℝ≥0∞) ∂μ = μ univ :=
by rw [lintegral_const, one_mul]

lemma set_lintegral_const (s : set α) (c : ℝ≥0∞) : ∫⁻ a in s, c ∂μ = c * μ s :=
by rw [lintegral_const, measure.restrict_apply_univ]

lemma set_lintegral_one (s) : ∫⁻ a in s, 1 ∂μ = μ s :=
by rw [set_lintegral_const, one_mul]

/-- `∫⁻ a in s, f a ∂μ` is defined as the supremum of integrals of simple functions
`φ : α →ₛ ℝ≥0∞` such that `φ ≤ f`. This lemma says that it suffices to take
functions `φ : α →ₛ ℝ≥0`. -/
lemma lintegral_eq_nnreal {m : measurable_space α} (f : α → ℝ≥0∞) (μ : measure α) :
  (∫⁻ a, f a ∂μ) = (⨆ (φ : α →ₛ ℝ≥0) (hf : ∀ x, ↑(φ x) ≤ f x),
      (φ.map (coe : ℝ≥0 → ℝ≥0∞)).lintegral μ) :=
begin
  rw lintegral,
  refine le_antisymm
    (bsupr_le $ assume φ hφ, _)
    (supr_le_supr2 $ λ φ, ⟨φ.map (coe : ℝ≥0 → ℝ≥0∞), le_rfl⟩),
  by_cases h : ∀ᵐ a ∂μ, φ a ≠ ∞,
  { let ψ := φ.map ennreal.to_nnreal,
    replace h : ψ.map (coe : ℝ≥0 → ℝ≥0∞) =ᵐ[μ] φ :=
      h.mono (λ a, ennreal.coe_to_nnreal),
    have : ∀ x, ↑(ψ x) ≤ f x := λ x, le_trans ennreal.coe_to_nnreal_le_self (hφ x),
    exact le_supr_of_le (φ.map ennreal.to_nnreal)
      (le_supr_of_le this (ge_of_eq $ lintegral_congr h)) },
  { have h_meas : μ (φ ⁻¹' {∞}) ≠ 0, from mt measure_zero_iff_ae_nmem.1 h,
    refine le_trans le_top (ge_of_eq $ (supr_eq_top _).2 $ λ b hb, _),
    obtain ⟨n, hn⟩ : ∃ n : ℕ, b < n * μ (φ ⁻¹' {∞}), from exists_nat_mul_gt h_meas (ne_of_lt hb),
    use (const α (n : ℝ≥0)).restrict (φ ⁻¹' {∞}),
    simp only [lt_supr_iff, exists_prop, coe_restrict, φ.measurable_set_preimage, coe_const,
      ennreal.coe_indicator, map_coe_ennreal_restrict, map_const, ennreal.coe_nat,
      restrict_const_lintegral],
    refine ⟨indicator_le (λ x hx, le_trans _ (hφ _)), hn⟩,
    simp only [mem_preimage, mem_singleton_iff] at hx,
    simp only [hx, le_top] }
end

lemma exists_simple_func_forall_lintegral_sub_lt_of_pos {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
  {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ φ : α →ₛ ℝ≥0, (∀ x, ↑(φ x) ≤ f x) ∧ ∀ ψ : α →ₛ ℝ≥0, (∀ x, ↑(ψ x) ≤ f x) →
    (map coe (ψ - φ)).lintegral μ < ε :=
begin
  rw lintegral_eq_nnreal at h,
  have := ennreal.lt_add_right h hε,
  erw ennreal.bsupr_add at this; [skip, exact ⟨0, λ x, by simp⟩],
  simp_rw [lt_supr_iff, supr_lt_iff, supr_le_iff] at this,
  rcases this with ⟨φ, hle : ∀ x, ↑(φ x) ≤ f x, b, hbφ, hb⟩,
  refine ⟨φ, hle, λ ψ hψ, _⟩,
  have : (map coe φ).lintegral μ ≠ ∞, from ne_top_of_le_ne_top h (le_bsupr φ hle),
  rw [← add_lt_add_iff_left this, ← add_lintegral, ← map_add @ennreal.coe_add],
  refine (hb _ (λ x, le_trans _ (max_le (hle x) (hψ x)))).trans_lt hbφ,
  norm_cast,
  simp only [add_apply, sub_apply, add_tsub_eq_max]
end

theorem supr_lintegral_le {ι : Sort*} (f : ι → α → ℝ≥0∞) :
  (⨆i, ∫⁻ a, f i a ∂μ) ≤ (∫⁻ a, ⨆i, f i a ∂μ) :=
begin
  simp only [← supr_apply],
  exact (monotone_lintegral μ).le_map_supr
end

theorem supr2_lintegral_le {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ℝ≥0∞) :
  (⨆i (h : ι' i), ∫⁻ a, f i h a ∂μ) ≤ (∫⁻ a, ⨆i (h : ι' i), f i h a ∂μ) :=
by { convert (monotone_lintegral μ).le_map_supr2 f, ext1 a, simp only [supr_apply] }

theorem le_infi_lintegral {ι : Sort*} (f : ι → α → ℝ≥0∞) :
  (∫⁻ a, ⨅i, f i a ∂μ) ≤ (⨅i, ∫⁻ a, f i a ∂μ) :=
by { simp only [← infi_apply], exact (monotone_lintegral μ).map_infi_le }

theorem le_infi2_lintegral {ι : Sort*} {ι' : ι → Sort*} (f : Π i, ι' i → α → ℝ≥0∞) :
  (∫⁻ a, ⨅ i (h : ι' i), f i h a ∂μ) ≤ (⨅ i (h : ι' i), ∫⁻ a, f i h a ∂μ) :=
by { convert (monotone_lintegral μ).map_infi2_le f, ext1 a, simp only [infi_apply] }

lemma lintegral_mono_ae {f g : α → ℝ≥0∞} (h : ∀ᵐ a ∂μ, f a ≤ g a) :
  (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, g a ∂μ) :=
begin
  rcases exists_measurable_superset_of_null h with ⟨t, hts, ht, ht0⟩,
  have : ∀ᵐ x ∂μ, x ∉ t := measure_zero_iff_ae_nmem.1 ht0,
  rw [lintegral, lintegral],
  refine (supr_le $ assume s, supr_le $ assume hfs,
    le_supr_of_le (s.restrict tᶜ) $ le_supr_of_le _ _),
  { assume a,
    by_cases a ∈ t;
      simp [h, restrict_apply, ht.compl],
    exact le_trans (hfs a) (by_contradiction $ assume hnfg, h (hts hnfg)) },
  { refine le_of_eq (simple_func.lintegral_congr $ this.mono $ λ a hnt, _),
    by_cases hat : a ∈ t; simp [hat, ht.compl],
    exact (hnt hat).elim }
end

lemma set_lintegral_mono_ae {s : set α} {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfg : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
lintegral_mono_ae $ (ae_restrict_iff $ measurable_set_le hf hg).2 hfg

lemma set_lintegral_mono {s : set α} {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfg : ∀ x ∈ s, f x ≤ g x) :
  ∫⁻ x in s, f x ∂μ ≤ ∫⁻ x in s, g x ∂μ :=
set_lintegral_mono_ae hf hg (ae_of_all _ hfg)

lemma lintegral_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
  (∫⁻ a, f a ∂μ) = (∫⁻ a, g a ∂μ) :=
le_antisymm (lintegral_mono_ae $ h.le) (lintegral_mono_ae $ h.symm.le)

lemma lintegral_congr {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) :
  (∫⁻ a, f a ∂μ) = (∫⁻ a, g a ∂μ) :=
by simp only [h]

lemma set_lintegral_congr {f : α → ℝ≥0∞} {s t : set α} (h : s =ᵐ[μ] t) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
by rw [measure.restrict_congr_set h]

lemma set_lintegral_congr_fun {f g : α → ℝ≥0∞} {s : set α} (hs : measurable_set s)
  (hfg : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
  ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ :=
by { rw lintegral_congr_ae, rw eventually_eq, rwa ae_restrict_iff' hs, }

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence.

See `lintegral_supr_directed` for a more general form. -/
theorem lintegral_supr
  {f : ℕ → α → ℝ≥0∞} (hf : ∀n, measurable (f n)) (h_mono : monotone f) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
begin
  set c : ℝ≥0 → ℝ≥0∞ := coe,
  set F := λ a:α, ⨆n, f n a,
  have hF : measurable F := measurable_supr hf,
  refine le_antisymm _ (supr_lintegral_le _),
  rw [lintegral_eq_nnreal],
  refine supr_le (assume s, supr_le (assume hsf, _)),
  refine ennreal.le_of_forall_lt_one_mul_le (assume a ha, _),
  rcases ennreal.lt_iff_exists_coe.1 ha with ⟨r, rfl, ha⟩,
  have ha : r < 1 := ennreal.coe_lt_coe.1 ha,
  let rs := s.map (λa, r * a),
  have eq_rs : (const α r : α →ₛ ℝ≥0∞) * map c s = rs.map c,
  { ext1 a, exact ennreal.coe_mul.symm },
  have eq : ∀p, (rs.map c) ⁻¹' {p} = (⋃n, (rs.map c) ⁻¹' {p} ∩ {a | p ≤ f n a}),
  { assume p,
    rw [← inter_Union, ← inter_univ ((map c rs) ⁻¹' {p})] {occs := occurrences.pos [1]},
    refine set.ext (assume x, and_congr_right $ assume hx, (true_iff _).2 _),
    by_cases p_eq : p = 0, { simp [p_eq] },
    simp at hx, subst hx,
    have : r * s x ≠ 0, { rwa [(≠), ← ennreal.coe_eq_zero] },
    have : s x ≠ 0, { refine mt _ this, assume h, rw [h, mul_zero] },
    have : (rs.map c) x < ⨆ (n : ℕ), f n x,
    { refine lt_of_lt_of_le (ennreal.coe_lt_coe.2 (_)) (hsf x),
      suffices : r * s x < 1 * s x, simpa [rs],
      exact mul_lt_mul_of_pos_right ha (pos_iff_ne_zero.2 this) },
    rcases lt_supr_iff.1 this with ⟨i, hi⟩,
    exact mem_Union.2 ⟨i, le_of_lt hi⟩ },
  have mono : ∀r:ℝ≥0∞, monotone (λn, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}),
  { assume r i j h,
    refine inter_subset_inter (subset.refl _) _,
    assume x hx, exact le_trans hx (h_mono h x) },
  have h_meas : ∀n, measurable_set {a : α | ⇑(map c rs) a ≤ f n a} :=
    assume n, measurable_set_le (simple_func.measurable _) (hf n),
  calc (r:ℝ≥0∞) * (s.map c).lintegral μ = ∑ r in (rs.map c).range, r * μ ((rs.map c) ⁻¹' {r}) :
      by rw [← const_mul_lintegral, eq_rs, simple_func.lintegral]
    ... = ∑ r in (rs.map c).range, r * μ (⋃n, (rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      by simp only [(eq _).symm]
    ... = ∑ r in (rs.map c).range, (⨆n, r * μ ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a})) :
      finset.sum_congr rfl $ assume x hx,
        begin
          rw [measure_Union_eq_supr (directed_of_sup $ mono x), ennreal.mul_supr],
        end
    ... = ⨆n, ∑ r in (rs.map c).range, r * μ ((rs.map c) ⁻¹' {r} ∩ {a | r ≤ f n a}) :
      begin
        rw [ennreal.finset_sum_supr_nat],
        assume p i j h,
        exact mul_le_mul_left' (measure_mono $ mono p h) _
      end
    ... ≤ (⨆n:ℕ, ((rs.map c).restrict {a | (rs.map c) a ≤ f n a}).lintegral μ) :
    begin
      refine supr_le_supr (assume n, _),
      rw [restrict_lintegral _ (h_meas n)],
      { refine le_of_eq (finset.sum_congr rfl $ assume r hr, _),
        congr' 2 with a,
        refine and_congr_right _,
        simp {contextual := tt} }
    end
    ... ≤ (⨆n, ∫⁻ a, f n a ∂μ) :
    begin
      refine supr_le_supr (assume n, _),
      rw [← simple_func.lintegral_eq_lintegral],
      refine lintegral_mono (assume a, _),
      simp only [map_apply] at h_meas,
      simp only [coe_map, restrict_apply _ (h_meas _), (∘)],
      exact indicator_apply_le id,
    end
end

/-- Monotone convergence theorem -- sometimes called Beppo-Levi convergence. Version with
ae_measurable functions. -/
theorem lintegral_supr' {f : ℕ → α → ℝ≥0∞} (hf : ∀n, ae_measurable (f n) μ)
  (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x)) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
begin
  simp_rw ←supr_apply,
  let p : α → (ℕ → ℝ≥0∞) → Prop := λ x f', monotone f',
  have hp : ∀ᵐ x ∂μ, p x (λ i, f i x), from h_mono,
  have h_ae_seq_mono : monotone (ae_seq hf p),
  { intros n m hnm x,
    by_cases hx : x ∈ ae_seq_set hf p,
    { exact ae_seq.prop_of_mem_ae_seq_set hf hx hnm, },
    { simp only [ae_seq, hx, if_false],
      exact le_rfl, }, },
  rw lintegral_congr_ae (ae_seq.supr hf hp).symm,
  simp_rw supr_apply,
  rw @lintegral_supr _ _ μ _ (ae_seq.measurable hf p) h_ae_seq_mono,
  congr,
  exact funext (λ n, lintegral_congr_ae (ae_seq.ae_seq_n_eq_fun_n_ae hf hp n)),
end

/-- Monotone convergence theorem expressed with limits -/
theorem lintegral_tendsto_of_tendsto_of_monotone {f : ℕ → α → ℝ≥0∞} {F : α → ℝ≥0∞}
  (hf : ∀n, ae_measurable (f n) μ) (h_mono : ∀ᵐ x ∂μ, monotone (λ n, f n x))
  (h_tendsto : ∀ᵐ x ∂μ, tendsto (λ n, f n x) at_top (𝓝 $ F x)) :
  tendsto (λ n, ∫⁻ x, f n x ∂μ) at_top (𝓝 $ ∫⁻ x, F x ∂μ) :=
begin
  have : monotone (λ n, ∫⁻ x, f n x ∂μ) :=
    λ i j hij, lintegral_mono_ae (h_mono.mono $ λ x hx, hx hij),
  suffices key : ∫⁻ x, F x ∂μ = ⨆n, ∫⁻ x, f n x ∂μ,
  { rw key,
    exact tendsto_at_top_supr this },
  rw ← lintegral_supr' hf h_mono,
  refine lintegral_congr_ae _,
  filter_upwards [h_mono, h_tendsto]
    with _ hx_mono hx_tendsto using tendsto_nhds_unique hx_tendsto (tendsto_at_top_supr hx_mono),
end

lemma lintegral_eq_supr_eapprox_lintegral {f : α → ℝ≥0∞} (hf : measurable f) :
  (∫⁻ a, f a ∂μ) = (⨆n, (eapprox f n).lintegral μ) :=
calc (∫⁻ a, f a ∂μ) = (∫⁻ a, ⨆n, (eapprox f n : α → ℝ≥0∞) a ∂μ) :
  by congr; ext a; rw [supr_eapprox_apply f hf]
... = (⨆n, ∫⁻ a, (eapprox f n : α → ℝ≥0∞) a ∂μ) :
begin
  rw [lintegral_supr],
  { measurability, },
  { assume i j h, exact (monotone_eapprox f h) }
end
... = (⨆n, (eapprox f n).lintegral μ) : by congr; ext n; rw [(eapprox f n).lintegral_eq_lintegral]

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. This lemma states states this fact in terms of `ε` and `δ`. -/
lemma exists_pos_set_lintegral_lt_of_measure_lt {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
  {ε : ℝ≥0∞} (hε : ε ≠ 0) :
  ∃ δ > 0, ∀ s, μ s < δ → ∫⁻ x in s, f x ∂μ < ε :=
begin
  rcases exists_between hε.bot_lt with ⟨ε₂, hε₂0 : 0 < ε₂, hε₂ε⟩,
  rcases exists_between hε₂0 with ⟨ε₁, hε₁0, hε₁₂⟩,
  rcases exists_simple_func_forall_lintegral_sub_lt_of_pos h hε₁0.ne' with ⟨φ, hle, hφ⟩,
  rcases φ.exists_forall_le with ⟨C, hC⟩,
  use [(ε₂ - ε₁) / C, ennreal.div_pos_iff.2 ⟨(tsub_pos_iff_lt.2 hε₁₂).ne', ennreal.coe_ne_top⟩],
  refine λ s hs, lt_of_le_of_lt _ hε₂ε,
  simp only [lintegral_eq_nnreal, supr_le_iff],
  intros ψ hψ,
  calc (map coe ψ).lintegral (μ.restrict s)
      ≤ (map coe φ).lintegral (μ.restrict s) + (map coe (ψ - φ)).lintegral (μ.restrict s) :
    begin
      rw [← simple_func.add_lintegral, ← simple_func.map_add @ennreal.coe_add],
      refine simple_func.lintegral_mono (λ x, _) le_rfl,
      simp [-ennreal.coe_add, add_tsub_eq_max, le_max_right]
    end
  ... ≤ (map coe φ).lintegral (μ.restrict s) + ε₁ :
    begin
      refine add_le_add le_rfl (le_trans _ (hφ _ hψ).le),
      exact simple_func.lintegral_mono le_rfl measure.restrict_le_self
    end
  ... ≤ (simple_func.const α (C : ℝ≥0∞)).lintegral (μ.restrict s) + ε₁ :
    by { mono*, exacts [λ x, coe_le_coe.2 (hC x), le_rfl, le_rfl] }
  ... = C * μ s + ε₁ : by simp [← simple_func.lintegral_eq_lintegral]
  ... ≤ C * ((ε₂ - ε₁) / C) + ε₁ : by { mono*, exacts [le_rfl, hs.le, le_rfl] }
  ... ≤ (ε₂ - ε₁) + ε₁ : add_le_add mul_div_le le_rfl
  ... = ε₂ : tsub_add_cancel_of_le hε₁₂.le,
end

/-- If `f` has finite integral, then `∫⁻ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma tendsto_set_lintegral_zero {ι} {f : α → ℝ≥0∞} (h : ∫⁻ x, f x ∂μ ≠ ∞)
  {l : filter ι} {s : ι → set α} (hl : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫⁻ x in s i, f x ∂μ) l (𝓝 0) :=
begin
  simp only [ennreal.nhds_zero, tendsto_infi, tendsto_principal, mem_Iio, ← pos_iff_ne_zero]
    at hl ⊢,
  intros ε ε0,
  rcases exists_pos_set_lintegral_lt_of_measure_lt h ε0.ne' with ⟨δ, δ0, hδ⟩,
  exact (hl δ δ0).mono (λ i, hδ _)
end

@[simp] lemma lintegral_add {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :=
calc (∫⁻ a, f a + g a ∂μ) =
    (∫⁻ a, (⨆n, (eapprox f n : α → ℝ≥0∞) a) + (⨆n, (eapprox g n : α → ℝ≥0∞) a) ∂μ) :
    by simp only [supr_eapprox_apply, hf, hg]
  ... = (∫⁻ a, (⨆n, (eapprox f n + eapprox g n : α → ℝ≥0∞) a) ∂μ) :
  begin
    congr, funext a,
    rw [ennreal.supr_add_supr_of_monotone], { refl },
    { assume i j h, exact monotone_eapprox _ h a },
    { assume i j h, exact monotone_eapprox _ h a },
  end
  ... = (⨆n, (eapprox f n).lintegral μ + (eapprox g n).lintegral μ) :
  begin
    rw [lintegral_supr],
    { congr,
      funext n, rw [← simple_func.add_lintegral, ← simple_func.lintegral_eq_lintegral],
      refl },
    { measurability, },
    { assume i j h a, exact add_le_add (monotone_eapprox _ h _) (monotone_eapprox _ h _) }
  end
  ... = (⨆n, (eapprox f n).lintegral μ) + (⨆n, (eapprox g n).lintegral μ) :
  by refine (ennreal.supr_add_supr_of_monotone _ _).symm;
     { assume i j h, exact simple_func.lintegral_mono (monotone_eapprox _ h) (le_refl μ) }
  ... = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :
    by rw [lintegral_eq_supr_eapprox_lintegral hf, lintegral_eq_supr_eapprox_lintegral hg]

lemma lintegral_add' {f g : α → ℝ≥0∞} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) :=
calc (∫⁻ a, f a + g a ∂μ) = (∫⁻ a, hf.mk f a + hg.mk g a ∂μ) :
  lintegral_congr_ae (eventually_eq.add hf.ae_eq_mk hg.ae_eq_mk)
... = (∫⁻ a, hf.mk f a ∂μ) + (∫⁻ a, hg.mk g a ∂μ) : lintegral_add hf.measurable_mk hg.measurable_mk
... = (∫⁻ a, f a ∂μ) + (∫⁻ a, g a ∂μ) : begin
  congr' 1,
  { exact lintegral_congr_ae hf.ae_eq_mk.symm },
  { exact lintegral_congr_ae hg.ae_eq_mk.symm },
end

lemma lintegral_zero : (∫⁻ a:α, 0 ∂μ) = 0 := by simp

lemma lintegral_zero_fun : (∫⁻ a:α, (0 : α → ℝ≥0∞) a ∂μ) = 0 := by simp

@[simp] lemma lintegral_smul_measure (c : ℝ≥0∞) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂ (c • μ) = c * ∫⁻ a, f a ∂μ :=
by simp only [lintegral, supr_subtype', simple_func.lintegral_smul, ennreal.mul_supr, smul_eq_mul]

@[simp] lemma lintegral_sum_measure {m : measurable_space α} {ι} (f : α → ℝ≥0∞)
  (μ : ι → measure α) :
  ∫⁻ a, f a ∂(measure.sum μ) = ∑' i, ∫⁻ a, f a ∂(μ i) :=
begin
  simp only [lintegral, supr_subtype', simple_func.lintegral_sum, ennreal.tsum_eq_supr_sum],
  rw [supr_comm],
  congr, funext s,
  induction s using finset.induction_on with i s hi hs, { apply bot_unique, simp },
  simp only [finset.sum_insert hi, ← hs],
  refine (ennreal.supr_add_supr _).symm,
  intros φ ψ,
  exact ⟨⟨φ ⊔ ψ, λ x, sup_le (φ.2 x) (ψ.2 x)⟩,
    add_le_add (simple_func.lintegral_mono le_sup_left le_rfl)
      (finset.sum_le_sum $ λ j hj, simple_func.lintegral_mono le_sup_right le_rfl)⟩
end

@[simp] lemma lintegral_add_measure {m : measurable_space α} (f : α → ℝ≥0∞) (μ ν : measure α) :
  ∫⁻ a, f a ∂ (μ + ν) = ∫⁻ a, f a ∂μ + ∫⁻ a, f a ∂ν :=
by simpa [tsum_fintype] using lintegral_sum_measure f (λ b, cond b μ ν)

@[simp] lemma lintegral_zero_measure {m : measurable_space α} (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂(0 : measure α) = 0 :=
bot_unique $ by simp [lintegral]

lemma set_lintegral_empty (f : α → ℝ≥0∞) : ∫⁻ x in ∅, f x ∂μ = 0 :=
by rw [measure.restrict_empty, lintegral_zero_measure]

lemma set_lintegral_univ (f : α → ℝ≥0∞) : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw measure.restrict_univ

lemma set_lintegral_measure_zero (s : set α) (f : α → ℝ≥0∞) (hs' : μ s = 0) :
  ∫⁻ x in s, f x ∂μ = 0 :=
begin
  convert lintegral_zero_measure _,
  exact measure.restrict_eq_zero.2 hs',
end

lemma lintegral_finset_sum (s : finset β) {f : β → α → ℝ≥0∞} (hf : ∀ b ∈ s, measurable (f b)) :
  (∫⁻ a, ∑ b in s, f b a ∂μ) = ∑ b in s, ∫⁻ a, f b a ∂μ :=
begin
  induction s using finset.induction_on with a s has ih,
  { simp },
  { simp only [finset.sum_insert has],
    rw [finset.forall_mem_insert] at hf,
    rw [lintegral_add hf.1 (s.measurable_sum hf.2), ih hf.2] }
end

@[simp] lemma lintegral_const_mul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
calc (∫⁻ a, r * f a ∂μ) = (∫⁻ a, (⨆n, (const α r * eapprox f n) a) ∂μ) :
    by { congr, funext a, rw [← supr_eapprox_apply f hf, ennreal.mul_supr], refl }
  ... = (⨆n, r * (eapprox f n).lintegral μ) :
  begin
    rw [lintegral_supr],
    { congr, funext n,
      rw [← simple_func.const_mul_lintegral, ← simple_func.lintegral_eq_lintegral] },
    { assume n, exact simple_func.measurable _ },
    { assume i j h a, exact mul_le_mul_left' (monotone_eapprox _ h _) _ }
  end
  ... = r * (∫⁻ a, f a ∂μ) : by rw [← ennreal.mul_supr, lintegral_eq_supr_eapprox_lintegral hf]

lemma lintegral_const_mul'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
begin
  have A : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk,
  have B : ∫⁻ a, r * f a ∂μ = ∫⁻ a, r * hf.mk f a ∂μ :=
    lintegral_congr_ae (eventually_eq.fun_comp hf.ae_eq_mk _),
  rw [A, B, lintegral_const_mul _ hf.measurable_mk],
end

lemma lintegral_const_mul_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
  r * (∫⁻ a, f a ∂μ) ≤ (∫⁻ a, r * f a ∂μ) :=
begin
  rw [lintegral, ennreal.mul_supr],
  refine supr_le (λs, _),
  rw [ennreal.mul_supr],
  simp only [supr_le_iff, ge_iff_le],
  assume hs,
  rw [← simple_func.const_mul_lintegral, lintegral],
  refine le_supr_of_le (const α r * s) (le_supr_of_le (λx, _) le_rfl),
  exact mul_le_mul_left' (hs x) _
end

lemma lintegral_const_mul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
  (∫⁻ a, r * f a ∂μ) = r * (∫⁻ a, f a ∂μ) :=
begin
  by_cases h : r = 0,
  { simp [h] },
  apply le_antisymm _ (lintegral_const_mul_le r f),
  have rinv : r * r⁻¹  = 1 := ennreal.mul_inv_cancel h hr,
  have rinv' : r ⁻¹ * r = 1, by { rw mul_comm, exact rinv },
  have := lintegral_const_mul_le (r⁻¹) (λx, r * f x),
  simp [(mul_assoc _ _ _).symm, rinv'] at this,
  simpa [(mul_assoc _ _ _).symm, rinv]
    using mul_le_mul_left' this r
end

lemma lintegral_mul_const (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul r hf]

lemma lintegral_mul_const'' (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul'' r hf]

lemma lintegral_mul_const_le (r : ℝ≥0∞) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂μ * r ≤ ∫⁻ a, f a * r ∂μ :=
by simp_rw [mul_comm, lintegral_const_mul_le r f]

lemma lintegral_mul_const' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞):
  ∫⁻ a, f a * r ∂μ = ∫⁻ a, f a ∂μ * r :=
by simp_rw [mul_comm, lintegral_const_mul' r f hr]

/- A double integral of a product where each factor contains only one variable
  is a product of integrals -/
lemma lintegral_lintegral_mul {β} [measurable_space β] {ν : measure β}
  {f : α → ℝ≥0∞} {g : β → ℝ≥0∞} (hf : ae_measurable f μ) (hg : ae_measurable g ν) :
  ∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ = ∫⁻ x, f x ∂μ * ∫⁻ y, g y ∂ν :=
by simp [lintegral_const_mul'' _ hg, lintegral_mul_const'' _ hf]

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₁ {f f' : α → β} (h : f =ᵐ[μ] f') (g : β → ℝ≥0∞) :
  (∫⁻ a, g (f a) ∂μ) = (∫⁻ a, g (f' a) ∂μ) :=
lintegral_congr_ae $ h.mono $ λ a h, by rw h

-- TODO: Need a better way of rewriting inside of a integral
lemma lintegral_rw₂ {f₁ f₁' : α → β} {f₂ f₂' : α → γ} (h₁ : f₁ =ᵐ[μ] f₁')
  (h₂ : f₂ =ᵐ[μ] f₂') (g : β → γ → ℝ≥0∞) :
  (∫⁻ a, g (f₁ a) (f₂ a) ∂μ) = (∫⁻ a, g (f₁' a) (f₂' a) ∂μ) :=
lintegral_congr_ae $ h₁.mp $ h₂.mono $ λ _ h₂ h₁, by rw [h₁, h₂]

@[simp] lemma lintegral_indicator (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f a ∂μ :=
begin
  simp only [lintegral, ← restrict_lintegral_eq_lintegral_restrict _ hs, supr_subtype'],
  apply le_antisymm; refine supr_le_supr2 (subtype.forall.2 $ λ φ hφ, _),
  { refine ⟨⟨φ, le_trans hφ (indicator_le_self _ _)⟩, _⟩,
    refine simple_func.lintegral_mono (λ x, _) le_rfl,
    by_cases hx : x ∈ s,
    { simp [hx, hs, le_refl] },
    { apply le_trans (hφ x),
      simp [hx, hs, le_refl] } },
  { refine ⟨⟨φ.restrict s, λ x, _⟩, le_rfl⟩,
    simp [hφ x, hs, indicator_le_indicator] }
end

lemma set_lintegral_eq_const {f : α → ℝ≥0∞} (hf : measurable f) (r : ℝ≥0∞) :
  ∫⁻ x in {x | f x = r}, f x ∂μ = r * μ {x | f x = r} :=
begin
  have : ∀ᵐ x ∂μ, x ∈ {x | f x = r} → f x = r := ae_of_all μ (λ _ hx, hx),
  rw [set_lintegral_congr_fun _ this],
  dsimp,
  rw [lintegral_const, measure.restrict_apply measurable_set.univ, set.univ_inter],
  exact hf (measurable_set_singleton r)
end

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
lemma mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : measurable f) (ε : ℝ≥0∞) :
  ε * μ {x | ε ≤ f x} ≤ ∫⁻ a, f a ∂μ :=
begin
  have : measurable_set {a : α | ε ≤ f a }, from hf measurable_set_Ici,
  rw [← simple_func.restrict_const_lintegral _ this, ← simple_func.lintegral_eq_lintegral],
  refine lintegral_mono (λ a, _),
  simp only [restrict_apply _ this],
  exact indicator_apply_le id
end

lemma lintegral_eq_top_of_measure_eq_top_pos {f : α → ℝ≥0∞} (hf : measurable f)
  (hμf : 0 < μ {x | f x = ∞}) : ∫⁻ x, f x ∂μ = ∞ :=
eq_top_iff.mpr $
calc ∞ = ∞ * μ {x | ∞ ≤ f x} : by simp [mul_eq_top, hμf.ne.symm]
   ... ≤ ∫⁻ x, f x ∂μ : mul_meas_ge_le_lintegral hf ∞

lemma meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : measurable f) {ε : ℝ≥0∞}
  (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
  μ {x | ε ≤ f x} ≤ (∫⁻ a, f a ∂μ) / ε :=
(ennreal.le_div_iff_mul_le (or.inl hε) (or.inl hε')).2 $
by { rw [mul_comm], exact mul_meas_ge_le_lintegral hf ε }

@[simp] lemma lintegral_eq_zero_iff {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂μ = 0 ↔ (f =ᵐ[μ] 0) :=
begin
  refine iff.intro (assume h, _) (assume h, _),
  { have : ∀n:ℕ, ∀ᵐ a ∂μ, f a < n⁻¹,
    { assume n,
      rw [ae_iff, ← nonpos_iff_eq_zero, ← @ennreal.zero_div n⁻¹,
        ennreal.le_div_iff_mul_le, mul_comm],
      simp only [not_lt],
      -- TODO: why `rw ← h` fails with "not an equality or an iff"?
      exacts [h ▸ mul_meas_ge_le_lintegral hf n⁻¹,
        or.inl (ennreal.inv_ne_zero.2 ennreal.coe_nat_ne_top),
        or.inr ennreal.zero_ne_top] },
    refine (ae_all_iff.2 this).mono (λ a ha, _),
    by_contradiction h,
    rcases ennreal.exists_inv_nat_lt h with ⟨n, hn⟩,
    exact (lt_irrefl _ $ lt_trans hn $ ha n).elim },
  { calc ∫⁻ a, f a ∂μ = ∫⁻ a, 0 ∂μ : lintegral_congr_ae h
      ... = 0 : lintegral_zero }
end

@[simp] lemma lintegral_eq_zero_iff' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) :
  ∫⁻ a, f a ∂μ = 0 ↔ (f =ᵐ[μ] 0) :=
begin
  have : ∫⁻ a, f a ∂μ = ∫⁻ a, hf.mk f a ∂μ := lintegral_congr_ae hf.ae_eq_mk,
  rw [this, lintegral_eq_zero_iff hf.measurable_mk],
  exact ⟨λ H, hf.ae_eq_mk.trans H, λ H, hf.ae_eq_mk.symm.trans H⟩
end

lemma lintegral_pos_iff_support {f : α → ℝ≥0∞} (hf : measurable f) :
  0 < ∫⁻ a, f a ∂μ ↔ 0 < μ (function.support f) :=
by simp [pos_iff_ne_zero, hf, filter.eventually_eq, ae_iff, function.support]

/-- Weaker version of the monotone convergence theorem-/
lemma lintegral_supr_ae {f : ℕ → α → ℝ≥0∞} (hf : ∀n, measurable (f n))
  (h_mono : ∀n, ∀ᵐ a ∂μ, f n a ≤ f n.succ a) :
  (∫⁻ a, ⨆n, f n a ∂μ) = (⨆n, ∫⁻ a, f n a ∂μ) :=
let ⟨s, hs⟩ := exists_measurable_superset_of_null
                       (ae_iff.1 (ae_all_iff.2 h_mono)) in
let g := λ n a, if a ∈ s then 0 else f n a in
have g_eq_f : ∀ᵐ a ∂μ, ∀n, g n a = f n a,
  from (measure_zero_iff_ae_nmem.1 hs.2.2).mono (assume a ha n, if_neg ha),
calc
  ∫⁻ a, ⨆n, f n a ∂μ = ∫⁻ a, ⨆n, g n a ∂μ :
  lintegral_congr_ae $ g_eq_f.mono $ λ a ha, by simp only [ha]
  ... = ⨆n, (∫⁻ a, g n a ∂μ) :
  lintegral_supr
    (assume n, measurable_const.piecewise hs.2.1 (hf n))
    (monotone_nat_of_le_succ $ assume n a, classical.by_cases
      (assume h : a ∈ s, by simp [g, if_pos h])
      (assume h : a ∉ s,
      begin
        simp only [g, if_neg h], have := hs.1, rw subset_def at this, have := mt (this a) h,
        simp only [not_not, mem_set_of_eq] at this, exact this n
      end))
  ... = ⨆n, (∫⁻ a, f n a ∂μ) :
    by simp only [lintegral_congr_ae (g_eq_f.mono $ λ a ha, ha _)]

lemma lintegral_sub {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g)
  (hg_fin : ∫⁻ a, g a ∂μ ≠ ∞) (h_le : g ≤ᵐ[μ] f) :
  ∫⁻ a, f a - g a ∂μ = ∫⁻ a, f a ∂μ - ∫⁻ a, g a ∂μ :=
begin
  rw [← ennreal.add_left_inj hg_fin,
        tsub_add_cancel_of_le (lintegral_mono_ae h_le),
      ← lintegral_add (hf.sub hg) hg],
  refine lintegral_congr_ae (h_le.mono $ λ x hx, _),
  exact tsub_add_cancel_of_le hx
end

lemma lintegral_sub_le (f g : α → ℝ≥0∞)
  (hf : measurable f) (hg : measurable g) (h : f ≤ᵐ[μ] g) :
  ∫⁻ x, g x ∂μ - ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x - f x ∂μ :=
begin
  by_cases hfi : ∫⁻ x, f x ∂μ = ∞,
  { rw [hfi, ennreal.sub_top],
    exact bot_le },
  { rw lintegral_sub hg hf hfi h,
    refl' }
end

lemma lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g)
  {s : set α} (hμs : μ s ≠ 0) (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) :
  ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
begin
  rw [← tsub_pos_iff_lt, ← lintegral_sub hg hf hfi h_le],
  by_contra hnlt,
  rw [not_lt, nonpos_iff_eq_zero, lintegral_eq_zero_iff (hg.sub hf), filter.eventually_eq] at hnlt,
  simp only [ae_iff, tsub_eq_zero_iff_le, pi.zero_apply, not_lt, not_le] at hnlt h,
  refine hμs _,
  push_neg at h,
  have hs_eq : s = {a : α | a ∈ s ∧ g a ≤ f a} ∪ {a : α | a ∈ s ∧ f a < g a},
  { ext1 x,
    simp_rw [set.mem_union, set.mem_set_of_eq, ← not_le],
    tauto, },
  rw hs_eq,
  refine measure_union_null h (measure_mono_null _ hnlt),
  simp,
end

lemma lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0)
  (hf : measurable f) (hg : measurable g) (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) :
  ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
begin
  rw [ne.def, ← measure.measure_univ_eq_zero] at hμ,
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hf hg hfi (ae_le_of_ae_lt h) hμ _,
  simpa using h,
end

lemma set_lintegral_strict_mono {f g : α → ℝ≥0∞} {s : set α}
  (hsm : measurable_set s) (hs : μ s ≠ 0) (hf : measurable f) (hg : measurable g)
  (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) :
  ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
lintegral_strict_mono (by simp [hs]) hf hg hfi ((ae_restrict_iff' hsm).mpr h)

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi_ae
  {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n))
  (h_mono : ∀n:ℕ, f n.succ ≤ᵐ[μ] f n) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
  ∫⁻ a, ⨅n, f n a ∂μ = ⨅n, ∫⁻ a, f n a ∂μ :=
have fn_le_f0 : ∫⁻ a, ⨅n, f n a ∂μ ≤ ∫⁻ a, f 0 a ∂μ, from
  lintegral_mono (assume a, infi_le_of_le 0 le_rfl),
have fn_le_f0' : (⨅n, ∫⁻ a, f n a ∂μ) ≤ ∫⁻ a, f 0 a ∂μ, from infi_le_of_le 0 le_rfl,
(ennreal.sub_right_inj h_fin fn_le_f0 fn_le_f0').1 $
show ∫⁻ a, f 0 a ∂μ - ∫⁻ a, ⨅n, f n a ∂μ = ∫⁻ a, f 0 a ∂μ - (⨅n, ∫⁻ a, f n a ∂μ), from
calc
  ∫⁻ a, f 0 a ∂μ - (∫⁻ a, ⨅n, f n a ∂μ) = ∫⁻ a, f 0 a - ⨅n, f n a ∂μ:
    (lintegral_sub (h_meas 0) (measurable_infi h_meas)
    (ne_top_of_le_ne_top h_fin $ lintegral_mono (assume a, infi_le _ _))
    (ae_of_all _ $ assume a, infi_le _ _)).symm
  ... = ∫⁻ a, ⨆n, f 0 a - f n a ∂μ : congr rfl (funext (assume a, ennreal.sub_infi))
  ... = ⨆n, ∫⁻ a, f 0 a - f n a ∂μ :
    lintegral_supr_ae
      (assume n, (h_meas 0).sub (h_meas n))
      (assume n, (h_mono n).mono $ assume a ha, tsub_le_tsub le_rfl ha)
  ... = ⨆n, ∫⁻ a, f 0 a ∂μ - ∫⁻ a, f n a ∂μ :
    have h_mono : ∀ᵐ a ∂μ, ∀n:ℕ, f n.succ a ≤ f n a := ae_all_iff.2 h_mono,
    have h_mono : ∀n, ∀ᵐ a ∂μ, f n a ≤ f 0 a := assume n, h_mono.mono $ assume a h,
    begin
      induction n with n ih,
      {exact le_rfl}, {exact le_trans (h n) ih}
    end,
    congr_arg supr $ funext $ assume n, lintegral_sub (h_meas _) (h_meas _)
      (ne_top_of_le_ne_top h_fin $ lintegral_mono_ae $ h_mono n) (h_mono n)
  ... = ∫⁻ a, f 0 a ∂μ - ⨅n, ∫⁻ a, f n a ∂μ : ennreal.sub_infi.symm

/-- Monotone convergence theorem for nonincreasing sequences of functions -/
lemma lintegral_infi
  {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n))
  (h_anti : antitone f) (h_fin : ∫⁻ a, f 0 a ∂μ ≠ ∞) :
  ∫⁻ a, ⨅n, f n a ∂μ = ⨅n, ∫⁻ a, f n a ∂μ :=
lintegral_infi_ae h_meas (λ n, ae_of_all _ $ h_anti n.le_succ) h_fin

/-- Known as Fatou's lemma, version with `ae_measurable` functions -/
lemma lintegral_liminf_le' {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, ae_measurable (f n) μ) :
  ∫⁻ a, liminf at_top (λ n, f n a) ∂μ ≤ liminf at_top (λ n, ∫⁻ a, f n a ∂μ) :=
calc
  ∫⁻ a, liminf at_top (λ n, f n a) ∂μ = ∫⁻ a, ⨆n:ℕ, ⨅i≥n, f i a ∂μ :
     by simp only [liminf_eq_supr_infi_of_nat]
  ... = ⨆n:ℕ, ∫⁻ a, ⨅i≥n, f i a ∂μ :
    lintegral_supr'
      (assume n, ae_measurable_binfi _ (countable_encodable _) h_meas)
      (ae_of_all μ (assume a n m hnm, infi_le_infi_of_subset $ λ i hi, le_trans hnm hi))
  ... ≤ ⨆n:ℕ, ⨅i≥n, ∫⁻ a, f i a ∂μ :
    supr_le_supr $ λ n, le_infi2_lintegral _
  ... = at_top.liminf (λ n, ∫⁻ a, f n a ∂μ) : filter.liminf_eq_supr_infi_of_nat.symm

/-- Known as Fatou's lemma -/
lemma lintegral_liminf_le {f : ℕ → α → ℝ≥0∞} (h_meas : ∀n, measurable (f n)) :
  ∫⁻ a, liminf at_top (λ n, f n a) ∂μ ≤ liminf at_top (λ n, ∫⁻ a, f n a ∂μ) :=
lintegral_liminf_le' (λ n, (h_meas n).ae_measurable)

lemma limsup_lintegral_le {f : ℕ → α → ℝ≥0∞} {g : α → ℝ≥0∞}
  (hf_meas : ∀ n, measurable (f n)) (h_bound : ∀n, f n ≤ᵐ[μ] g) (h_fin : ∫⁻ a, g a ∂μ ≠ ∞) :
  limsup at_top (λn, ∫⁻ a, f n a ∂μ) ≤ ∫⁻ a, limsup at_top (λn, f n a) ∂μ :=
calc
  limsup at_top (λn, ∫⁻ a, f n a ∂μ) = ⨅n:ℕ, ⨆i≥n, ∫⁻ a, f i a ∂μ :
    limsup_eq_infi_supr_of_nat
  ... ≤ ⨅n:ℕ, ∫⁻ a, ⨆i≥n, f i a ∂μ :
    infi_le_infi $ assume n, supr2_lintegral_le _
  ... = ∫⁻ a, ⨅n:ℕ, ⨆i≥n, f i a ∂μ :
    begin
      refine (lintegral_infi _ _ _).symm,
      { assume n, exact measurable_bsupr _ (countable_encodable _) hf_meas },
      { assume n m hnm a, exact (supr_le_supr_of_subset $ λ i hi, le_trans hnm hi) },
      { refine ne_top_of_le_ne_top h_fin (lintegral_mono_ae _),
        refine (ae_all_iff.2 h_bound).mono (λ n hn, _),
        exact supr_le (λ i, supr_le $ λ hi, hn i) }
    end
  ... = ∫⁻ a, limsup at_top (λn, f n a) ∂μ :
    by simp only [limsup_eq_infi_supr_of_nat]

/-- Dominated convergence theorem for nonnegative functions -/
lemma tendsto_lintegral_of_dominated_convergence
  {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀n, measurable (F n)) (h_bound : ∀n, F n ≤ᵐ[μ] bound)
  (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) at_top (𝓝 (∫⁻ a, f a ∂μ)) :=
tendsto_of_le_liminf_of_limsup_le
(calc ∫⁻ a, f a ∂μ = ∫⁻ a, liminf at_top (λ (n : ℕ), F n a) ∂μ :
      lintegral_congr_ae $ h_lim.mono $ assume a h, h.liminf_eq.symm
 ... ≤ liminf at_top (λ n, ∫⁻ a, F n a ∂μ) : lintegral_liminf_le hF_meas)
(calc limsup at_top (λ (n : ℕ), ∫⁻ a, F n a ∂μ) ≤ ∫⁻ a, limsup at_top (λn, F n a) ∂μ :
      limsup_lintegral_le hF_meas h_bound h_fin
 ... = ∫⁻ a, f a ∂μ : lintegral_congr_ae $ h_lim.mono $ λ a h, h.limsup_eq)

/-- Dominated convergence theorem for nonnegative functions which are just almost everywhere
measurable. -/
lemma tendsto_lintegral_of_dominated_convergence'
  {F : ℕ → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀n, ae_measurable (F n) μ) (h_bound : ∀n, F n ≤ᵐ[μ] bound)
  (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) at_top (𝓝 (∫⁻ a, f a ∂μ)) :=
begin
  have : ∀ n, ∫⁻ a, F n a ∂μ = ∫⁻ a, (hF_meas n).mk (F n) a ∂μ :=
    λ n, lintegral_congr_ae (hF_meas n).ae_eq_mk,
  simp_rw this,
  apply tendsto_lintegral_of_dominated_convergence bound (λ n, (hF_meas n).measurable_mk) _ h_fin,
  { have : ∀ n, ∀ᵐ a ∂μ, (hF_meas n).mk (F n) a = F n a :=
      λ n, (hF_meas n).ae_eq_mk.symm,
    have : ∀ᵐ a ∂μ, ∀ n, (hF_meas n).mk (F n) a = F n a := ae_all_iff.mpr this,
    filter_upwards [this, h_lim] with a H H',
    simp_rw H,
    exact H', },
  { assume n,
    filter_upwards [h_bound n, (hF_meas n).ae_eq_mk] with a H H',
    rwa H' at H, },
end

/-- Dominated convergence theorem for filters with a countable basis -/
lemma tendsto_lintegral_filter_of_dominated_convergence {ι} {l : filter ι}
  [l.is_countably_generated]
  {F : ι → α → ℝ≥0∞} {f : α → ℝ≥0∞} (bound : α → ℝ≥0∞)
  (hF_meas : ∀ᶠ n in l, measurable (F n))
  (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, F n a ≤ bound a)
  (h_fin : ∫⁻ a, bound a ∂μ ≠ ∞)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) l (𝓝 (f a))) :
  tendsto (λn, ∫⁻ a, F n a ∂μ) l (𝓝 $ ∫⁻ a, f a ∂μ) :=
begin
  rw tendsto_iff_seq_tendsto,
  intros x xl,
  have hxl, { rw tendsto_at_top' at xl, exact xl },
  have h := inter_mem hF_meas h_bound,
  replace h := hxl _ h,
  rcases h with ⟨k, h⟩,
  rw ← tendsto_add_at_top_iff_nat k,
  refine tendsto_lintegral_of_dominated_convergence _ _ _ _ _,
  { exact bound },
  { intro, refine (h _ _).1, exact nat.le_add_left _ _ },
  { intro, refine (h _ _).2, exact nat.le_add_left _ _ },
  { assumption },
  { refine h_lim.mono (λ a h_lim, _),
    apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
    { assumption },
    rw tendsto_add_at_top_iff_nat,
    assumption }
end

section
open encodable

/-- Monotone convergence for a suprema over a directed family and indexed by an encodable type -/
theorem lintegral_supr_directed [encodable β] {f : β → α → ℝ≥0∞}
  (hf : ∀b, measurable (f b)) (h_directed : directed (≤) f) :
  ∫⁻ a, ⨆b, f b a ∂μ = ⨆b, ∫⁻ a, f b a ∂μ :=
begin
  casesI is_empty_or_nonempty β, { simp [supr_of_empty] },
  inhabit β,
  have : ∀a, (⨆ b, f b a) = (⨆ n, f (h_directed.sequence f n) a),
  { assume a,
    refine le_antisymm (supr_le $ assume b, _) (supr_le $ assume n, le_supr (λn, f n a) _),
    exact le_supr_of_le (encode b + 1) (h_directed.le_sequence b a) },
  calc ∫⁻ a, ⨆ b, f b a ∂μ = ∫⁻ a, ⨆ n, f (h_directed.sequence f n) a ∂μ :
      by simp only [this]
    ... = ⨆ n, ∫⁻ a, f (h_directed.sequence f n) a ∂μ :
      lintegral_supr (assume n, hf _) h_directed.sequence_mono
    ... = ⨆ b, ∫⁻ a, f b a ∂μ :
    begin
      refine le_antisymm (supr_le $ assume n, _) (supr_le $ assume b, _),
      { exact le_supr (λb, ∫⁻ a, f b a ∂μ) _ },
      { exact le_supr_of_le (encode b + 1)
          (lintegral_mono $ h_directed.le_sequence b) }
    end
end

end

lemma lintegral_tsum [encodable β] {f : β → α → ℝ≥0∞} (hf : ∀i, measurable (f i)) :
  ∫⁻ a, ∑' i, f i a ∂μ = ∑' i, ∫⁻ a, f i a ∂μ :=
begin
  simp only [ennreal.tsum_eq_supr_sum],
  rw [lintegral_supr_directed],
  { simp [lintegral_finset_sum _ (λ i _, hf i)] },
  { assume b, exact finset.measurable_sum _ (λ i _, hf i) },
  { assume s t,
    use [s ∪ t],
    split,
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_left _ _),
    exact assume a, finset.sum_le_sum_of_subset (finset.subset_union_right _ _) }
end

open measure

lemma lintegral_Union [encodable β] {s : β → set α} (hm : ∀ i, measurable_set (s i))
  (hd : pairwise (disjoint on s)) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ = ∑' i, ∫⁻ a in s i, f a ∂μ :=
by simp only [measure.restrict_Union hd hm, lintegral_sum_measure]

lemma lintegral_Union_le [encodable β] (s : β → set α) (f : α → ℝ≥0∞) :
  ∫⁻ a in ⋃ i, s i, f a ∂μ ≤ ∑' i, ∫⁻ a in s i, f a ∂μ :=
begin
  rw [← lintegral_sum_measure],
  exact lintegral_mono' restrict_Union_le le_rfl
end

lemma lintegral_union {f : α → ℝ≥0∞} {A B : set α}
  (hA : measurable_set A) (hB : measurable_set B) (hAB : disjoint A B) :
  ∫⁻ a in A ∪ B, f a ∂μ = ∫⁻ a in A, f a ∂μ + ∫⁻ a in B, f a ∂μ :=
begin
  rw [set.union_eq_Union, lintegral_Union, tsum_bool, add_comm],
  { simp only [to_bool_false_eq_ff, to_bool_true_eq_tt, cond] },
  { intros i, exact measurable_set.cond hA hB },
  { rwa pairwise_disjoint_on_bool }
end

lemma lintegral_add_compl (f : α → ℝ≥0∞) {A : set α} (hA : measurable_set A) :
  ∫⁻ x in A, f x ∂μ + ∫⁻ x in Aᶜ, f x ∂μ = ∫⁻ x, f x ∂μ :=
by rw [← lintegral_add_measure, measure.restrict_add_restrict_compl hA]

lemma lintegral_map {mβ : measurable_space β} {f : β → ℝ≥0∞} {g : α → β}
  (hf : measurable f) (hg : measurable g) : ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
begin
  simp only [lintegral_eq_supr_eapprox_lintegral, hf, hf.comp hg],
  congr' with n : 1,
  convert simple_func.lintegral_map _ hg,
  ext1 x, simp only [eapprox_comp hf hg, coe_comp]
end

lemma lintegral_map' {mβ : measurable_space β} {f : β → ℝ≥0∞} {g : α → β}
  (hf : ae_measurable f (measure.map g μ)) (hg : measurable g) :
  ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, f (g a) ∂μ :=
calc ∫⁻ a, f a ∂(measure.map g μ) = ∫⁻ a, hf.mk f a ∂(measure.map g μ) :
  lintegral_congr_ae hf.ae_eq_mk
... = ∫⁻ a, hf.mk f (g a) ∂μ : lintegral_map hf.measurable_mk hg
... = ∫⁻ a, f (g a) ∂μ : lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

lemma lintegral_map_le {mβ : measurable_space β} (f : β → ℝ≥0∞) {g : α → β} (hg : measurable g) :
  ∫⁻ a, f a ∂(measure.map g μ) ≤ ∫⁻ a, f (g a) ∂μ :=
begin
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral],
  refine bsupr_le (λ i hi, supr_le (λ h'i, _)),
  refine le_supr_of_le (i ∘ g) (le_supr_of_le (hi.comp hg) _),
  exact le_supr_of_le (λ x, h'i (g x)) (le_of_eq (lintegral_map hi hg))
end

lemma lintegral_comp [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  (hf : measurable f) (hg : measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂(map g μ) :=
(lintegral_map hf hg).symm

lemma set_lintegral_map [measurable_space β] {f : β → ℝ≥0∞} {g : α → β}
  {s : set β} (hs : measurable_set s) (hf : measurable f) (hg : measurable g) :
  ∫⁻ y in s, f y ∂(map g μ) = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ :=
by rw [restrict_map hg hs, lintegral_map hf hg]

/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` wich
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
lemma _root_.measurable_embedding.lintegral_map [measurable_space β] {g : α → β}
  (hg : measurable_embedding g) (f : β → ℝ≥0∞) :
  ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
begin
  rw [lintegral, lintegral],
  refine le_antisymm (bsupr_le $ λ f₀ hf₀, _) (bsupr_le $ λ f₀ hf₀, _),
  { rw [simple_func.lintegral_map _ hg.measurable],
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g, from λ x, hf₀ (g x),
    exact le_supr_of_le (comp f₀ g hg.measurable) (le_supr _ this) },
  { rw [← f₀.extend_comp_eq hg (const _ 0), ← simple_func.lintegral_map,
      ← simple_func.lintegral_eq_lintegral, ← lintegral],
    refine lintegral_mono_ae (hg.ae_map_iff.2 $ eventually_of_forall $ λ x, _),
    exact (extend_apply _ _ _ _).trans_le (hf₀ _) }
end

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
lemma lintegral_map_equiv [measurable_space β] (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
  ∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ :=
g.measurable_embedding.lintegral_map f

lemma measure_preserving.lintegral_comp {mb : measurable_space β} {ν : measure β} {g : α → β}
  (hg : measure_preserving g μ ν) {f : β → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν :=
by rw [← hg.map_eq, lintegral_map hf hg.measurable]

lemma measure_preserving.lintegral_comp_emb {mb : measurable_space β} {ν : measure β} {g : α → β}
  (hg : measure_preserving g μ ν) (hge : measurable_embedding g) (f : β → ℝ≥0∞) :
  ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν :=
by rw [← hg.map_eq, hge.lintegral_map]

lemma measure_preserving.set_lintegral_comp_preimage {mb : measurable_space β} {ν : measure β}
  {g : α → β} (hg : measure_preserving g μ ν) {s : set β} (hs : measurable_set s)
  {f : β → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν :=
by rw [← hg.map_eq, set_lintegral_map hs hf hg.measurable]

lemma measure_preserving.set_lintegral_comp_preimage_emb {mb : measurable_space β} {ν : measure β}
  {g : α → β} (hg : measure_preserving g μ ν) (hge : measurable_embedding g) (f : β → ℝ≥0∞)
  (s : set β) :
  ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν :=
by rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]

lemma measure_preserving.set_lintegral_comp_emb {mb : measurable_space β} {ν : measure β}
  {g : α → β} (hg : measure_preserving g μ ν) (hge : measurable_embedding g) (f : β → ℝ≥0∞)
  (s : set α) :
  ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν :=
by rw [← hg.set_lintegral_comp_preimage_emb hge, preimage_image_eq _ hge.injective]

section dirac_and_count
variable [measurable_space α]

lemma lintegral_dirac' (a : α) {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂(dirac a) = f a :=
by simp [lintegral_congr_ae (ae_eq_dirac' hf)]

lemma lintegral_dirac [measurable_singleton_class α] (a : α) (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂(dirac a) = f a :=
by simp [lintegral_congr_ae (ae_eq_dirac f)]

lemma lintegral_encodable {α : Type*} {m : measurable_space α} [encodable α]
  [measurable_singleton_class α] (f : α → ℝ≥0∞) (μ : measure α) :
  ∫⁻ a, f a ∂μ = ∑' a, f a * μ {a} :=
begin
  conv_lhs { rw [← sum_smul_dirac μ, lintegral_sum_measure] },
  congr' 1 with a : 1,
  rw [lintegral_smul_measure, lintegral_dirac, mul_comm],
end

lemma lintegral_count' {f : α → ℝ≥0∞} (hf : measurable f) :
  ∫⁻ a, f a ∂count = ∑' a, f a :=
begin
  rw [count, lintegral_sum_measure],
  congr,
  exact funext (λ a, lintegral_dirac' a hf),
end

lemma lintegral_count [measurable_singleton_class α] (f : α → ℝ≥0∞) :
  ∫⁻ a, f a ∂count = ∑' a, f a :=
begin
  rw [count, lintegral_sum_measure],
  congr,
  exact funext (λ a, lintegral_dirac a f),
end

end dirac_and_count

lemma ae_lt_top {f : α → ℝ≥0∞} (hf : measurable f) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
  ∀ᵐ x ∂μ, f x < ∞ :=
begin
  simp_rw [ae_iff, ennreal.not_lt_top], by_contra h, apply h2f.lt_top.not_le,
  have : (f ⁻¹' {∞}).indicator ⊤ ≤ f,
  { intro x, by_cases hx : x ∈ f ⁻¹' {∞}; [simpa [hx], simp [hx]] },
  convert lintegral_mono this,
  rw [lintegral_indicator _ (hf (measurable_set_singleton ∞))], simp [ennreal.top_mul, preimage, h]
end

lemma ae_lt_top' {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
  ∀ᵐ x ∂μ, f x < ∞ :=
begin
  have h2f_meas : ∫⁻ x, hf.mk f x ∂μ ≠ ∞, by rwa ← lintegral_congr_ae hf.ae_eq_mk,
  exact (ae_lt_top hf.measurable_mk h2f_meas).mp (hf.ae_eq_mk.mono (λ x hx h, by rwa hx)),
end

lemma set_lintegral_lt_top_of_bdd_above
  {s : set α} (hs : μ s ≠ ∞) {f : α → ℝ≥0} (hf : measurable f) (hbdd : bdd_above (f '' s)) :
  ∫⁻ x in s, f x ∂μ < ∞ :=
begin
  obtain ⟨M, hM⟩ := hbdd,
  rw mem_upper_bounds at hM,
  refine lt_of_le_of_lt (set_lintegral_mono hf.coe_nnreal_ennreal
    (@measurable_const _ _ _ _ ↑M) _) _,
  { simpa using hM },
  { rw lintegral_const,
    refine ennreal.mul_lt_top ennreal.coe_lt_top.ne _,
    simp [hs] }
end

lemma set_lintegral_lt_top_of_is_compact [topological_space α] [opens_measurable_space α]
  {s : set α} (hs : μ s ≠ ∞) (hsc : is_compact s) {f : α → ℝ≥0} (hf : continuous f) :
  ∫⁻ x in s, f x ∂μ < ∞ :=
set_lintegral_lt_top_of_bdd_above hs hf.measurable (hsc.image hf).bdd_above

lemma _root_.is_finite_measure.lintegral_lt_top_of_bounded_to_ennreal {α : Type*}
  [measurable_space α] (μ : measure α) [μ_fin : is_finite_measure μ]
  {f : α → ℝ≥0∞} (f_bdd : ∃ c : ℝ≥0, ∀ x, f x ≤ c) : ∫⁻ x, f x ∂μ < ∞ :=
begin
  cases f_bdd with c hc,
  apply lt_of_le_of_lt (@lintegral_mono _ _ μ _ _ hc),
  rw lintegral_const,
  exact ennreal.mul_lt_top ennreal.coe_lt_top.ne μ_fin.measure_univ_lt_top.ne,
end

/-- Given a measure `μ : measure α` and a function `f : α → ℝ≥0∞`, `μ.with_density f` is the
measure such that for a measurable set `s` we have `μ.with_density f s = ∫⁻ a in s, f a ∂μ`. -/
def measure.with_density {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞) : measure α :=
measure.of_measurable (λs hs, ∫⁻ a in s, f a ∂μ) (by simp) (λ s hs hd, lintegral_Union hs hd _)

@[simp] lemma with_density_apply (f : α → ℝ≥0∞) {s : set α} (hs : measurable_set s) :
  μ.with_density f s = ∫⁻ a in s, f a ∂μ :=
measure.of_measurable_apply s hs

lemma with_density_congr_ae {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) :
  μ.with_density f = μ.with_density g :=
begin
  apply measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, with_density_apply _ hs],
  exact lintegral_congr_ae (ae_restrict_of_ae h)
end

lemma with_density_add {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  μ.with_density (f + g) = μ.with_density f + μ.with_density g :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.add_apply,
      with_density_apply _ hs, with_density_apply _ hs, ← lintegral_add hf hg],
  refl,
end

lemma with_density_smul (r : ℝ≥0∞) {f : α → ℝ≥0∞} (hf : measurable f) :
  μ.with_density (r • f) = r • μ.with_density f :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_smul, pi.smul_apply,
      with_density_apply _ hs, smul_eq_mul, ← lintegral_const_mul r hf],
  refl,
end

lemma with_density_smul' (r : ℝ≥0∞) (f : α → ℝ≥0∞) (hr : r ≠ ∞) :
  μ.with_density (r • f) = r • μ.with_density f :=
begin
  refine measure.ext (λ s hs, _),
  rw [with_density_apply _ hs, measure.coe_smul, pi.smul_apply,
      with_density_apply _ hs, smul_eq_mul, ← lintegral_const_mul' r f hr],
  refl,
end

lemma is_finite_measure_with_density {f : α → ℝ≥0∞}
  (hf : ∫⁻ a, f a ∂μ ≠ ∞) : is_finite_measure (μ.with_density f) :=
{ measure_univ_lt_top :=
    by rwa [with_density_apply _ measurable_set.univ, measure.restrict_univ, lt_top_iff_ne_top] }

lemma with_density_absolutely_continuous
  {m : measurable_space α} (μ : measure α) (f : α → ℝ≥0∞) : μ.with_density f ≪ μ :=
begin
  refine absolutely_continuous.mk (λ s hs₁ hs₂, _),
  rw with_density_apply _ hs₁,
  exact set_lintegral_measure_zero _ _ hs₂
end

@[simp]
lemma with_density_zero : μ.with_density 0 = 0 :=
begin
  ext1 s hs,
  simp [with_density_apply _ hs],
end

@[simp]
lemma with_density_one : μ.with_density 1 = μ :=
begin
  ext1 s hs,
  simp [with_density_apply _ hs],
end

lemma with_density_tsum {f : ℕ → α → ℝ≥0∞} (h : ∀ i, measurable (f i)) :
  μ.with_density (∑' n, f n) = sum (λ n, μ.with_density (f n)) :=
begin
  ext1 s hs,
  simp_rw [sum_apply _ hs, with_density_apply _ hs],
  change ∫⁻ x in s, (∑' n, f n) x ∂μ = ∑' (i : ℕ), ∫⁻ x, f i x ∂(μ.restrict s),
  rw ← lintegral_tsum h,
  refine lintegral_congr (λ x, tsum_apply (pi.summable.2 (λ _, ennreal.summable))),
end

lemma with_density_indicator {s : set α} (hs : measurable_set s) (f : α → ℝ≥0∞) :
  μ.with_density (s.indicator f) = (μ.restrict s).with_density f :=
begin
  ext1 t ht,
  rw [with_density_apply _ ht, lintegral_indicator _ hs,
      restrict_comm hs, ← with_density_apply _ ht]
end

lemma with_density_indicator_one {s : set α} (hs : measurable_set s) :
  μ.with_density (s.indicator 1) = μ.restrict s :=
by rw [with_density_indicator hs, with_density_one]

lemma with_density_of_real_mutually_singular {f : α → ℝ} (hf : measurable f) :
  μ.with_density (λ x, ennreal.of_real $ f x) ⊥ₘ μ.with_density (λ x, ennreal.of_real $ -f x) :=
begin
  set S : set α := { x | f x < 0 } with hSdef,
  have hS : measurable_set S := measurable_set_lt hf measurable_const,
  refine ⟨S, hS, _, _⟩,
  { rw [with_density_apply _ hS, lintegral_eq_zero_iff hf.ennreal_of_real, eventually_eq],
    exact (ae_restrict_mem hS).mono (λ x hx, ennreal.of_real_eq_zero.2 (le_of_lt hx)) },
  { rw [with_density_apply _ hS.compl, lintegral_eq_zero_iff hf.neg.ennreal_of_real, eventually_eq],
    exact (ae_restrict_mem hS.compl).mono (λ x hx, ennreal.of_real_eq_zero.2
      (not_lt.1 $ mt neg_pos.1 hx)) },
end

lemma restrict_with_density {s : set α} (hs : measurable_set s) (f : α → ℝ≥0∞) :
  (μ.with_density f).restrict s = (μ.restrict s).with_density f :=
begin
  ext1 t ht,
  rw [restrict_apply ht, with_density_apply _ ht,
      with_density_apply _ (ht.inter hs), restrict_restrict ht],
end

lemma with_density_eq_zero {f : α → ℝ≥0∞}
  (hf : ae_measurable f μ) (h : μ.with_density f = 0) :
  f =ᵐ[μ] 0 :=
by rw [← lintegral_eq_zero_iff' hf, ← set_lintegral_univ,
       ← with_density_apply _ measurable_set.univ, h, measure.coe_zero, pi.zero_apply]

lemma with_density_apply_eq_zero {f : α → ℝ≥0∞} {s : set α} (hf : measurable f) :
  μ.with_density f s = 0 ↔ μ ({x | f x ≠ 0} ∩ s) = 0 :=
begin
  split,
  { assume hs,
    let t := to_measurable (μ.with_density f) s,
    apply measure_mono_null
      (inter_subset_inter_right _ (subset_to_measurable (μ.with_density f) s)),
    have A : μ.with_density f t = 0, by rw [measure_to_measurable, hs],
    rw [with_density_apply f (measurable_set_to_measurable _ s), lintegral_eq_zero_iff hf,
        eventually_eq, ae_restrict_iff, ae_iff] at A,
    swap, { exact hf (measurable_set_singleton 0) },
    simp only [pi.zero_apply, mem_set_of_eq, filter.mem_mk] at A,
    convert A,
    ext x,
    simp only [and_comm, exists_prop, mem_inter_eq, iff_self, mem_set_of_eq, mem_compl_eq,
               not_forall] },
  { assume hs,
    let t := to_measurable μ ({x | f x ≠ 0} ∩ s),
    have A : s ⊆ t ∪ {x | f x = 0},
    { assume x hx,
      rcases eq_or_ne (f x) 0 with fx|fx,
      { simp only [fx, mem_union_eq, mem_set_of_eq, eq_self_iff_true, or_true] },
      { left,
        apply subset_to_measurable _ _,
        exact ⟨fx, hx⟩ } },
    apply measure_mono_null A (measure_union_null _ _),
    { apply with_density_absolutely_continuous,
      rwa measure_to_measurable },
    { have M : measurable_set {x : α | f x = 0} := hf (measurable_set_singleton _),
      rw [with_density_apply _ M, (lintegral_eq_zero_iff hf)],
      filter_upwards [ae_restrict_mem M],
      simp only [imp_self, pi.zero_apply, implies_true_iff] } }
end

lemma ae_with_density_iff {p : α → Prop} {f : α → ℝ≥0∞} (hf : measurable f) :
  (∀ᵐ x ∂(μ.with_density f), p x) ↔ ∀ᵐ x ∂μ, f x ≠ 0 → p x :=
begin
  rw [ae_iff, ae_iff, with_density_apply_eq_zero hf],
  congr',
  ext x,
  simp only [exists_prop, mem_inter_eq, iff_self, mem_set_of_eq, not_forall],
end

lemma ae_with_density_iff_ae_restrict {p : α → Prop} {f : α → ℝ≥0∞} (hf : measurable f) :
  (∀ᵐ x ∂(μ.with_density f), p x) ↔ (∀ᵐ x ∂(μ.restrict {x | f x ≠ 0}), p x) :=
begin
  rw [ae_with_density_iff hf, ae_restrict_iff'],
  { refl },
  { exact hf (measurable_set_singleton 0).compl },
end

lemma ae_measurable_with_density_iff {E : Type*} [normed_group E] [normed_space ℝ E]
  [topological_space.second_countable_topology E] [measurable_space E] [borel_space E]
  {f : α → ℝ≥0} (hf : measurable f) {g : α → E} :
  ae_measurable g (μ.with_density (λ x, (f x : ℝ≥0∞))) ↔ ae_measurable (λ x, (f x : ℝ) • g x) μ :=
begin
  split,
  { rintros ⟨g', g'meas, hg'⟩,
    have A : measurable_set {x : α | f x ≠ 0} := (hf (measurable_set_singleton 0)).compl,
    refine ⟨λ x, (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, _⟩,
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ {x | f x ≠ 0},
    { rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg',
      rw ae_restrict_iff' A,
      filter_upwards [hg'],
      assume a ha h'a,
      have : (f a : ℝ≥0∞) ≠ 0, by simpa only [ne.def, coe_eq_zero] using h'a,
      rw ha this },
    { filter_upwards [ae_restrict_mem A.compl],
      assume x hx,
      simp only [not_not, mem_set_of_eq, mem_compl_eq] at hx,
      simp [hx] } },
  { rintros ⟨g', g'meas, hg'⟩,
    refine ⟨λ x, (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.smul g'meas, _⟩,
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal],
    filter_upwards [hg'],
    assume x hx h'x,
    rw [← hx, smul_smul, _root_.inv_mul_cancel, one_smul],
    simp only [ne.def, coe_eq_zero] at h'x,
    simpa only [nnreal.coe_eq_zero, ne.def] using h'x }
end

lemma ae_measurable_with_density_ennreal_iff {f : α → ℝ≥0} (hf : measurable f) {g : α → ℝ≥0∞} :
  ae_measurable g (μ.with_density (λ x, (f x : ℝ≥0∞))) ↔
    ae_measurable (λ x, (f x : ℝ≥0∞) * g x) μ :=
begin
  split,
  { rintros ⟨g', g'meas, hg'⟩,
    have A : measurable_set {x : α | f x ≠ 0} := (hf (measurable_set_singleton 0)).compl,
    refine ⟨λ x, f x * g' x, hf.coe_nnreal_ennreal.smul g'meas, _⟩,
    apply ae_of_ae_restrict_of_ae_restrict_compl {x | f x ≠ 0},
    { rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal] at hg',
      rw ae_restrict_iff' A,
      filter_upwards [hg'],
      assume a ha h'a,
      have : (f a : ℝ≥0∞) ≠ 0, by simpa only [ne.def, coe_eq_zero] using h'a,
      rw ha this },
    { filter_upwards [ae_restrict_mem A.compl],
      assume x hx,
      simp only [not_not, mem_set_of_eq, mem_compl_eq] at hx,
      simp [hx] } },
  { rintros ⟨g', g'meas, hg'⟩,
    refine ⟨λ x, (f x)⁻¹ * g' x, hf.coe_nnreal_ennreal.inv.smul g'meas, _⟩,
    rw [eventually_eq, ae_with_density_iff hf.coe_nnreal_ennreal],
    filter_upwards [hg'],
    assume x hx h'x,
    rw [← hx, ← mul_assoc, ennreal.inv_mul_cancel h'x ennreal.coe_ne_top, one_mul] }
end

end lintegral

end measure_theory

open measure_theory measure_theory.simple_func
/-- To prove something for an arbitrary measurable function into `ℝ≥0∞`, it suffices to show
that the property holds for (multiples of) characteristic functions and is closed under addition
and supremum of increasing sequences of functions.

It is possible to make the hypotheses in the induction steps a bit stronger, and such conditions
can be added once we need them (for example in `h_add` it is only necessary to consider the sum of
a simple function with a multiple of a characteristic function and that the intersection
of their images is a subset of `{0}`. -/
@[elab_as_eliminator]
theorem measurable.ennreal_induction {α} [measurable_space α] {P : (α → ℝ≥0∞) → Prop}
  (h_ind : ∀ (c : ℝ≥0∞) ⦃s⦄, measurable_set s → P (indicator s (λ _, c)))
  (h_add : ∀ ⦃f g : α → ℝ≥0∞⦄, disjoint (support f) (support g) → measurable f → measurable g →
    P f → P g → P (f + g))
  (h_supr : ∀ ⦃f : ℕ → α → ℝ≥0∞⦄ (hf : ∀n, measurable (f n)) (h_mono : monotone f)
    (hP : ∀ n, P (f n)), P (λ x, ⨆ n, f n x))
  ⦃f : α → ℝ≥0∞⦄ (hf : measurable f) : P f :=
begin
  convert h_supr (λ n, (eapprox f n).measurable) (monotone_eapprox f) _,
  { ext1 x, rw [supr_eapprox_apply f hf] },
  { exact λ n, simple_func.induction (λ c s hs, h_ind c hs)
      (λ f g hfg hf hg, h_add hfg f.measurable g.measurable hf hg) (eapprox f n) }
end

namespace measure_theory

variables {α : Type*} {m m0 : measurable_space α}

include m

/-- This is Exercise 1.2.1 from [tao2010]. It allows you to express integration of a measurable
function with respect to `(μ.with_density f)` as an integral with respect to `μ`, called the base
measure. `μ` is often the Lebesgue measure, and in this circumstance `f` is the probability density
function, and `(μ.with_density f)` represents any continuous random variable as a
probability measure, such as the uniform distribution between 0 and 1, the Gaussian distribution,
the exponential distribution, the Beta distribution, or the Cauchy distribution (see Section 2.4
of [wasserman2004]). Thus, this method shows how to one can calculate expectations, variances,
and other moments as a function of the probability density function.
 -/
lemma lintegral_with_density_eq_lintegral_mul (μ : measure α)
  {f : α → ℝ≥0∞} (h_mf : measurable f) : ∀ {g : α → ℝ≥0∞}, measurable g →
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  apply measurable.ennreal_induction,
  { intros c s h_ms,
    simp [*, mul_comm _ c, ← indicator_mul_right], },
  { intros g h h_univ h_mea_g h_mea_h h_ind_g h_ind_h,
    simp [mul_add, *, measurable.mul] },
  { intros g h_mea_g h_mono_g h_ind,
    have : monotone (λ n a, f a * g n a) := λ m n hmn x, ennreal.mul_le_mul le_rfl (h_mono_g hmn x),
    simp [lintegral_supr, ennreal.mul_supr, h_mf.mul (h_mea_g _), *] }
end

lemma set_lintegral_with_density_eq_set_lintegral_mul (μ : measure α) {f g : α → ℝ≥0∞}
  (hf : measurable f) (hg : measurable g) {s : set α} (hs : measurable_set s) :
  ∫⁻ x in s, g x ∂μ.with_density f = ∫⁻ x in s, (f * g) x ∂μ :=
by rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul _ hf hg]

/-- The Lebesgue integral of `g` with respect to the measure `μ.with_density f` coincides with
the integral of `f * g`. This version assumes that `g` is almost everywhere measurable. For a
version without conditions on `g` but requiring that `f` is almost everywhere finite, see
`lintegral_with_density_eq_lintegral_mul_non_measurable` -/
lemma lintegral_with_density_eq_lintegral_mul₀' {μ : measure α} {f : α → ℝ≥0∞}
  (hf : ae_measurable f μ) {g : α → ℝ≥0∞} (hg : ae_measurable g (μ.with_density f)) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  let f' := hf.mk f,
  have : μ.with_density f = μ.with_density f' := with_density_congr_ae hf.ae_eq_mk,
  rw this at ⊢ hg,
  let g' := hg.mk g,
  calc ∫⁻ a, g a ∂(μ.with_density f') = ∫⁻ a, g' a ∂(μ.with_density f') :
    lintegral_congr_ae hg.ae_eq_mk
  ... = ∫⁻ a, (f' * g') a ∂μ :
    lintegral_with_density_eq_lintegral_mul _ hf.measurable_mk hg.measurable_mk
  ... = ∫⁻ a, (f' * g) a ∂μ :
    begin
      apply lintegral_congr_ae,
      apply ae_of_ae_restrict_of_ae_restrict_compl {x | f' x ≠ 0},
      { have Z := hg.ae_eq_mk,
        rw [eventually_eq, ae_with_density_iff_ae_restrict hf.measurable_mk] at Z,
        filter_upwards [Z],
        assume x hx,
        simp only [hx, pi.mul_apply] },
      { have M : measurable_set {x : α | f' x ≠ 0}ᶜ :=
          (hf.measurable_mk (measurable_set_singleton 0).compl).compl,
        filter_upwards [ae_restrict_mem M],
        assume x hx,
        simp only [not_not, mem_set_of_eq, mem_compl_eq] at hx,
        simp only [hx, zero_mul, pi.mul_apply] }
    end
  ... = ∫⁻ (a : α), (f * g) a ∂μ :
    begin
      apply lintegral_congr_ae,
      filter_upwards [hf.ae_eq_mk],
      assume x hx,
      simp only [hx, pi.mul_apply],
    end
end

lemma lintegral_with_density_eq_lintegral_mul₀ {μ : measure α} {f : α → ℝ≥0∞}
  (hf : ae_measurable f μ) {g : α → ℝ≥0∞} (hg : ae_measurable g μ) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
lintegral_with_density_eq_lintegral_mul₀' hf (hg.mono' (with_density_absolutely_continuous μ f))

lemma lintegral_with_density_le_lintegral_mul (μ : measure α)
  {f : α → ℝ≥0∞} (f_meas : measurable f) (g : α → ℝ≥0∞) :
  ∫⁻ a, g a ∂(μ.with_density f) ≤ ∫⁻ a, (f * g) a ∂μ :=
begin
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral],
  refine bsupr_le (λ i i_meas, supr_le (λ hi, _)),
  have A : f * i ≤ f * g := λ x, ennreal.mul_le_mul le_rfl (hi x),
  refine le_supr_of_le (f * i) (le_supr_of_le (f_meas.mul i_meas) _),
  exact le_supr_of_le A (le_of_eq (lintegral_with_density_eq_lintegral_mul _ f_meas i_meas))
end

lemma lintegral_with_density_eq_lintegral_mul_non_measurable (μ : measure α)
  {f : α → ℝ≥0∞} (f_meas : measurable f) (hf : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  refine le_antisymm (lintegral_with_density_le_lintegral_mul μ f_meas g) _,
  rw [← supr_lintegral_measurable_le_eq_lintegral, ← supr_lintegral_measurable_le_eq_lintegral],
  refine bsupr_le (λ i i_meas, supr_le (λ hi, _)),
  have A : (λ x, (f x)⁻¹ * i x) ≤ g,
  { assume x,
    dsimp,
    rw [mul_comm, ← div_eq_mul_inv],
    exact div_le_of_le_mul' (hi x), },
  refine le_supr_of_le (λ x, (f x)⁻¹ * i x) (le_supr_of_le (f_meas.inv.mul i_meas) _),
  refine le_supr_of_le A _,
  rw lintegral_with_density_eq_lintegral_mul _ f_meas (f_meas.inv.mul i_meas),
  apply lintegral_mono_ae,
  filter_upwards [hf],
  assume x h'x,
  rcases eq_or_ne (f x) 0 with hx|hx,
  { have := hi x,
    simp only [hx, zero_mul, pi.mul_apply, nonpos_iff_eq_zero] at this,
    simp [this] },
  { apply le_of_eq _,
    dsimp,
    rw [← mul_assoc, ennreal.mul_inv_cancel hx h'x.ne, one_mul] }
end

lemma set_lintegral_with_density_eq_set_lintegral_mul_non_measurable (μ : measure α)
  {f : α → ℝ≥0∞} (f_meas : measurable f) (g : α → ℝ≥0∞)
  {s : set α} (hs : measurable_set s) (hf : ∀ᵐ x ∂(μ.restrict s), f x < ∞) :
  ∫⁻ a in s, g a ∂(μ.with_density f) = ∫⁻ a in s, (f * g) a ∂μ :=
by rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul_non_measurable _ f_meas hf]

lemma lintegral_with_density_eq_lintegral_mul_non_measurable₀ (μ : measure α)
  {f : α → ℝ≥0∞} (hf : ae_measurable f μ) (h'f : ∀ᵐ x ∂μ, f x < ∞) (g : α → ℝ≥0∞) :
  ∫⁻ a, g a ∂(μ.with_density f) = ∫⁻ a, (f * g) a ∂μ :=
begin
  let f' := hf.mk f,
  calc
  ∫⁻ a, g a ∂(μ.with_density f)
      = ∫⁻ a, g a ∂(μ.with_density f') : by rw with_density_congr_ae hf.ae_eq_mk
  ... = ∫⁻ a, (f' * g) a ∂μ :
    begin
      apply lintegral_with_density_eq_lintegral_mul_non_measurable _ hf.measurable_mk,
      filter_upwards [h'f, hf.ae_eq_mk],
      assume x hx h'x,
      rwa ← h'x,
    end
  ... = ∫⁻ a, (f * g) a ∂μ :
    begin
      apply lintegral_congr_ae,
      filter_upwards [hf.ae_eq_mk],
      assume x hx,
      simp only [hx, pi.mul_apply],
    end
end

lemma set_lintegral_with_density_eq_set_lintegral_mul_non_measurable₀ (μ : measure α)
  {f : α → ℝ≥0∞} {s : set α} (hf : ae_measurable f (μ.restrict s)) (g : α → ℝ≥0∞)
  (hs : measurable_set s) (h'f : ∀ᵐ x ∂(μ.restrict s), f x < ∞) :
  ∫⁻ a in s, g a ∂(μ.with_density f) = ∫⁻ a in s, (f * g) a ∂μ :=
by rw [restrict_with_density hs, lintegral_with_density_eq_lintegral_mul_non_measurable₀ _ hf h'f]

lemma with_density_mul (μ : measure α) {f g : α → ℝ≥0∞} (hf : measurable f) (hg : measurable g) :
  μ.with_density (f * g) = (μ.with_density f).with_density g :=
begin
  ext1 s hs,
  simp [with_density_apply _ hs, restrict_with_density hs,
        lintegral_with_density_eq_lintegral_mul _ hf hg],
end

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
lemma exists_pos_lintegral_lt_of_sigma_finite
  (μ : measure α) [sigma_finite μ] {ε : ℝ≥0∞} (ε0 : ε ≠ 0) :
  ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ measurable g ∧ (∫⁻ x, g x ∂μ < ε) :=
begin
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
  `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
   is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → set α := disjointed (spanning_sets μ),
  have : ∀ n, μ (s n) < ∞,
    from λ n, (measure_mono $ disjointed_subset _ _).trans_lt (measure_spanning_sets_lt_top μ n),
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ ∑' i, μ (s i) * δ i < ε,
    from ennreal.exists_pos_tsum_mul_lt_of_encodable ε0 _ (λ n, (this n).ne),
  set N : α → ℕ := spanning_sets_index μ,
  have hN_meas : measurable N := measurable_spanning_sets_index μ,
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanning_sets_index_singleton μ,
  refine ⟨δ ∘ N, λ x, δpos _, measurable_from_nat.comp hN_meas, _⟩,
  simpa [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas, hNs,
    lintegral_encodable, measurable_spanning_sets_index, mul_comm] using δsum,
end

lemma lintegral_trim {μ : measure α} (hm : m ≤ m0)
  {f : α → ℝ≥0∞} (hf : @measurable _ _ m _ f) :
  ∫⁻ a, f a ∂(μ.trim hm) = ∫⁻ a, f a ∂μ :=
begin
  refine @measurable.ennreal_induction α m (λ f, ∫⁻ a, f a ∂(μ.trim hm) = ∫⁻ a, f a ∂μ) _ _ _ f hf,
  { intros c s hs,
    rw [lintegral_indicator _ hs, lintegral_indicator _ (hm s hs),
      set_lintegral_const, set_lintegral_const],
    suffices h_trim_s : μ.trim hm s = μ s, by rw h_trim_s,
    exact trim_measurable_set_eq hm hs, },
  { intros f g hfg hf hg hf_prop hg_prop,
    have h_m := lintegral_add hf hg,
    have h_m0 := lintegral_add (measurable.mono hf hm le_rfl) (measurable.mono hg hm le_rfl),
    rwa [hf_prop, hg_prop, ← h_m0] at h_m, },
  { intros f hf hf_mono hf_prop,
    rw lintegral_supr hf hf_mono,
    rw lintegral_supr (λ n, measurable.mono (hf n) hm le_rfl) hf_mono,
    congr,
    exact funext (λ n, hf_prop n), },
end

lemma lintegral_trim_ae {μ : measure α} (hm : m ≤ m0)
  {f : α → ℝ≥0∞} (hf : ae_measurable f (μ.trim hm)) :
  ∫⁻ a, f a ∂(μ.trim hm) = ∫⁻ a, f a ∂μ :=
by rw [lintegral_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk),
  lintegral_congr_ae hf.ae_eq_mk, lintegral_trim hm hf.measurable_mk]

section sigma_finite

variables {E : Type*} [normed_group E] [measurable_space E]
  [opens_measurable_space E]

lemma univ_le_of_forall_fin_meas_le {μ : measure α} (hm : m ≤ m0) [@sigma_finite _ m (μ.trim hm)]
  (C : ℝ≥0∞) {f : set α → ℝ≥0∞} (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → f s ≤ C)
  (h_F_lim : ∀ S : ℕ → set α,
    (∀ n, measurable_set[m] (S n)) → monotone S → f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
  f univ ≤ C :=
begin
  let S := @spanning_sets _ m (μ.trim hm) _,
  have hS_mono : monotone S, from @monotone_spanning_sets _ m (μ.trim hm) _,
  have hS_meas : ∀ n, measurable_set[m] (S n), from @measurable_spanning_sets _ m (μ.trim hm) _,
  rw ← @Union_spanning_sets _ m (μ.trim hm),
  refine (h_F_lim S hS_meas hS_mono).trans _,
  refine supr_le (λ n, hf (S n) (hS_meas n) _),
  exact ((le_trim hm).trans_lt (@measure_spanning_sets_lt_top _ m (μ.trim hm) _ n)).ne,
end

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `ae_measurable` version. -/
lemma lintegral_le_of_forall_fin_meas_le_of_measurable {μ : measure α} (hm : m ≤ m0)
  [@sigma_finite _ m (μ.trim hm)] (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : measurable f)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) :
  ∫⁻ x, f x ∂μ ≤ C :=
begin
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ, by simp only [measure.restrict_univ],
  rw ← this,
  refine univ_le_of_forall_fin_meas_le hm C hf (λ S hS_meas hS_mono, _),
  rw ← lintegral_indicator,
  swap, { exact hm (⋃ n, S n) (@measurable_set.Union _ _ m _ _ hS_meas), },
  have h_integral_indicator : (⨆ n, ∫⁻ x in S n, f x ∂μ) = ⨆ n, ∫⁻ x, (S n).indicator f x ∂μ,
  { congr,
    ext1 n,
    rw lintegral_indicator _ (hm _ (hS_meas n)), },
  rw [h_integral_indicator,  ← lintegral_supr],
  { refine le_of_eq (lintegral_congr (λ x, _)),
    simp_rw indicator_apply,
    by_cases hx_mem : x ∈ Union S,
    { simp only [hx_mem, if_true],
      obtain ⟨n, hxn⟩ := mem_Union.mp hx_mem,
      refine le_antisymm (trans _ (le_supr _ n)) (supr_le (λ i, _)),
      { simp only [hxn, le_refl, if_true], },
      { by_cases hxi : x ∈ S i; simp [hxi], }, },
    { simp only [hx_mem, if_false],
      rw mem_Union at hx_mem,
      push_neg at hx_mem,
      refine le_antisymm (zero_le _) (supr_le (λ n, _)),
      simp only [hx_mem n, if_false, nonpos_iff_eq_zero], }, },
  { exact λ n, hf_meas.indicator (hm _ (hS_meas n)), },
  { intros n₁ n₂ hn₁₂ a,
    simp_rw indicator_apply,
    split_ifs,
    { exact le_rfl, },
    { exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1, },
    { exact zero_le _, },
    { exact le_rfl, }, },
end

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
lemma lintegral_le_of_forall_fin_meas_le' {μ : measure α} (hm : m ≤ m0)
  [@sigma_finite _ m (μ.trim hm)] (C : ℝ≥0∞) {f : _ → ℝ≥0∞} (hf_meas : ae_measurable f μ)
  (hf : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) :
  ∫⁻ x, f x ∂μ ≤ C :=
begin
  let f' := hf_meas.mk f,
  have hf' : ∀ s, measurable_set[m] s → μ s ≠ ∞ → ∫⁻ x in s, f' x ∂μ ≤ C,
  { refine λ s hs hμs, (le_of_eq _).trans (hf s hs hμs),
    refine lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono (λ x hx, _))),
    rw hx, },
  rw lintegral_congr_ae hf_meas.ae_eq_mk,
  exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf',
end

omit m

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
lemma lintegral_le_of_forall_fin_meas_le [measurable_space α] {μ : measure α} [sigma_finite μ]
  (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : ae_measurable f μ)
  (hf : ∀ s, measurable_set s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) :
  ∫⁻ x, f x ∂μ ≤ C :=
@lintegral_le_of_forall_fin_meas_le' _ _ _ _ _ (by rwa trim_eq_self) C _ hf_meas hf

/-- A sigma-finite measure is absolutely continuous with respect to some finite measure. -/
lemma exists_absolutely_continuous_is_finite_measure
  {m : measurable_space α} (μ : measure α) [sigma_finite μ] :
  ∃ (ν : measure α), is_finite_measure ν ∧ μ ≪ ν :=
begin
  obtain ⟨g, gpos, gmeas, hg⟩ : ∃ (g : α → ℝ≥0), (∀ (x : α), 0 < g x) ∧
    measurable g ∧ ∫⁻ (x : α), ↑(g x) ∂μ < 1 :=
      exists_pos_lintegral_lt_of_sigma_finite μ (ennreal.zero_lt_one).ne',
  refine ⟨μ.with_density (λ x, g x), is_finite_measure_with_density hg.ne_top, _⟩,
  have : μ = (μ.with_density (λ x, g x)).with_density (λ x, (g x)⁻¹),
  { have A : (λ (x : α), (g x : ℝ≥0∞)) * (λ (x : α), (↑(g x))⁻¹) = 1,
    { ext1 x,
      exact ennreal.mul_inv_cancel (ennreal.coe_ne_zero.2 ((gpos x).ne')) ennreal.coe_ne_top },
    rw [← with_density_mul _ gmeas.coe_nnreal_ennreal gmeas.coe_nnreal_ennreal.inv, A,
        with_density_one] },
  conv_lhs { rw this },
  exact with_density_absolutely_continuous _ _,
end

end sigma_finite

end measure_theory
