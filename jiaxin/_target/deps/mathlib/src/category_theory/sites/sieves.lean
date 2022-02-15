/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, E. W. Ayers
-/

import order.complete_lattice
import category_theory.over
import category_theory.yoneda
import category_theory.limits.shapes.pullbacks
import data.set.lattice

/-!
# Theory of sieves

- For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X`
  which is closed under left-composition.
- The complete lattice structure on sieves is given, as well as the Galois insertion
  given by downward-closing.
- A `sieve X` (functorially) induces a presheaf on `C` together with a monomorphism to
  the yoneda embedding of `X`.

## Tags

sieve, pullback
-/

universes v₁ v₂ v₃ u₁ u₂ u₃
namespace category_theory

open category limits

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D] (F : C ⥤ D)
variables {X Y Z : C} (f : Y ⟶ X)

/-- A set of arrows all with codomain `X`. -/
@[derive complete_lattice]
def presieve (X : C) := Π ⦃Y⦄, set (Y ⟶ X)

namespace presieve

instance : inhabited (presieve X) := ⟨⊤⟩

/-- Given a sieve `S` on `X : C`, its associated diagram `S.diagram` is defined to be
    the natural functor from the full subcategory of the over category `C/X` consisting
    of arrows in `S` to `C`. -/
abbreviation diagram (S : presieve X) : {f : over X // S f.hom} ⥤ C :=
full_subcategory_inclusion _ ⋙ over.forget X

/-- Given a sieve `S` on `X : C`, its associated cocone `S.cocone` is defined to be
    the natural cocone over the diagram defined above with cocone point `X`. -/
abbreviation cocone (S : presieve X) : cocone S.diagram :=
(over.forget_cocone X).whisker (full_subcategory_inclusion _)

/--
Given a set of arrows `S` all with codomain `X`, and a set of arrows with codomain `Y` for each
`f : Y ⟶ X` in `S`, produce a set of arrows with codomain `X`:
`{ g ≫ f | (f : Y ⟶ X) ∈ S, (g : Z ⟶ Y) ∈ R f }`.
-/
def bind (S : presieve X) (R : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → presieve Y) :
  presieve X :=
λ Z h, ∃ (Y : C) (g : Z ⟶ Y) (f : Y ⟶ X) (H : S f), R H g ∧ g ≫ f = h

@[simp]
lemma bind_comp {S : presieve X}
  {R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → presieve Y} {g : Z ⟶ Y} (h₁ : S f) (h₂ : R h₁ g) :
bind S R (g ≫ f) :=
⟨_, _, _, h₁, h₂, rfl⟩

/-- The singleton presieve.  -/
-- Note we can't make this into `has_singleton` because of the out-param.
inductive singleton : presieve X
| mk : singleton f

@[simp] lemma singleton_eq_iff_domain (f g : Y ⟶ X) : singleton f g ↔ f = g :=
begin
  split,
  { rintro ⟨a, rfl⟩,
    refl },
  { rintro rfl,
    apply singleton.mk, }
end

lemma singleton_self : singleton f f := singleton.mk

/--
Pullback a set of arrows with given codomain along a fixed map, by taking the pullback in the
category.
This is not the same as the arrow set of `sieve.pullback`, but there is a relation between them
in `pullback_arrows_comm`.
-/
inductive pullback_arrows [has_pullbacks C] (R : presieve X) :
  presieve Y
| mk (Z : C) (h : Z ⟶ X) : R h → pullback_arrows (pullback.snd : pullback h f ⟶ Y)

lemma pullback_singleton [has_pullbacks C] (g : Z ⟶ X) :
 pullback_arrows f (singleton g) = singleton (pullback.snd : pullback g f ⟶ _) :=
begin
  ext W h,
  split,
  { rintro ⟨W, _, _, _⟩,
    exact singleton.mk },
  { rintro ⟨_⟩,
    exact pullback_arrows.mk Z g singleton.mk }
end

/-- Construct the presieve given by the family of arrows indexed by `ι`. -/
inductive of_arrows {ι : Type*} (Y : ι → C) (f : Π i, Y i ⟶ X) : presieve X
| mk (i : ι) : of_arrows (f i)

lemma of_arrows_punit :
  of_arrows _ (λ _ : punit, f) = singleton f :=
begin
  ext Y g,
  split,
  { rintro ⟨_⟩,
    apply singleton.mk },
  { rintro ⟨_⟩,
    exact of_arrows.mk punit.star },
end

lemma of_arrows_pullback [has_pullbacks C] {ι : Type*}
  (Z : ι → C) (g : Π (i : ι), Z i ⟶ X) :
  of_arrows (λ i, pullback (g i) f) (λ i, pullback.snd) =
    pullback_arrows f (of_arrows Z g) :=
begin
  ext T h,
  split,
  { rintro ⟨hk⟩,
   exact pullback_arrows.mk _ _ (of_arrows.mk hk) },
  { rintro ⟨W, k, hk₁⟩,
    cases hk₁ with i hi,
    apply of_arrows.mk },
end

lemma of_arrows_bind {ι : Type*} (Z : ι → C) (g : Π (i : ι), Z i ⟶ X)
  (j : Π ⦃Y⦄ (f : Y ⟶ X), of_arrows Z g f → Type*)
  (W : Π ⦃Y⦄ (f : Y ⟶ X) H, j f H → C)
  (k : Π ⦃Y⦄ (f : Y ⟶ X) H i, W f H i ⟶ Y) :
  (of_arrows Z g).bind (λ Y f H, of_arrows (W f H) (k f H)) =
    of_arrows (λ (i : Σ i, j _ (of_arrows.mk i)), W (g i.1) _ i.2)
      (λ ij, k (g ij.1) _ ij.2 ≫ g ij.1) :=
begin
  ext Y f,
  split,
  { rintro ⟨_, _, _, ⟨i⟩, ⟨i'⟩, rfl⟩,
    exact of_arrows.mk (sigma.mk _ _) },
  { rintro ⟨i⟩,
    exact bind_comp _ (of_arrows.mk _) (of_arrows.mk _) }
end

/-- Given a presieve on `F(X)`, we can define a presieve on `X` by taking the preimage via `F`. -/
def functor_pullback (R : presieve (F.obj X)) : presieve X := λ _ f, R (F.map f)

@[simp] lemma functor_pullback_mem (R : presieve (F.obj X)) {Y} (f : Y ⟶ X) :
  R.functor_pullback F f ↔ R (F.map f) := iff.rfl

@[simp] lemma functor_pullback_id (R : presieve X) : R.functor_pullback (𝟭 _) = R := rfl

section functor_pushforward
variables {E : Type u₃} [category.{v₃} E] (G : D ⥤ E)

/--
Given a presieve on `X`, we can define a presieve on `F(X)` (which is actually a sieve)
by taking the sieve generated by the image via `F`.
-/
def functor_pushforward (S : presieve X) : presieve (F.obj X) :=
λ Y f, ∃ (Z : C) (g : Z ⟶ X) (h : Y ⟶ F.obj Z), S g ∧ f = h ≫ F.map g

/--
An auxillary definition in order to fix the choice of the preimages between various definitions.
-/
@[nolint has_inhabited_instance]
structure functor_pushforward_structure (S : presieve X) {Y} (f : Y ⟶ F.obj X) :=
(preobj : C) (premap : preobj ⟶ X) (lift : Y ⟶ F.obj preobj)
(cover : S premap) (fac : f = lift ≫ F.map premap)

/-- The fixed choice of a preimage. -/
noncomputable def get_functor_pushforward_structure {F : C ⥤ D} {S : presieve X} {Y : D}
  {f : Y ⟶ F.obj X} (h : S.functor_pushforward F f) : functor_pushforward_structure F S f :=
by { choose Z f' g h₁ h using h, exact ⟨Z, f', g, h₁, h⟩ }

lemma functor_pushforward_comp (R : presieve X) :
  R.functor_pushforward (F ⋙ G) = (R.functor_pushforward F).functor_pushforward G :=
begin
  ext x f,
  split,
  { rintro ⟨X, f₁, g₁, h₁, rfl⟩, exact ⟨F.obj X, F.map f₁, g₁, ⟨X, f₁, 𝟙 _, h₁, by simp⟩, rfl⟩ },
  { rintro ⟨X, f₁, g₁, ⟨X', f₂, g₂, h₁, rfl⟩, rfl⟩, use ⟨X', f₂, g₁ ≫ G.map g₂, h₁, by simp⟩ }
end

lemma image_mem_functor_pushforward (R : presieve X) {f : Y ⟶ X} (h : R f) :
  R.functor_pushforward F (F.map f) := ⟨Y, f, 𝟙 _, h, by simp⟩

end functor_pushforward
end presieve

/--
For an object `X` of a category `C`, a `sieve X` is a set of morphisms to `X` which is closed under
left-composition.
-/
structure sieve {C : Type u₁} [category.{v₁} C] (X : C) :=
(arrows : presieve X)
(downward_closed' : ∀ {Y Z f} (hf : arrows f) (g : Z ⟶ Y), arrows (g ≫ f))

namespace sieve

instance : has_coe_to_fun (sieve X) (λ _, presieve X) := ⟨sieve.arrows⟩

initialize_simps_projections sieve (arrows → apply)

variables {S R : sieve X}

@[simp, priority 100] lemma downward_closed (S : sieve X) {f : Y ⟶ X} (hf : S f)
  (g : Z ⟶ Y) : S (g ≫ f) :=
S.downward_closed' hf g

lemma arrows_ext : Π {R S : sieve X}, R.arrows = S.arrows → R = S
| ⟨Ra, _⟩ ⟨Sa, _⟩ rfl := rfl

@[ext]
protected lemma ext {R S : sieve X}
  (h : ∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) :
  R = S :=
arrows_ext $ funext $ λ x, funext $ λ f, propext $ h f

protected lemma ext_iff {R S : sieve X} :
  R = S ↔ (∀ ⦃Y⦄ (f : Y ⟶ X), R f ↔ S f) :=
⟨λ h Y f, h ▸ iff.rfl, sieve.ext⟩

open lattice

/-- The supremum of a collection of sieves: the union of them all. -/
protected def Sup (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := λ Y, {f | ∃ S ∈ 𝒮, sieve.arrows S f},
  downward_closed' := λ Y Z f, by { rintro ⟨S, hS, hf⟩ g, exact ⟨S, hS, S.downward_closed hf _⟩ } }

/-- The infimum of a collection of sieves: the intersection of them all. -/
protected def Inf (𝒮 : set (sieve X)) : (sieve X) :=
{ arrows := λ Y, {f | ∀ S ∈ 𝒮, sieve.arrows S f},
  downward_closed' := λ Y Z f hf g S H, S.downward_closed (hf S H) g }

/-- The union of two sieves is a sieve. -/
protected def union (S R : sieve X) : sieve X :=
{ arrows := λ Y f, S f ∨ R f,
  downward_closed' := by { rintros Y Z f (h | h) g; simp [h] } }

/-- The intersection of two sieves is a sieve. -/
protected def inter (S R : sieve X) : sieve X :=
{ arrows := λ Y f, S f ∧ R f,
  downward_closed' := by { rintros Y Z f ⟨h₁, h₂⟩ g, simp [h₁, h₂] } }

/--
Sieves on an object `X` form a complete lattice.
We generate this directly rather than using the galois insertion for nicer definitional properties.
-/
instance : complete_lattice (sieve X) :=
{ le           := λ S R, ∀ ⦃Y⦄ (f : Y ⟶ X), S f → R f,
  le_refl      := λ S f q, id,
  le_trans     := λ S₁ S₂ S₃ S₁₂ S₂₃ Y f h, S₂₃ _ (S₁₂ _ h),
  le_antisymm  := λ S R p q, sieve.ext (λ Y f, ⟨p _, q _⟩),
  top          := { arrows := λ _, set.univ, downward_closed' := λ Y Z f g h, ⟨⟩ },
  bot          := { arrows := λ _, ∅, downward_closed' := λ _ _ _ p _, false.elim p },
  sup          := sieve.union,
  inf          := sieve.inter,
  Sup          := sieve.Sup,
  Inf          := sieve.Inf,
  le_Sup       := λ 𝒮 S hS Y f hf, ⟨S, hS, hf⟩,
  Sup_le       := λ ℰ S hS Y f, by { rintro ⟨R, hR, hf⟩, apply hS R hR _ hf },
  Inf_le       := λ _ _ hS _ _ h, h _ hS,
  le_Inf       := λ _ _ hS _ _ hf _ hR, hS _ hR _ hf,
  le_sup_left  := λ _ _ _ _, or.inl,
  le_sup_right := λ _ _ _ _, or.inr,
  sup_le       := λ _ _ _ a b _ _ hf, hf.elim (a _) (b _),
  inf_le_left  := λ _ _ _ _, and.left,
  inf_le_right := λ _ _ _ _, and.right,
  le_inf       := λ _ _ _ p q _ _ z, ⟨p _ z, q _ z⟩,
  le_top       := λ _ _ _ _, trivial,
  bot_le       := λ _ _ _, false.elim }

/-- The maximal sieve always exists. -/
instance sieve_inhabited : inhabited (sieve X) := ⟨⊤⟩

@[simp]
lemma Inf_apply {Ss : set (sieve X)} {Y} (f : Y ⟶ X) :
  Inf Ss f ↔ ∀ (S : sieve X) (H : S ∈ Ss), S f :=
iff.rfl

@[simp]
lemma Sup_apply {Ss : set (sieve X)} {Y} (f : Y ⟶ X) :
  Sup Ss f ↔ ∃ (S : sieve X) (H : S ∈ Ss), S f :=
iff.rfl

@[simp]
lemma inter_apply {R S : sieve X} {Y} (f : Y ⟶ X) :
  (R ⊓ S) f ↔ R f ∧ S f :=
iff.rfl

@[simp]
lemma union_apply {R S : sieve X} {Y} (f : Y ⟶ X) :
  (R ⊔ S) f ↔ R f ∨ S f :=
iff.rfl

@[simp]
lemma top_apply (f : Y ⟶ X) : (⊤ : sieve X) f := trivial

/-- Generate the smallest sieve containing the given set of arrows. -/
@[simps]
def generate (R : presieve X) : sieve X :=
{ arrows := λ Z f, ∃ Y (h : Z ⟶ Y) (g : Y ⟶ X), R g ∧ h ≫ g = f,
  downward_closed' :=
  begin
    rintro Y Z _ ⟨W, g, f, hf, rfl⟩ h,
    exact ⟨_, h ≫ g, _, hf, by simp⟩,
  end }

/--
Given a presieve on `X`, and a sieve on each domain of an arrow in the presieve, we can bind to
produce a sieve on `X`.
-/
@[simps]
def bind (S : presieve X) (R : Π ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y) : sieve X :=
{ arrows := S.bind (λ Y f h, R h),
  downward_closed' :=
  begin
    rintro Y Z f ⟨W, f, h, hh, hf, rfl⟩ g,
    exact ⟨_, g ≫ f, _, hh, by simp [hf]⟩,
  end }

open order lattice

lemma sets_iff_generate (R : presieve X) (S : sieve X) :
  generate R ≤ S ↔ R ≤ S :=
⟨λ H Y g hg, H _ ⟨_, 𝟙 _, _, hg, id_comp _⟩,
 λ ss Y f,
  begin
    rintro ⟨Z, f, g, hg, rfl⟩,
    exact S.downward_closed (ss Z hg) f,
  end⟩

/-- Show that there is a galois insertion (generate, set_over). -/
def gi_generate : galois_insertion (generate : presieve X → sieve X) arrows :=
{ gc := sets_iff_generate,
  choice := λ 𝒢 _, generate 𝒢,
  choice_eq := λ _ _, rfl,
  le_l_u := λ S Y f hf, ⟨_, 𝟙 _, _, hf, id_comp _⟩ }

lemma le_generate (R : presieve X) : R ≤ generate R :=
gi_generate.gc.le_u_l R

@[simp] lemma generate_sieve (S : sieve X) : generate S = S :=
gi_generate.l_u_eq S

/-- If the identity arrow is in a sieve, the sieve is maximal. -/
lemma id_mem_iff_eq_top : S (𝟙 X) ↔ S = ⊤ :=
⟨λ h, top_unique $ λ Y f _, by simpa using downward_closed _ h f,
 λ h, h.symm ▸ trivial⟩

/-- If an arrow set contains a split epi, it generates the maximal sieve. -/
lemma generate_of_contains_split_epi {R : presieve X} (f : Y ⟶ X) [split_epi f]
  (hf : R f) : generate R = ⊤ :=
begin
  rw ← id_mem_iff_eq_top,
  exact ⟨_, section_ f, f, hf, by simp⟩,
end

@[simp]
lemma generate_of_singleton_split_epi (f : Y ⟶ X) [split_epi f] :
  generate (presieve.singleton f) = ⊤ :=
generate_of_contains_split_epi f (presieve.singleton_self _)

@[simp]
lemma generate_top : generate (⊤ : presieve X) = ⊤ :=
generate_of_contains_split_epi (𝟙 _) ⟨⟩

/-- Given a morphism `h : Y ⟶ X`, send a sieve S on X to a sieve on Y
    as the inverse image of S with `_ ≫ h`.
    That is, `sieve.pullback S h := (≫ h) '⁻¹ S`. -/
@[simps]
def pullback (h : Y ⟶ X) (S : sieve X) : sieve Y :=
{ arrows := λ Y sl, S (sl ≫ h),
  downward_closed' := λ Z W f g h, by simp [g] }

@[simp]
lemma pullback_id : S.pullback (𝟙 _) = S :=
by simp [sieve.ext_iff]

@[simp]
lemma pullback_top {f : Y ⟶ X} : (⊤ : sieve X).pullback f = ⊤ :=
top_unique (λ _ g, id)

lemma pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y} (S : sieve X) :
  S.pullback (g ≫ f) = (S.pullback f).pullback g :=
by simp [sieve.ext_iff]

@[simp]
lemma pullback_inter {f : Y ⟶ X} (S R : sieve X) :
 (S ⊓ R).pullback f = S.pullback f ⊓ R.pullback f :=
by simp [sieve.ext_iff]

lemma pullback_eq_top_iff_mem (f : Y ⟶ X) : S f ↔ S.pullback f = ⊤ :=
by rw [← id_mem_iff_eq_top, pullback_apply, id_comp]

lemma pullback_eq_top_of_mem (S : sieve X) {f : Y ⟶ X} : S f → S.pullback f = ⊤ :=
(pullback_eq_top_iff_mem f).1

/--
Push a sieve `R` on `Y` forward along an arrow `f : Y ⟶ X`: `gf : Z ⟶ X` is in the sieve if `gf`
factors through some `g : Z ⟶ Y` which is in `R`.
-/
@[simps]
def pushforward (f : Y ⟶ X) (R : sieve Y) : sieve X :=
{ arrows := λ Z gf, ∃ g, g ≫ f = gf ∧ R g,
  downward_closed' := λ Z₁ Z₂ g ⟨j, k, z⟩ h, ⟨h ≫ j, by simp [k], by simp [z]⟩ }

lemma pushforward_apply_comp {R : sieve Y} {Z : C} {g : Z ⟶ Y} (hg : R g) (f : Y ⟶ X) :
  R.pushforward f (g ≫ f) :=
⟨g, rfl, hg⟩

lemma pushforward_comp {f : Y ⟶ X} {g : Z ⟶ Y} (R : sieve Z) :
  R.pushforward (g ≫ f) = (R.pushforward g).pushforward f :=
sieve.ext (λ W h, ⟨λ ⟨f₁, hq, hf₁⟩, ⟨f₁ ≫ g, by simpa, f₁, rfl, hf₁⟩,
                   λ ⟨y, hy, z, hR, hz⟩, ⟨z, by rwa reassoc_of hR, hz⟩⟩)

lemma galois_connection (f : Y ⟶ X) : galois_connection (sieve.pushforward f) (sieve.pullback f) :=
λ S R, ⟨λ hR Z g hg, hR _ ⟨g, rfl, hg⟩, λ hS Z g ⟨h, hg, hh⟩, hg ▸ hS h hh⟩

lemma pullback_monotone (f : Y ⟶ X) : monotone (sieve.pullback f) :=
(galois_connection f).monotone_u

lemma pushforward_monotone (f : Y ⟶ X) : monotone (sieve.pushforward f) :=
(galois_connection f).monotone_l

lemma le_pushforward_pullback (f : Y ⟶ X) (R : sieve Y) :
  R ≤ (R.pushforward f).pullback f :=
(galois_connection f).le_u_l _

lemma pullback_pushforward_le (f : Y ⟶ X) (R : sieve X) :
  (R.pullback f).pushforward f ≤ R :=
(galois_connection f).l_u_le _

lemma pushforward_union {f : Y ⟶ X} (S R : sieve Y) :
  (S ⊔ R).pushforward f = S.pushforward f ⊔ R.pushforward f :=
(galois_connection f).l_sup

lemma pushforward_le_bind_of_mem (S : presieve X)
  (R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y) (f : Y ⟶ X) (h : S f) :
  (R h).pushforward f ≤ bind S R :=
begin
  rintro Z _ ⟨g, rfl, hg⟩,
  exact ⟨_, g, f, h, hg, rfl⟩,
end

lemma le_pullback_bind (S : presieve X) (R : Π ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S f → sieve Y)
  (f : Y ⟶ X) (h : S f) :
  R h ≤ (bind S R).pullback f :=
begin
  rw ← galois_connection f,
  apply pushforward_le_bind_of_mem,
end

/-- If `f` is a monomorphism, the pushforward-pullback adjunction on sieves is coreflective. -/
def galois_coinsertion_of_mono (f : Y ⟶ X) [mono f] :
  galois_coinsertion (sieve.pushforward f) (sieve.pullback f) :=
begin
  apply (galois_connection f).to_galois_coinsertion,
  rintros S Z g ⟨g₁, hf, hg₁⟩,
  rw cancel_mono f at hf,
  rwa ← hf,
end

/-- If `f` is a split epi, the pushforward-pullback adjunction on sieves is reflective. -/
def galois_insertion_of_split_epi (f : Y ⟶ X) [split_epi f] :
  galois_insertion (sieve.pushforward f) (sieve.pullback f) :=
begin
  apply (galois_connection f).to_galois_insertion,
  intros S Z g hg,
  refine ⟨g ≫ section_ f, by simpa⟩,
end

lemma pullback_arrows_comm [has_pullbacks C] {X Y : C} (f : Y ⟶ X)
  (R : presieve X) :
  sieve.generate (R.pullback_arrows f) = (sieve.generate R).pullback f :=
begin
  ext Z g,
  split,
  { rintro ⟨_, h, k, hk, rfl⟩,
    cases hk with W g hg,
    change (sieve.generate R).pullback f (h ≫ pullback.snd),
    rw [sieve.pullback_apply, assoc, ← pullback.condition, ← assoc],
    exact sieve.downward_closed _ (sieve.le_generate R W hg) (h ≫ pullback.fst)},
  { rintro ⟨W, h, k, hk, comm⟩,
    exact ⟨_, _, _, presieve.pullback_arrows.mk _ _ hk, pullback.lift_snd _ _ comm⟩ },
end

section functor
variables {E : Type u₃} [category.{v₃} E] (G : D ⥤ E)

/--
If `R` is a sieve, then the `category_theory.presieve.functor_pullback` of `R` is actually a sieve.
-/
@[simps] def functor_pullback (R : sieve (F.obj X)) : sieve X :=
{ arrows := presieve.functor_pullback F R,
  downward_closed' := λ _ _ f hf g,
  begin
    unfold presieve.functor_pullback,
    rw F.map_comp,
    exact R.downward_closed hf (F.map g),
  end }

@[simp] lemma functor_pullback_arrows (R : sieve (F.obj X)) :
  (R.functor_pullback F).arrows = R.arrows.functor_pullback F := rfl

@[simp] lemma functor_pullback_id (R : sieve X) : R.functor_pullback (𝟭 _) = R :=
by { ext, refl }

lemma functor_pullback_comp (R : sieve ((F ⋙ G).obj X)) :
  R.functor_pullback (F ⋙ G) = (R.functor_pullback G).functor_pullback F := by { ext, refl }

lemma functor_pushforward_extend_eq {R : presieve X} :
  (generate R).arrows.functor_pushforward F = R.functor_pushforward F :=
begin
  ext Y f, split,
  { rintro ⟨X', g, f', ⟨X'', g', f'', h₁, rfl⟩, rfl⟩,
    exact ⟨X'', f'', f' ≫ F.map g', h₁, by simp⟩ },
  { rintro ⟨X', g, f', h₁, h₂⟩, exact ⟨X', g, f', le_generate R _ h₁, h₂⟩ }
end

/-- The sieve generated by the image of `R` under `F`. -/
@[simps] def functor_pushforward (R : sieve X) : sieve (F.obj X) :=
{ arrows := R.arrows.functor_pushforward F,
  downward_closed' := λ Y Z f h g, by
  { obtain ⟨X, α, β, hα, rfl⟩ := h,
    exact ⟨X, α, g ≫ β, hα, by simp⟩ } }

@[simp] lemma functor_pushforward_id (R : sieve X) :
  R.functor_pushforward (𝟭 _) = R :=
begin
  ext X f,
  split,
  { intro hf,
    obtain ⟨X, g, h, hg, rfl⟩ := hf,
    exact R.downward_closed hg h, },
  { intro hf,
    exact ⟨X, f, 𝟙 _, hf, by simp⟩ }
end

lemma functor_pushforward_comp (R : sieve X) :
  R.functor_pushforward (F ⋙ G) = (R.functor_pushforward F).functor_pushforward G :=
by { ext, simpa [R.arrows.functor_pushforward_comp F G] }


lemma functor_galois_connection (X : C) :
  _root_.galois_connection
    (sieve.functor_pushforward F : sieve X → sieve (F.obj X))
    (sieve.functor_pullback F) :=
begin
  intros R S,
  split,
  { intros hle X f hf,
    apply hle,
    refine ⟨X, f, 𝟙 _, hf, _⟩,
    rw id_comp, },
  { rintros hle Y f ⟨X, g, h, hg, rfl⟩,
    apply sieve.downward_closed S,
    exact hle g hg, }
end

lemma functor_pullback_monotone (X : C) :
  monotone (sieve.functor_pullback F : sieve (F.obj X) → sieve X) :=
(functor_galois_connection F X).monotone_u

lemma functor_pushforward_monotone (X : C) :
  monotone (sieve.functor_pushforward F : sieve X → sieve (F.obj X)) :=
(functor_galois_connection F X).monotone_l

lemma le_functor_pushforward_pullback (R : sieve X) :
  R ≤ (R.functor_pushforward F).functor_pullback F :=
(functor_galois_connection F X).le_u_l _

lemma functor_pullback_pushforward_le (R : sieve (F.obj X)) :
  (R.functor_pullback F).functor_pushforward F ≤ R :=
(functor_galois_connection F X).l_u_le _

lemma functor_pushforward_union (S R : sieve X) :
  (S ⊔ R).functor_pushforward F = S.functor_pushforward F ⊔ R.functor_pushforward F :=
(functor_galois_connection F X).l_sup

lemma functor_pullback_union (S R : sieve (F.obj X)) :
  (S ⊔ R).functor_pullback F = S.functor_pullback F ⊔ R.functor_pullback F := rfl

lemma functor_pullback_inter (S R : sieve (F.obj X)) :
  (S ⊓ R).functor_pullback F = S.functor_pullback F ⊓ R.functor_pullback F := rfl

@[simp] lemma functor_pushforward_bot (F : C ⥤ D) (X : C) :
  (⊥ : sieve X).functor_pushforward F = ⊥ := (functor_galois_connection F X).l_bot

@[simp] lemma functor_pushforward_top (F : C ⥤ D) (X : C) :
  (⊤ : sieve X).functor_pushforward F = ⊤ :=
  begin
    refine (generate_sieve _).symm.trans _,
    apply generate_of_contains_split_epi (𝟙 (F.obj X)),
    refine ⟨X, 𝟙 _, 𝟙 _, trivial, by simp⟩
  end

@[simp] lemma functor_pullback_bot (F : C ⥤ D) (X : C) :
  (⊥ : sieve (F.obj X)).functor_pullback F = ⊥ := rfl

@[simp] lemma functor_pullback_top (F : C ⥤ D) (X : C) :
  (⊤ : sieve (F.obj X)).functor_pullback F = ⊤ := rfl

lemma image_mem_functor_pushforward (R : sieve X) {V} {f : V ⟶ X} (h : R f) :
  R.functor_pushforward F (F.map f) := ⟨V, f, 𝟙 _, h, by simp⟩

/-- When `F` is essentially surjective and full, the galois connection is a galois insertion. -/
def ess_surj_full_functor_galois_insertion [ess_surj F] [full F] (X : C) :
  galois_insertion
    (sieve.functor_pushforward F : sieve X → sieve (F.obj X))
    (sieve.functor_pullback F) :=
begin
  apply (functor_galois_connection F X).to_galois_insertion,
  intros S Y f hf,
  refine ⟨_, F.preimage ((F.obj_obj_preimage_iso Y).hom ≫ f), (F.obj_obj_preimage_iso Y).inv, _⟩,
  simpa using S.downward_closed hf _,
end

/-- When `F` is fully faithful, the galois connection is a galois coinsertion. -/
def fully_faithful_functor_galois_coinsertion [full F] [faithful F] (X : C) :
  galois_coinsertion
    (sieve.functor_pushforward F : sieve X → sieve (F.obj X))
    (sieve.functor_pullback F) :=
begin
  apply (functor_galois_connection F X).to_galois_coinsertion,
  rintros S Y f ⟨Z, g, h, h₁, h₂⟩,
  rw [←F.image_preimage h, ←F.map_comp] at h₂,
  rw F.map_injective h₂,
  exact S.downward_closed h₁ _,
end

end functor

/-- A sieve induces a presheaf. -/
@[simps]
def functor (S : sieve X) : Cᵒᵖ ⥤ Type v₁ :=
{ obj := λ Y, {g : Y.unop ⟶ X // S g},
  map := λ Y Z f g, ⟨f.unop ≫ g.1, downward_closed _ g.2 _⟩ }

/--
If a sieve S is contained in a sieve T, then we have a morphism of presheaves on their induced
presheaves.
-/
@[simps]
def nat_trans_of_le {S T : sieve X} (h : S ≤ T) : S.functor ⟶ T.functor :=
{ app := λ Y f, ⟨f.1, h _ f.2⟩ }.

/-- The natural inclusion from the functor induced by a sieve to the yoneda embedding. -/
@[simps]
def functor_inclusion (S : sieve X) : S.functor ⟶ yoneda.obj X :=
{ app := λ Y f, f.1 }.

lemma nat_trans_of_le_comm {S T : sieve X} (h : S ≤ T) :
  nat_trans_of_le h ≫ functor_inclusion _ = functor_inclusion _ :=
rfl

/-- The presheaf induced by a sieve is a subobject of the yoneda embedding. -/
instance functor_inclusion_is_mono : mono S.functor_inclusion :=
⟨λ Z f g h, by { ext Y y, apply congr_fun (nat_trans.congr_app h Y) y }⟩

/--
A natural transformation to a representable functor induces a sieve. This is the left inverse of
`functor_inclusion`, shown in `sieve_of_functor_inclusion`.
-/
-- TODO: Show that when `f` is mono, this is right inverse to `functor_inclusion` up to isomorphism.
@[simps]
def sieve_of_subfunctor {R} (f : R ⟶ yoneda.obj X) : sieve X :=
{ arrows := λ Y g, ∃ t, f.app (opposite.op Y) t = g,
  downward_closed' := λ Y Z _,
  begin
    rintro ⟨t, rfl⟩ g,
    refine ⟨R.map g.op t, _⟩,
    rw functor_to_types.naturality _ _ f,
    simp,
  end }

lemma sieve_of_subfunctor_functor_inclusion : sieve_of_subfunctor S.functor_inclusion = S :=
begin
  ext,
  simp only [functor_inclusion_app, sieve_of_subfunctor_apply, subtype.val_eq_coe],
  split,
  { rintro ⟨⟨f, hf⟩, rfl⟩,
    exact hf },
  { intro hf,
    exact ⟨⟨_, hf⟩, rfl⟩ }
end

instance functor_inclusion_top_is_iso : is_iso ((⊤ : sieve X).functor_inclusion) :=
⟨⟨{ app := λ Y a, ⟨a, ⟨⟩⟩ }, by tidy⟩⟩

end sieve
end category_theory
