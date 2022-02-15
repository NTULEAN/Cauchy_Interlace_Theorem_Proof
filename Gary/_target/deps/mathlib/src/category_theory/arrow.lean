/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.comma

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `comma L R`,
where `L` and `R` are both the identity functor.

We also define the typeclass `has_lift`, representing a choice of a lift
of a commutative square (that is, a diagonal morphism making the two triangles commute).

## Tags

comma, arrow
-/

namespace category_theory

universes v u -- morphism levels before object levels. See note [category_theory universes].
variables {T : Type u} [category.{v} T]

section
variables (T)

/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
     squares in `T`. -/
@[derive category]
def arrow := comma.{v v v} (𝟭 T) (𝟭 T)

-- Satisfying the inhabited linter
instance arrow.inhabited [inhabited T] : inhabited (arrow T) :=
{ default := show comma (𝟭 T) (𝟭 T), from default }

end

namespace arrow

@[simp] lemma id_left (f : arrow T) : comma_morphism.left (𝟙 f) = 𝟙 (f.left) := rfl
@[simp] lemma id_right (f : arrow T) : comma_morphism.right (𝟙 f) = 𝟙 (f.right) := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps]
def mk {X Y : T} (f : X ⟶ Y) : arrow T :=
{ left := X,
  right := Y,
  hom := f }

theorem mk_injective (A B : T) :
  function.injective (arrow.mk : (A ⟶ B) → arrow T) :=
λ f g h, by { cases h, refl }

theorem mk_inj (A B : T) {f g : A ⟶ B} : arrow.mk f = arrow.mk g ↔ f = g :=
(mk_injective A B).eq_iff
instance {X Y : T} : has_coe (X ⟶ Y) (arrow T) := ⟨mk⟩

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
def hom_mk {f g : arrow T} {u : f.left ⟶ g.left} {v : f.right ⟶ g.right}
  (w : u ≫ g.hom = f.hom ≫ v) : f ⟶ g :=
{ left := u,
  right := v,
  w' := w }

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
def hom_mk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (w : u ≫ g = f ≫ v) : arrow.mk f ⟶ arrow.mk g :=
{ left := u,
  right := v,
  w' := w }

@[simp, reassoc] lemma w {f g : arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right := sq.w

-- `w_mk_left` is not needed, as it is a consequence of `w` and `mk_hom`.
@[simp, reassoc] lemma w_mk_right {f : arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) :
  sq.left ≫ g = f.hom ≫ sq.right :=
sq.w

lemma is_iso_of_iso_left_of_is_iso_right
  {f g : arrow T} (ff : f ⟶ g) [is_iso ff.left] [is_iso ff.right] : is_iso ff :=
{ out := ⟨⟨inv ff.left, inv ff.right⟩,
          by { ext; dsimp; simp only [is_iso.hom_inv_id] },
          by { ext; dsimp; simp only [is_iso.inv_hom_id] }⟩ }

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps] def iso_mk {f g : arrow T}
  (l : f.left ≅ g.left) (r : f.right ≅ g.right) (h : l.hom ≫ g.hom = f.hom ≫ r.hom) :
  f ≅ g :=
comma.iso_mk l r h

section

variables {f g : arrow T} (sq : f ⟶ g)

instance is_iso_left [is_iso sq] : is_iso sq.left :=
{ out := ⟨(inv sq).left, by simp only [← comma.comp_left, is_iso.hom_inv_id, is_iso.inv_hom_id,
    arrow.id_left, eq_self_iff_true, and_self]⟩ }

instance is_iso_right [is_iso sq] : is_iso sq.right :=
{ out := ⟨(inv sq).right, by simp only [← comma.comp_right, is_iso.hom_inv_id, is_iso.inv_hom_id,
    arrow.id_right, eq_self_iff_true, and_self]⟩ }

@[simp] lemma inv_left [is_iso sq] : (inv sq).left = inv sq.left :=
is_iso.eq_inv_of_hom_inv_id $ by rw [← comma.comp_left, is_iso.hom_inv_id, id_left]

@[simp] lemma inv_right [is_iso sq] : (inv sq).right = inv sq.right :=
is_iso.eq_inv_of_hom_inv_id $ by rw [← comma.comp_right, is_iso.hom_inv_id, id_right]

@[simp] lemma left_hom_inv_right [is_iso sq] : sq.left ≫ g.hom ≫ inv sq.right = f.hom :=
by simp only [← category.assoc, is_iso.comp_inv_eq, w]

-- simp proves this
lemma inv_left_hom_right [is_iso sq] : inv sq.left ≫ f.hom ≫ sq.right = g.hom :=
by simp only [w, is_iso.inv_comp_eq]

instance mono_left [mono sq] : mono sq.left :=
{ right_cancellation := λ Z φ ψ h, begin
    let aux : (Z ⟶ f.left) → (arrow.mk (𝟙 Z) ⟶ f) := λ φ, { left := φ, right := φ ≫ f.hom },
    show (aux φ).left = (aux ψ).left,
    congr' 1,
    rw ← cancel_mono sq,
    ext,
    { exact h },
    { simp only [comma.comp_right, category.assoc, ← arrow.w],
      simp only [← category.assoc, h], },
  end }

instance epi_right [epi sq] : epi sq.right :=
{ left_cancellation := λ Z φ ψ h, begin
    let aux : (g.right ⟶ Z) → (g ⟶ arrow.mk (𝟙 Z)) := λ φ, { right := φ, left := g.hom ≫ φ },
    show (aux φ).right = (aux ψ).right,
    congr' 1,
    rw ← cancel_epi sq,
    ext,
    { simp only [comma.comp_left, category.assoc, arrow.w_assoc, h], },
    { exact h },
  end }

end

/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp] lemma square_to_iso_invert (i : arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ arrow.mk p.hom) :
  i.hom ≫ sq.right ≫ p.inv = sq.left :=
by simpa only [category.assoc] using (iso.comp_inv_eq p).mpr ((arrow.w_mk_right sq).symm)

/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
lemma square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : arrow T) (sq : arrow.mk i.hom ⟶ p) :
  i.inv ≫ sq.left ≫ p.hom = sq.right :=
by simp only [iso.inv_hom_id_assoc, arrow.w, arrow.mk_hom]

/-- A lift of a commutative square is a diagonal morphism making the two triangles commute. -/
@[ext] structure lift_struct {f g : arrow T} (sq : f ⟶ g) :=
(lift : f.right ⟶ g.left)
(fac_left' : f.hom ≫ lift = sq.left . obviously)
(fac_right' : lift ≫ g.hom = sq.right . obviously)

restate_axiom lift_struct.fac_left'
restate_axiom lift_struct.fac_right'

instance lift_struct_inhabited {X : T} : inhabited (lift_struct (𝟙 (arrow.mk (𝟙 X)))) :=
⟨⟨𝟙 _, category.id_comp _, category.comp_id _⟩⟩

/-- `has_lift sq` says that there is some `lift_struct sq`, i.e., that it is possible to find a
    diagonal morphism making the two triangles commute. -/
class has_lift {f g : arrow T} (sq : f ⟶ g) : Prop :=
mk' :: (exists_lift : nonempty (lift_struct sq))

lemma has_lift.mk {f g : arrow T} {sq : f ⟶ g} (s : lift_struct sq) : has_lift sq :=
⟨nonempty.intro s⟩

attribute [simp, reassoc] lift_struct.fac_left lift_struct.fac_right

/-- Given `has_lift sq`, obtain a lift. -/
noncomputable def has_lift.struct {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : lift_struct sq :=
classical.choice has_lift.exists_lift

/-- If there is a lift of a commutative square `sq`, we can access it by saying `lift sq`. -/
noncomputable abbreviation lift {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : f.right ⟶ g.left :=
(has_lift.struct sq).lift

lemma lift.fac_left {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : f.hom ≫ lift sq = sq.left :=
by simp

lemma lift.fac_right {f g : arrow T} (sq : f ⟶ g) [has_lift sq] : lift sq ≫ g.hom = sq.right :=
by simp

@[simp, reassoc]
lemma lift.fac_right_of_to_mk {X Y : T} {f : arrow T} {g : X ⟶ Y} (sq : f ⟶ mk g) [has_lift sq] :
  lift sq ≫ g = sq.right :=
by simp only [←mk_hom g, lift.fac_right]

@[simp, reassoc]
lemma lift.fac_left_of_from_mk {X Y : T} {f : X ⟶ Y} {g : arrow T} (sq : mk f ⟶ g) [has_lift sq] :
  f ≫ lift sq = sq.left :=
by simp only [←mk_hom f, lift.fac_left]

@[simp, reassoc]
lemma lift_mk'_left {X Y P Q : T} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (h : u ≫ g = f ≫ v) [has_lift $ arrow.hom_mk' h] : f ≫ lift (arrow.hom_mk' h) = u :=
by simp only [←arrow.mk_hom f, lift.fac_left, arrow.hom_mk'_left]

@[simp, reassoc]
lemma lift_mk'_right {X Y P Q : T} {f : X ⟶ Y} {g : P ⟶ Q} {u : X ⟶ P} {v : Y ⟶ Q}
  (h : u ≫ g = f ≫ v) [has_lift $ arrow.hom_mk' h] : lift (arrow.hom_mk' h) ≫ g = v :=
by simp only [←arrow.mk_hom g, lift.fac_right, arrow.hom_mk'_right]

section

instance subsingleton_lift_struct_of_epi {f g : arrow T} (sq : f ⟶ g) [epi f.hom] :
  subsingleton (lift_struct sq) :=
subsingleton.intro $ λ a b, lift_struct.ext a b $ (cancel_epi f.hom).1 $ by simp

instance subsingleton_lift_struct_of_mono {f g : arrow T} (sq : f ⟶ g) [mono g.hom] :
  subsingleton (lift_struct sq) :=
subsingleton.intro $ λ a b, lift_struct.ext a b $ (cancel_mono g.hom).1 $ by simp

end

variables {C : Type u} [category.{v} C]
/-- A helper construction: given a square between `i` and `f ≫ g`, produce a square between
`i` and `g`, whose top leg uses `f`:
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
 -/
@[simps] def square_to_snd {X Y Z: C} {i : arrow C} {f : X ⟶ Y} {g : Y ⟶ Z}
  (sq : i ⟶ arrow.mk (f ≫ g)) :
  i ⟶ arrow.mk g :=
{ left := sq.left ≫ f,
  right := sq.right }

/-- The functor sending an arrow to its source. -/
@[simps] def left_func : arrow C ⥤ C := comma.fst _ _

/-- The functor sending an arrow to its target. -/
@[simps] def right_func : arrow C ⥤ C := comma.snd _ _

/-- The natural transformation from `left_func` to `right_func`, given by the arrow itself. -/
@[simps]
def left_to_right : (left_func : arrow C ⥤ C) ⟶ right_func :=
{ app := λ f, f.hom }

end arrow

namespace functor

universes v₁ v₂ u₁ u₂

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
def map_arrow (F : C ⥤ D) : arrow C ⥤ arrow D :=
{ obj := λ a,
  { left := F.obj a.left,
    right := F.obj a.right,
    hom := F.map a.hom, },
  map := λ a b f,
  { left := F.map f.left,
    right := F.map f.right,
    w' := by { have w := f.w, simp only [id_map] at w, dsimp, simp only [←F.map_comp, w], } } }

end functor

end category_theory
