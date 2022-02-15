
namespace dependentProd
  inductive myNat
  | O: myNat
  | S (x: myNat): myNat
  -- sigma type: dependent pair type; (confusingly dependent product)
  -- generalization of Cartesian product ×
  -- the last one's type depend on previous's value
  -- somehow like (a: α) × (x: β(a)) 
  -- the notation for the type is ∑x:α, β x
  variable α: Type
  variable β: α -> Type
  variable a: α
  variable b: β a 
  #check sigma.mk a b
  #check (sigma.mk a b).1
  #check (sigma.mk a b).2
  #reduce (sigma.mk a b).2
end dependentProd
namespace attributeTest 
  variable {α: Type*}
  def is_prefix (l₁: list α) (l₂: list α): Prop := 
    ∃ v: list α, l₁ ++ v = l₂
  infix ` <+= `:50 := is_prefix
  attribute [simp] 
  theorem list.is_prefix_refl (l: list α) : l <+= l :=
    ⟨[], by simp⟩ -- TODO ???  
end attributeTest

namespace tacticsTest 
  example: 3 = 3 :=
  begin
    generalize hypo: 3 = x, -- beta reduction in lambda?
    refl
  end
  -- example (p q r: Prop): p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := begin
  --   -- split,
  --   -- apply iff.intro
  --   constructor, -- they are interchangable
  -- end
end tacticsTest

namespace inductiveTypes1
  inductive weekday -- inductively define a type
  | monday | tuesday | wednesday | thursday | friday | saturday | sunday
  -- notice above accept only constructors
  -- how do I compose types?

  -- inductive good_Types: Type* -- hmm. something isn't correct -- you need type class?
  -- | ℕ | ℝ 

  #check weekday.sunday
  -- below functions were auto generated & protected. i.e. they are not visible even you open namespace.
  -- this is to avoid conflicts since almost every def have them.
  #check weekday.rec -- define function over type element inductively, (def) -> ((elem) -> (result))
  #check weekday.rec_on -- define function over type element inductively, (elem) -> (def) -> (result)
  #check weekday.cases_on -- only have enumerated constructors (?)

  -- recall @ prepends terms, making their type explicit
  #check rfl
  -- #check exact -- exact is not recognizable

  namespace weekday -- automatically open it
  open weekday (renaming rec -> rec)
  def number_of_day (d: weekday): nat :=
    rec 1 2 3 4 5 6 7 d

  #reduce number_of_day tuesday

  def next (d: weekday): weekday := rec tuesday wednesday thursday friday saturday sunday monday d
  def prev (d: weekday): weekday := rec sunday monday tuesday wednesday thursday friday saturday d
  #check next thursday
  end weekday
end inductiveTypes1

namespace inductiveTypes2
  #check sum ℕ ℕ 
  def func (x: ℕ ⊕ ℕ): ℕ := sum.rec (λ (t: ℕ), t) (λ (t: ℕ), t + 1) x
  #reduce func (sum.inl 3)
  #reduce func (sum.inr 3)

  #check ℕ × ℕ 
  def func2 (x: ℕ × ℕ): ℕ := (prod.fst x) * (prod.snd x)
  #reduce func2 ⟨1, 3⟩ 

  #check option ℕ 
  #check option.none
 
  inductive maybe (a: Type*)
  | none : maybe
  | some (x: a): maybe
  #check (maybe.some 3 : maybe ℕ)
  #check (maybe.none : maybe ℕ)
  inductive sum2 -- functionally equivalent to putting common data on top
  | inl (α : Type* )  (val : α) : sum2
  | inr (β : Type* ) (val : β) : sum2

  
  inductive myForall {α: Type*} (q: α -> Prop): Prop
  | intro: (Π(a: α), q a) -> myForall
  inductive myExists {α: Type*} (q: α -> Prop): Prop
  | intro: Π(a: α), q a -> myExists

    -- tactic mode hypothesis := all type that have evidence
    -- recall def. equality can be converted to Prop identity by refl.
  inductive foo: Type 
  | bar1 : ℕ -> ℕ -> foo
  | bar2 : ℕ -> ℕ -> ℕ -> foo
  def silly (x: foo) : ℕ := 
  begin
    cases x with a b c d e, exact b, exact e
  end
  
  
end inductiveTypes2


namespace wtf
  universe u
  variables {α β: Type u}
  inductive image_of (f: α -> β): β -> Type u
  | imf : Π a, image_of (f a) -- to define an element of image_of f a type, it suffice to 

  -- same thing by prop & subtype
  def isImageOf (f: α -> β) (b: β) := ∃x: α, f x = b
  def my_image_of (f: α -> β ):= {b: β // isImageOf f b}

  -- def can be used in proving as well as identies
  def pl (a: nat) (b: nat) := a + b
  example: pl 2 2 = 4 := begin
    rw pl,
  end
end wtf

namespace hidden
  class myInhabited (a: Type*) := (default: a)
  instance propIsInhabited: myInhabited Prop := ⟨true⟩
  def default (a: Type*) [s: myInhabited a]: a := s.default 
  #reduce default Prop
  -- #check (nat.no_confusion)
  def reduce_one: ℕ -> option ℕ
  | 0            := option.none
  | (nat.succ a) := option.some a
  def reduce_one_2 (x: nat) (nz: ¬ x = 0): ℕ
  
end hidden

#check (ℕ : Type 0)
namespace unconfused
  -- [imo] no_confusion is to prove two things are not same if they are different constructors of same inductive type.
  -- see https://xenaproject.wordpress.com/2018/03/24/no-confusion-over-no_confusion/
  inductive myType
  | A
  | B
  def myType_isEqual (a b: myType) : Prop := 
    myType.rec (myType.rec true false b) (myType.rec false true b) a
  theorem myType_no_confusion (u v: myType) (pe: u = v): myType_isEqual u v :=
  begin
    rw pe, cases v; unfold myType_isEqual,
  end
end unconfused

-- namespace typeuniverses
-- #check (nat: Type 0)
-- inductive myType: Type 2 | none | some: test2 -> myType
-- inductive test2: Type 2 | some: myType -> test2

-- end typeuniverses


namespace structures
  structure point2d (num_t: Type*) := mk :: (x: num_t) (y: num_t)
  #print prefix structures.point2d
  #reduce (@point2d.mk ℕ 2 3)
  #reduce (point2d.mk 2 3) -- structure argument auto marked as implicit (the compiler claims it is always derivable from constructors)
  #reduce {point2d . x := 3, y := 2} -- alt symbol
  #reduce point2d.x

  universe u
  structure point (a: Type u) := mk :: (x: a) (y : a)
  structure {v} point2 (a: Type v) := mk :: (x: a) (y: a) -- the universe variable
  def {uu} pts (x: Type uu) := x

  structure point3d (num_t: Type*) extends point2d num_t := mk :: (z: num_t)
  def p1 := (@point3d.mk ℕ (point2d.mk 1 2) 5)
  def p2 := {point3d . x := 1, y := 2, z := 3}
  #reduce p2.x -- shouldn't this equal to point3d.x .. p2 ..?

end structures


namespace someDoubts
  def 

end someDoubts