/-
  Transformation.lean
  ====================

  Level 2: Transformations (Morphisms)

  Distinction alone gives us static objects.
  Transformation gives us dynamics — the ability to move between states.

  This is the category theory insight:
  - Objects: distinguished states (Level 1)
  - Morphisms: transformations between states (Level 2)
  - Non-commutativity: [f,g] ≠ 0 (Level 3)

  Like a Rubik's cube:
  - States are objects (43 quintillion)
  - Rotations are morphisms (18 generators)
  - Non-commutativity gives the puzzle its complexity
-/

import PhysicalLoF.Foundations.Distinction

namespace PhysicalLoF.Foundations

/-! ## Level 2: Transformation -/

/-- A transformation from type A to type B -/
abbrev Transformation (A B : Type u) := A → B

/-- The identity transformation: do nothing -/
def idTransform (A : Type u) : Transformation A A := id

/-- Composition of transformations: do f then g -/
def compose {A B C : Type u}
    (f : Transformation A B) (g : Transformation B C) :
    Transformation A C := g ∘ f

/-! ## Basic Properties -/

/-- Identity is a left unit for composition -/
theorem id_compose_left {A B : Type u} (f : Transformation A B) :
    compose (idTransform A) f = f := rfl

/-- Identity is a right unit for composition -/
theorem id_compose_right {A B : Type u} (f : Transformation A B) :
    compose f (idTransform B) = f := rfl

/-- Composition is associative -/
theorem compose_assoc {A B C D : Type u}
    (f : Transformation A B) (g : Transformation B C) (h : Transformation C D) :
    compose (compose f g) h = compose f (compose g h) := rfl

/-! ## Endomorphisms (transformations A → A) -/

/-- An endomorphism is a transformation from a type to itself -/
abbrev Endomorphism (A : Type u) := Transformation A A

/-- Endomorphisms can be composed indefinitely -/
def iterateEndo {A : Type u} (f : Endomorphism A) : Nat → Endomorphism A
  | 0 => idTransform A
  | n + 1 => compose (iterateEndo f n) f

/-! ## Level 3: Non-Commutativity of Transformations -/

/--
  Two endomorphisms commute if their order doesn't matter.
  f ∘ g = g ∘ f
-/
def Commute {A : Type u} (f g : Endomorphism A) : Prop :=
  compose f g = compose g f

/--
  Two endomorphisms are non-commuting if their order DOES matter.
  [f, g] ≠ 0 in physics notation
-/
def NonCommuting {A : Type u} (f g : Endomorphism A) : Prop :=
  ¬Commute f g

/-- If f and g don't commute, they are distinguishable as functions -/
theorem noncommuting_distinguishable {A : Type u} {f g : Endomorphism A}
    (h : NonCommuting f g) : Distinguishable (compose f g) (compose g f) := by
  intro heq
  exact h heq

/-! ## The Hierarchy Theorem -/

/--
  THE HIERARCHY OF STRUCTURE:

  Level 0: Void (nothing)
  Level 1: Distinction (A ≠ B) — objects exist
  Level 2: Transformation (f : A → B) — can move between objects
  Level 3: Non-commutativity ([f,g] ≠ 0) — order matters
  Level 4: Physics (Lie algebras, gauge theory, etc.)

  Each level requires the previous:
  - Can't transform without distinct endpoints
  - Can't have [f,g] ≠ 0 without transformations
  - Can't have physics without non-commutativity
-/
theorem hierarchy_requires_distinction {A : Type u}
    (f g : Endomorphism A) (h : NonCommuting f g) :
    Distinguishable (compose f g) (compose g f) :=
  noncommuting_distinguishable h

/-! ## Example: Boolean Transformations -/

/-- NOT: the basic Boolean transformation -/
def boolNot : Endomorphism Bool := not

/-- NOT ∘ NOT = identity -/
theorem not_not_id : compose boolNot boolNot = idTransform Bool := by
  funext b
  cases b <;> rfl

end PhysicalLoF.Foundations
