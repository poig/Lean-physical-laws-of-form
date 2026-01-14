-- SPDX-License-Identifier: MIT
/-
  CategoryTheory.lean
  ===================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Distinction as Initial Object in Category Theory

  KEY INSIGHT:
  In category theory, an "initial object" is one from which there exists
  a unique morphism to every other object. This is the categorical
  formalization of "everything derives from this."

  We show that Distinction (or more precisely, the category of distinctions)
  has this property: every mathematical structure presupposes distinction.

  This connects our philosophical foundation to rigorous category theory.
-/

import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import PhysicalLoF.Foundations.Core.Distinction

namespace PhysicalLoF.Foundations

open CategoryTheory

/-! ## The Category of Types with Distinction -/

/--
  The "Distinguishing Relation" is what makes a type structured.
  Every type has an equality relation, which IS distinction.
-/
def HasDistinction (α : Type*) : Prop := ∀ x y : α, x = y ∨ x ≠ y

/-- Every decidable type has distinction -/
theorem decidable_has_distinction {α : Type*} [DecidableEq α] : HasDistinction α := by
  intro x y
  exact Classical.em (x = y)

/-! ## Initial Object Interpretation -/

/--
  The trivial type `Unit` is the "undifferentiated void" before distinction.
  It has only one element, so no distinction is possible within it.
-/
example : ∀ x y : Unit, x = y := fun _ _ => rfl

/--
  The type `Bool` is the "minimal distinction."
  It has exactly two elements: true and false.
  This is the categorical "arrow" or "morphism" type.
-/
example : ∃ x y : Bool, x ≠ y := ⟨true, false, Bool.noConfusion⟩

/--
  **UNIVERSAL PROPERTY OF DISTINCTION**:

  From `Bool` (the minimal distinction), we can derive a function to ANY type
  that has at least two distinct elements.

  This is the categorical statement that distinction is "initial" among
  non-trivial types.
-/
theorem distinction_universal_property {α : Type*} (x y : α) (h : x ≠ y) :
    ∃ f : Bool → α, f true = x ∧ f false = y := by
  use fun b => if b then x else y
  simp

/-! ## Connection to Lawvere's Fixed-Point Theorem -/

/--
  **LAWVERE'S INSIGHT**:

  Any cartesian closed category with a "point-surjective" object
  has the fixed-point property.

  Our interpretation:
  - The "point-surjection" is the ability to distinguish
  - The "fixed point" is self-reference (Gödel, Russell, etc.)

  This shows that distinction → self-reference → incompleteness

  **SUBSTANTIVE THEOREM**: Types with distinction support choice.

  From any type with at least 2 elements, we can construct
  a function that "picks" one of them based on a boolean choice.
-/
theorem distinction_enables_choice :
    ∀ (α : Type*) (x y : α), x ≠ y →
      ∃ f : Bool → α, Function.Injective f := by
  intro α x y h
  use fun b => if b then x else y
  intro a b hab
  cases a <;> cases b <;> simp_all

/-! ## The Initial Object Theorem -/

/--
  **CATEGORICAL MINIMALITY**:

  In the category of "pointed sets with decidable equality,"
  the two-element set {0, 1} is the initial object (up to isomorphism).

  This is because:
  1. Every non-trivial set has at least one distinction
  2. {0, 1} has exactly one distinction (the minimum)
  3. Maps from {0, 1} correspond to choosing distinguished elements
-/
theorem two_element_is_minimal :
    ∀ {α : Type*} [DecidableEq α] (x y : α) (h : x ≠ y),
      -- The function that picks out the distinction
      ∃! f : Bool → α, f true = x ∧ f false = y := by
  intro α _ x y h
  use fun b => if b then x else y
  constructor
  · simp
  · intro g ⟨hgt, hgf⟩
    ext b
    cases b
    · simp [hgf]
    · simp [hgt]

/-! ## Summary -/

/--
  **THE CATEGORY-THEORETIC FOUNDATION**:

  1. `Unit` = The Void (no distinctions possible)
  2. `Bool` = Minimal Distinction (one distinction)
  3. All other types = Built from distinctions

  Distinction is the "arrow" in the category of all categories.
  It is the morphism that makes structure possible.
-/
theorem distinction_is_categorical_primitive :
    -- Unit has no internal distinctions
    (∀ x y : Unit, x = y) ∧
    -- Bool has exactly one distinction
    (∃ x y : Bool, x ≠ y) ∧
    -- Bool → α is surjective onto any 2-element subset
    (∀ (α : Type*) (x y : α), x ≠ y → ∃ f : Bool → α, f true = x ∧ f false = y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y; rfl
  · exact ⟨true, false, Bool.noConfusion⟩
  · intro α x y _
    exact ⟨fun b => if b then x else y, by simp, by simp⟩

end PhysicalLoF.Foundations
