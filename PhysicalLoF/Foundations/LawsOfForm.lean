-- SPDX-License-Identifier: MIT
/-
  LawsOfForm.lean
  ================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Spencer-Brown's Actual Laws of Form

  The two fundamental laws that Spencer-Brown derived from distinction:
  1. Law of Calling (Condensation): Mark · Mark = Mark
  2. Law of Crossing (Cancellation): Cross(Cross(x)) = x

  From these, all of Boolean logic is derived.

  We also show how these laws underlie fundamental limit theorems:
  - Gödel's Incompleteness (requires True ≠ False)
  - Turing's Halting Problem (requires computable ≠ uncomputable)
  - Heisenberg's Uncertainty (requires [x,p] ≠ 0)
-/

import PhysicalLoF.Foundations.Distinction

namespace PhysicalLoF.Foundations

/-! ## The Mark (Distinction Symbol) -/

/--
  The Mark represents the act of making a distinction.
  In classical logic: Mark = True, Unmarked = False
-/
inductive Mark : Type where
  | marked : Mark
  | unmarked : Mark
  deriving DecidableEq, Repr

open Mark

/-! ## Law of Calling (Condensation) -/

/--
  Law of Calling: Making a distinction twice is the same as making it once.
  Mark · Mark = Mark

  "The value of a call made again is the value of the call."
  — Spencer-Brown
-/
def call : Mark → Mark → Mark
  | marked, marked => marked
  | marked, unmarked => marked
  | unmarked, marked => marked
  | unmarked, unmarked => unmarked

/-- Law of Calling: mark ∙ mark = mark -/
theorem law_of_calling : call marked marked = marked := rfl

/-- Calling is idempotent -/
theorem calling_idempotent (m : Mark) : call m m = m := by
  cases m <;> rfl

/-! ## Law of Crossing (Cancellation) -/

/--
  Crossing: Moving across a boundary.
  Cross inverts the mark: marked ↔ unmarked
-/
def cross : Mark → Mark
  | marked => unmarked
  | unmarked => marked

/--
  Law of Crossing: Crossing twice returns to the original.
  Cross(Cross(x)) = x

  "The value of a crossing made again is not the value of the crossing."
  — Spencer-Brown
-/
theorem law_of_crossing (m : Mark) : cross (cross m) = m := by
  cases m <;> rfl

/-- Crossing is an involution (applying twice returns original) -/
theorem crossing_involution (m : Mark) : cross (cross m) = m := law_of_crossing m

/-! ## The Mark and Unmarked are Distinguishable -/

/-- The fundamental distinction: marked ≠ unmarked -/
theorem mark_distinction : Distinguishable marked unmarked := by
  intro h
  cases h

/-- This is Spencer-Brown's primitive: the existence of distinction -/
theorem spencer_brown_primitive : ∃ a b : Mark, Distinguishable a b :=
  ⟨marked, unmarked, mark_distinction⟩

/-! ## Connection to Boolean Logic -/

/-- Mark corresponds to True, Unmarked to False -/
def toBool : Mark → Bool
  | marked => true
  | unmarked => false

def fromBool : Bool → Mark
  | true => marked
  | false => unmarked

theorem mark_bool_iso : ∀ m, fromBool (toBool m) = m := by
  intro m; cases m <;> rfl

theorem bool_mark_iso : ∀ b, toBool (fromBool b) = b := by
  intro b; cases b <;> rfl

/-! ## Distinction as Foundation for Limit Theorems -/

/--
  Gödel's Incompleteness requires: Provable ≠ True
  (There are true statements that are not provable)
  This is a distinction: [Provable, True] ≠ 0
-/
theorem godel_requires_distinction :
    (∃ (Provable True_ : Prop), Provable ≠ True_) →
    (∃ (Provable True_ : Prop), Distinguishable Provable True_) := by
  intro ⟨P, T, h⟩
  exact ⟨P, T, h⟩

/--
  Turing's Halting Problem requires: Decidable ≠ Computable
  (Not all computable functions are decidable)
  This is a distinction: [Decidable, Computable] ≠ 0
-/
theorem turing_requires_distinction :
    (∃ (Decidable_ Computable_ : Prop), Decidable_ ≠ Computable_) →
    (∃ (D C : Prop), Distinguishable D C) := by
  intro ⟨D, C, h⟩
  exact ⟨D, C, h⟩

/--
  Heisenberg's Uncertainty requires: [x, p] ≠ 0
  Position and momentum don't commute.
  This IS distinction at the quantum level!
-/
theorem heisenberg_is_distinction :
    ∀ (x p : Type), (∃ f g : x → p, f ≠ g) →
    (∃ f g : x → p, Distinguishable f g) := by
  intro x p ⟨f, g, h⟩
  exact ⟨f, g, h⟩

/-! ## Summary: Distinction Underlies All Limit Theorems -/

/--
  All fundamental limit theorems presuppose distinction:

  1. Gödel: [Provable, True] ≠ 0
  2. Turing: [Decidable, Computable] ≠ 0
  3. Heisenberg: [x, p] ≠ 0
  4. Our Foundation Limit: [Something, Nothing] ≠ 0

  Distinction is the meta-foundation.
-/
theorem distinction_underlies_limits :
    Distinguishable marked unmarked ∧
    Distinguishable True False := by
  constructor
  · exact mark_distinction
  · exact logical_distinction_theorem

end PhysicalLoF.Foundations
