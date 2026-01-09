-- SPDX-License-Identifier: MIT
/-
  Automata.lean
  =============
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Myhill-Nerode Theorem as Capacity Overflow

  KEY INSIGHT:
  The Myhill-Nerode theorem states that a language is regular IFF
  it has finitely many equivalence classes of distinguishable strings.

  This is EXACTLY our Capacity Overflow framework:
  - Finite equivalence classes → Finite Capacity → Regular (tractable)
  - Infinite equivalence classes → Capacity Overflow → Non-regular (intractable)

  The automaton's STATES are the CAPACITY to distinguish strings!

  This file USES Mathlib's official Myhill-Nerode formalization.
-/

import Mathlib.Computability.MyhillNerode
import PhysicalLoF.Foundations.MetaDistinction
import PhysicalLoF.Foundations.Distinction

namespace PhysicalLoF.Complexity

open Foundations
open Language

/-! ## Using Mathlib's Myhill-Nerode -/

variable {α : Type*}

/--
  **BRIDGE TO MATHLIB**: Mathlib's `leftQuotient` is the distinguishability relation.

  Two strings x and y are L-equivalent iff L.leftQuotient x = L.leftQuotient y.
  This is exactly our "indistinguishable" notion.
-/
def StringsIndistinguishable (L : Language α) (x y : List α) : Prop :=
  L.leftQuotient x = L.leftQuotient y

/--
  **MATHLIB THEOREM**: The Myhill-Nerode theorem directly.

  A language is regular iff the set of left quotients is finite.
  In capacity terms: Regular ↔ Finite Capacity.
-/
theorem myhill_nerode_mathlib (L : Language α) :
    L.IsRegular ↔ (Set.range L.leftQuotient).Finite :=
  Language.isRegular_iff_finite_range_leftQuotient

/-! ## Connection to Meta-Distinction -/

/--
  A Language defines a Meta-Distinction on strings.
  The distinguishability is based on left quotients (Mathlib's definition).
-/
def LanguageAsMetaDistinction (L : Language α) : MetaDistinction (List α) where
  Allow := fun x y => L.leftQuotient x ≠ L.leftQuotient y  -- Different quotients = distinguishable
  Cost := fun _ _ => 1

/-! ## Capacity Overflow Interpretation -/

/--
  **CAPACITY OVERFLOW THEOREM** (using Mathlib):

  If the set of left quotients is infinite, the language is NOT regular.
  This is capacity overflow: infinite distinguishability → non-regularity.
-/
theorem capacity_overflow_implies_nonregular (L : Language α) :
    (Set.range L.leftQuotient).Infinite → ¬L.IsRegular := by
  intro h_infinite
  rw [myhill_nerode_mathlib]
  exact Set.not_finite.mpr h_infinite

/--
  **FINITE CAPACITY THEOREM** (using Mathlib):

  If a language is regular, its left quotient set is finite.
  This means: regular languages have finite distinction capacity.
-/
theorem regular_implies_finite_capacity (L : Language α) :
    L.IsRegular → (Set.range L.leftQuotient).Finite :=
  (myhill_nerode_mathlib L).mp

/--
  **THE CAPACITY-REGULARITY EQUIVALENCE**:

  This is the core connection between our framework and automata theory:
  - Finite states = Finite capacity
  - Regular language = Finite equivalence classes = Bounded distinction
-/
theorem capacity_regularity_equivalence (L : Language α) :
    L.IsRegular ↔ (Set.range L.leftQuotient).Finite :=
  myhill_nerode_mathlib L

end PhysicalLoF.Complexity
