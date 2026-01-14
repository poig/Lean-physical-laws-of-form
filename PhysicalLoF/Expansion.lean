-- SPDX-License-Identifier: MIT
/-
  Expansion.lean
  ==============
  Copyright (C) 2026 Tan Jun Liang

  The Formal Theory of Dimensional Expansion (Open-Endedness).
  Explains how "Capacity Overflow" triggers the creation of New Space.
-/

import PhysicalLoF.Foundations.System.MetaDistinction
import PhysicalLoF.Foundations.System.Transformation

namespace PhysicalLoF.Expansion

open PhysicalLoF.Foundations

/-! ## 1. The Finite Box Problem -/

/--
  **Closed System**:
  A system with a fixed number of dimensions $D$.
  It has a hard capacity limit $C_{max}$.
-/
structure ClosedSystem (D : ℕ) where
  State : Vector ℕ D
  Capacity : ℕ := 2^D

/--
  **The Overflow Condition**:
  When distinctions > Capacity, the system becomes "Confused" (Indistinguishable).
-/
def IsOverflow (sys : ClosedSystem D) (Distinctions : ℕ) : Prop :=
  Distinctions > sys.Capacity

/-! ## 2. The Dimensional Jump -/

/--
  **Open System**:
  A system that can change its Type (Dimension) over time.
  This requires a Sigma Type (Dependent Pair).
-/
structure OpenSystem where
  Dim : ℕ
  State : Vector ℕ Dim

/--
  **Expansion Operator**:
  A transformation that takes an overflowing system at Dim $D$
  and returns a stable system at Dim $D+1$.

  $E(S_D) \to S_{D+1}$
-/
def ExpandDimension (sys : OpenSystem) : OpenSystem :=
  { Dim := sys.Dim + 1,
    State := Vector.append sys.State (Vector.replicate 1 0) } -- Add a new axis (initialized to 0)

/-! ## 3. The Law of Necessity -/

/--
  **Theorem: The Dimensional Imperative**.
  If a system is overflowing, it MUST expand to resolve the paradox.
  (Optimization within D is impossible; only climbing to D+1 works).
-/
axiom DimensionalImperative :
  ∀ (sys : OpenSystem) (load : ℕ), load > 2^sys.Dim → ExpandDimension sys ≠ sys


/-
  **Interpretation**:
  - The "Wall" (Overflow) is the signal to "Grow".
  - Intelligence is not just "Solving the P puzzle" (Optimization).
  - Intelligence is "Inventing the NP oracle" (Expansion).
-/

end PhysicalLoF.Expansion
