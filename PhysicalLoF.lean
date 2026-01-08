/-
  PhysicalLoF.lean
  ================

  Main entry point for the Physical Laws of Form library.

  This library extends Spencer-Brown's Laws of Form (1969) to physics
  and computation, providing machine-verified proofs of the necessity
  of non-commutativity for existence.

  Key Theorems:
  - Indistinguishability Collapse Theorem
  - Distinction-Existence Theorem
  - Master Necessity Theorem
  - Foundation Limit Theorem (Optimality)
  - Laws of Calling and Crossing

  Author: Engineering ToE Framework
  Based on: Spencer-Brown, G. (1969). Laws of Form.
-/

-- Foundations
import PhysicalLoF.Foundations.Distinction
import PhysicalLoF.Foundations.Collapse
import PhysicalLoF.Foundations.Existence
import PhysicalLoF.Foundations.Optimality
import PhysicalLoF.Foundations.LawsOfForm
import PhysicalLoF.Foundations.Transformation

-- Impossibility Theorems (Gödel, Turing, Heisenberg)
import PhysicalLoF.ImpossibilityTheorems

-- Re-export main definitions
namespace PhysicalLoF

export Foundations (
  -- Core distinction
  Distinguishable
  -- Collapse and existence
  indistinguishability_collapse
  master_necessity
  -- Optimality
  distinction_is_optimal
  foundation_limit
  -- Spencer-Brown's Laws
  Mark
  law_of_calling
  law_of_crossing
  spencer_brown_primitive
  distinction_underlies_limits
)

end PhysicalLoF
