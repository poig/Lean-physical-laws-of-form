/-
  PhysicalLoF.lean
  ================

  Main entry point for the Physical Laws of Form library.

  This library extends Spencer-Brown's Laws of Form (1969) to physics
  and computation, providing machine-verified proofs of the necessity
  of non-commutativity for existence.

  Key Theorems:
  - Spencer-Brown Collapse Theorem
  - Distinction-Existence Theorem
  - Master Necessity Theorem

  Author: Engineering ToE Framework
  Based on: Spencer-Brown, G. (1969). Laws of Form.
-/

-- Foundations
import PhysicalLoF.Foundations.Distinction
import PhysicalLoF.Foundations.Collapse
import PhysicalLoF.Foundations.Existence

-- Re-export main definitions
namespace PhysicalLoF

export Foundations (Distinguishable spencer_brown_collapse master_necessity)

end PhysicalLoF
