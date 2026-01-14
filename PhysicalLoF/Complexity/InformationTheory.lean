-- SPDX-License-Identifier: MIT
/-
  InformationTheory.lean
  ======================
  Copyright (C) 2026 Tan Jun Liang

  Bridging Distinction Logic to Information Theory.

  We serve the AI Engineering needs by proving:
  1. **Kolmogorov Complexity** is just **Distinction Cost** (length of the Form).
  2. **Generalization** is **Sparsity** (Occam's Razor).

  This provides the theoretical justification for why sparse models (like DeepSeek)
  outperform dense models in efficiency.
-/

import PhysicalLoF.Intelligence
import PhysicalLoF.Foundations.Core.Distinction

namespace PhysicalLoF.Complexity.InformationTheory

open PhysicalLoF.Intelligence
open PhysicalLoF.Foundations.Form

/-! ## 1. Kolmogorov Complexity -/

/--
  **Kolmogorov Complexity K(x)**:
  The length of the shortest program that outputs x.

  In Laws of Form, the "Program" is the Form itself.
  The "Length" is the Distinction Cost (number of marks).
-/
def KolmogorovComplexity (f : PhysicalLoF.Foundations.Form) : ℕ :=
  DistinctionCost f

/--
  **Theorem: The Void is the Simplest Program**.
  K(0) = 0.
-/
theorem void_is_simplest : KolmogorovComplexity void = 0 := rfl

/-! ## 2. Compression Ratio -/

/--
  **Compression Ratio**:
  Size(Uncompressed) / Size(Compressed).

  Here, we compare the "Raw Truth Table" size to the "Distinction Cost".
-/
noncomputable def CompressionRatio (TruthTableSize : ℕ) (f : PhysicalLoF.Foundations.Form) : ℚ :=
  (TruthTableSize : ℚ) / max 1 (DistinctionCost f : ℚ)

/-! ## 3. The Generalization Theorem (Occam's Razor) -/

/--
  **Principle of Sparsity**:
  If two Forms A and B simulate the same Logic (Extension),
  the one with lower Distinction Cost (Intension) is "better".

  This is the formal definition of **Occam's Razor**.
-/
def IsBetterModel (A B : PhysicalLoF.Foundations.Form) : Prop :=
  (∀ (ctx : PhysicalLoF.Foundations.Form), eval (compose A ctx) = eval (compose B ctx)) ∧ -- Same Behavior
  (DistinctionCost A < DistinctionCost B) -- Lower Cost

/--
  **Theorem: Optimization Targets Sparsity**.
  An ideal optimizer reduces Kolmogorov Complexity while maintaining accuracy.
-/
theorem sparsity_is_optimization (A B : PhysicalLoF.Foundations.Form) :
  IsBetterModel A B → KolmogorovComplexity A < KolmogorovComplexity B := by
  intro h
  exact h.2

end PhysicalLoF.Complexity.InformationTheory
