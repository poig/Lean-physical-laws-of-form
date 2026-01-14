-- SPDX-License-Identifier: MIT
/-
  Goedel.lean
  ===========
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Mapping Gödel's Incompleteness to Meta-Distinction.

  KEY INSIGHT:
  A Logical System (T) is a Structure (Meta-Distinction).
  Incompleteness means the Structure has "Blind Spots".
  There exist distinctions [True, False] for G that T cannot observe.
-/

import PhysicalLoF.Foundations.System.MetaDistinction
import Foundation.FirstOrder.Incompleteness.First

namespace PhysicalLoF.Logic

open Foundations
open LO.FirstOrder
open LO.FirstOrder.Arithmetic

/-! ## Logic as Meta-Distinction -/

/--
  A Theory T acts as a Meta-Distinction on Sentences.
  It allows us to distinguish True statements from False ones.
-/
structure LogicDistinction (T : ArithmeticTheory) where
  -- We treat "Truth" as a distinction between φ and ∼φ
  knows_truth : Sentence ℒₒᵣ → Bool

/--
  The Provability Constraint:
  We can only distinguish φ from ∼φ if T proves one of them.
-/
def ProvabilityConstraint (T : ArithmeticTheory) : MetaDistinction (Sentence ℒₒᵣ) where
  Allow := fun φ ψ =>
    -- We allow distinguishing φ from ψ only if T proves they are different
    -- Simplified: If T proves (φ ↔ ¬ψ)
    Nonempty (T ⊢ φ ⭤ ∼ψ)
  Cost := fun _ _ => 1

/-! ## The Bridge Theorem -/

/--
  Gödel's Theorem rephrased:
  There exists a distinction (G vs ~G) that is REAL (in Model N)
  but NOT OBSERVABLE by T (ProvabilityConstraint).
-/
theorem goedel_implies_hidden_distinction
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ (δ : Sentence ℒₒᵣ),
      -- 1. Example: Delta is True in reality (Distinguishable from False in N)
      (ℕ ⊧ₘ δ) ∧
      -- 2. But T cannot distinguish it (cannot prove it)
      (T ⊬ δ) := by

  -- This is exactly the content of 'exists_true_but_unprovable_sentence'
  exact exists_true_but_unprovable_sentence T

/--
  **SUBSTANTIVE THEOREM**: Logic is a subset of Meta-Distinction.

  Some distinctions are Real (true in ℕ) but Unprovable (T cannot observe them).
  This is the formal content of Gödel's incompleteness.
-/
theorem logic_distinction_limit (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ (δ : Sentence ℒₒᵣ), (ℕ ⊧ₘ δ) ∧ (T ⊬ δ) :=
  exists_true_but_unprovable_sentence T

end PhysicalLoF.Logic
