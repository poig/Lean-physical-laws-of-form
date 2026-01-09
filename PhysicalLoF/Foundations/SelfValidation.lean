-- SPDX-License-Identifier: MIT
/-
  SelfValidation.lean
  ===================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Performative Consistency and Self-Validation

  We prove that "denying distinction" is a performative contradiction.
  To deny P, one must distinguish P from True.
-/

import PhysicalLoF.Foundations.Distinction
import Mathlib.Tactic

namespace PhysicalLoF.Foundations

/-! ## The Necessity of Distinction for Refutation -/

/--
  **THEOREM: Refutation Implies Distinction**

  To assert "Not P" (¬P) is to assert that P implies False.
  This structurally requires distinguishing the case where P holds regarding False.

  Formally: If ¬P is true, then P is distinguishable from True.
-/
theorem refutation_implies_distinction {P : Prop} (h : ¬P) :
    Distinguishable P True := by
  -- Distinguishable P True means P ≠ True
  unfold Distinguishable
  intro h_eq
  -- If P = True, then ¬P = ¬True = False, contradiction
  rw [h_eq] at h
  exact h trivial

/--
  **THEOREM: The "Performative Cogito"**

  The statement "There are no distinctions" refutes itself.
  Let Q = "∀ P S : Prop, ¬Distinguishable P S".
  If Q is true, then we can surely distinguish True from False?
-/
theorem performative_consistency :
    ¬(∀ (A B : Prop), ¬Distinguishable A B) := by
  intro NoDistinction
  -- If there are no distinctions, then True and False are indistinguishable
  have h_tf := NoDistinction True False
  -- But we know True and False ARE distinguishable
  have h_dist : Distinguishable True False := logical_distinction_theorem
  -- Contradiction
  exact h_tf h_dist

/-! ## Self-Validation of the Foundation -/

/--
  **THEOREM: The Foundation is Unavoidable**

  Any attempt to define a system without distinction fails because
  defining the system distinguishes it from "no system".
-/
theorem distinction_is_unavoidable :
  ∀ (System : Type), (System → Prop) → ∃ (a b : Prop), Distinguishable a b :=
  fun _ _ => ⟨True, False, logical_distinction_theorem⟩

end PhysicalLoF.Foundations
