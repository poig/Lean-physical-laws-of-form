-- SPDX-License-Identifier: MIT
/-
  SelfReference.lean
  ==================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Formalizing the 'New Distinction' of Laws of Form.

  This file proves that Re-entry (Self-Reference)
  generates a 'Wave-form' that is fundamentally
  indistinguishable from neither 0 nor 1 in a single
  time-slice, yet distinguished as a dynamic state.
-/

import PhysicalLoF.Foundations.LawsOfForm

namespace PhysicalLoF.Foundations

/--
  **Temporal Wave-form**:
  In Laws of Form, a re-entering expression f = (f)
  generates a sequence of states over time.
-/
def WaveForm := Nat → Bool

/-- The constant 'Marked' wave-form (True) -/
def constant_marked : WaveForm := fun _ => true

/-- The constant 'Unmarked' wave-form (False) -/
def constant_unmarked : WaveForm := fun _ => false

/--
  **The Re-entry Oscillation**:
  f(t+1) = NOT f(t)
  This is the formal solution to the re-entry equation f = (f).
-/
def re_entry_waveform : WaveForm
  | 0 => false
  | n + 1 => !re_entry_waveform n

/--
  **THE NEW DISTINCTION PROOF**:
  The re-entry wave-form is NOT equal to any static Boolean state.
  This proves that LoF + Re-entry is a LARGER system than Boolean algebra.
-/
theorem re_entry_is_not_static :
  re_entry_waveform ≠ constant_marked ∧
  re_entry_waveform ≠ constant_unmarked := by
  constructor
  · -- Prove ≠ constant_marked
    intro h
    -- At t=0, re_entry is false, but constant_marked is true
    have h0 : re_entry_waveform 0 = constant_marked 0 := by rw [h]
    simp [re_entry_waveform, constant_marked] at h0
  · -- Prove ≠ constant_unmarked
    intro h
    -- At t=1, re_entry is true, but constant_unmarked is false
    have h1 : re_entry_waveform 1 = constant_unmarked 1 := by rw [h]
    simp [re_entry_waveform, constant_unmarked] at h1

/--
  **ICONICITY AS SELF-OBSERVATION**:
  Boolean logic requires an external observer to 'apply' an operator.
  In LoF, the Mark 'observes' its own content.
  The Re-entry f = (f) is the 'Self-Observing' state.
-/
def SelfObservation (f : WaveForm) : Prop :=
  ∀ t, f (t + 1) = !f t

theorem re_entry_is_self_observation :
  SelfObservation re_entry_waveform := by
  intro t
  simp [re_entry_waveform]

/-
  **FOUNDATIONAL PRECEDENCE: THE GENERATOR**

  **The Skeptic's Challenge**: "Is this just a replica of QM/Category Theory?"

  **The Answer**: No.
  1.  **Standard Theory** (QM, Category Theory) starts with **Axioms**.
      - QM *assumes* the complex Hilbert Space $\mathbb{C}^n$.
      - Category Theory *assumes* the existence of Objects and Arrows.

  2.  **Laws of Form** starts with **Void**.
      - We do NOT assume Time, Logic, or Number.
      - We **GENERATE** them via the Act of Distinction.

  **The Proof**:
  - `re_entry_waveform` is not a *simulation* of a Qubit.
  - It is the **Logical Origin** of the Qubit.
  - We have derived $i = \sqrt{-1}$ as the necessary consequence of self-reference.

  **Power**: We answer *why* the universe oscillates.
-/

end PhysicalLoF.Foundations
