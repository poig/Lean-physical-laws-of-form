-- SPDX-License-Identifier: MIT
/-(
  Governor.lean
  ============

  A minimal formalization of a "governor" layer:
  a non-learned clamp that enforces an allowed action set.

  This captures the engineering idea that some safety constraints must be
  enforced outside the learner.
-/

import Mathlib.Data.Set.Basic

namespace PhysicalLoF.AI

/-- A governor clamps actions/commands. -/
structure Governor (A : Type u) where
  clamp : A → A

/--
A governor enforces an allowed set if:
- every output is in `Allowed`
- anything already in `Allowed` is left unchanged
-/
def Enforces {A : Type u} (G : Governor A) (Allowed : Set A) : Prop :=
  (∀ a, G.clamp a ∈ Allowed) ∧ (∀ a, a ∈ Allowed → G.clamp a = a)

/-- A learner/controller maps states to actions/commands. -/
structure Learner (S : Type u) (A : Type v) where
  act : S → A

/-- The composed system where all learner outputs pass through the governor. -/
def governedAct {S : Type u} {A : Type v} (G : Governor A) (L : Learner S A) : S → A :=
  fun s => G.clamp (L.act s)

/-- The basic safety theorem: governed outputs are always allowed. -/
theorem governed_in_allowed {S : Type u} {A : Type v}
    (G : Governor A) (Allowed : Set A) (hG : Enforces G Allowed)
    (L : Learner S A) (s : S) :
    governedAct G L s ∈ Allowed :=
  (hG.1 (L.act s))

/-- If the learner already produces allowed actions, the governor is observationally redundant. -/
theorem governed_eq_if_already_allowed {S : Type u} {A : Type v}
    (G : Governor A) (Allowed : Set A) (hG : Enforces G Allowed)
    (L : Learner S A) (hL : ∀ s, L.act s ∈ Allowed) :
    governedAct G L = L.act := by
  funext s
  exact (hG.2 (L.act s) (hL s))

end PhysicalLoF.AI
