-- SPDX-License-Identifier: MIT
/-
  SelfModel.lean
  ==============

  Self-modeling: an agent that represents its own observation class.
  Consistency = internal model matches external reality.
  Mismatch = hallucination / delusion.
-/

import PhysicalLoF.AI.Observation

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-! ## Self-Model Structure -/

/--
A self-model is an agent's internal representation of:
- its own state (internal)
- what it believes the world sees of it (external)
Consistency requires these match.
-/
structure SelfModel (U : Type u) (M : BoundedMetaDistinction U) where
  /-- The agent's internal belief about its own observation class -/
  internal : ObsQuot M
  /-- The agent's belief about how the external world perceives it -/
  external : ObsQuot M

/-- A self-model is consistent if internal = external. -/
def SelfModel.isConsistent {U : Type u} {M : BoundedMetaDistinction U} (s : SelfModel U M) : Prop :=
  s.internal = s.external

/-- Hallucination: the internal model claims something the external model doesn't support. -/
def SelfModel.isHallucinating {U : Type u} {M : BoundedMetaDistinction U} (s : SelfModel U M) : Prop :=
  s.internal ≠ s.external

theorem consistent_not_hallucinating {U : Type u} {M : BoundedMetaDistinction U} (s : SelfModel U M) :
    s.isConsistent ↔ ¬s.isHallucinating := by
  simp [SelfModel.isConsistent, SelfModel.isHallucinating]

/-! ## Grounded Self-Model -/

/--
A grounded self-model: the agent's internal belief matches the actual observation class
of its true state.
-/
def GroundedSelfModel {U : Type u} (M : BoundedMetaDistinction U) (trueState : U) : SelfModel U M where
  internal := obsClass M trueState
  external := obsClass M trueState

theorem grounded_is_consistent {U : Type u} (M : BoundedMetaDistinction U) (u : U) :
    (GroundedSelfModel M u).isConsistent := by
  rfl

/-! ## Self-Model Updates -/

/--
An update function that maintains consistency: if you update both internal and external
the same way, consistency is preserved.
-/
def updateSelfModel {U : Type u} {M : BoundedMetaDistinction U}
    (s : SelfModel U M) (f : ObsQuot M → ObsQuot M) : SelfModel U M where
  internal := f s.internal
  external := f s.external

theorem update_preserves_consistency {U : Type u} {M : BoundedMetaDistinction U}
    (s : SelfModel U M) (f : ObsQuot M → ObsQuot M) (hc : s.isConsistent) :
    (updateSelfModel s f).isConsistent := by
  simp only [SelfModel.isConsistent, updateSelfModel] at *
  rw [hc]

end PhysicalLoF.AI
