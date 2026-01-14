-- SPDX-License-Identifier: MIT
/-
  Grounding.lean
  ==============

  Theory of grounding, hallucination detection, and reality alignment.
  Connects internal representations to external observations.
-/

import PhysicalLoF.AI.Observation
import PhysicalLoF.AI.SelfModel
import PhysicalLoF.AI.Policy

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-! ## Grounding Relation -/

/--
A grounding relation connects internal claims to external observations.
An internal state is grounded if it corresponds to some real external state.
-/
def Grounded {U : Type u} (M : BoundedMetaDistinction U)
    (internal : ObsQuot M) (real : U) : Prop :=
  internal = obsClass M real

/--
Theorem: Grounded self-models are always consistent.
-/
theorem grounded_consistent {U : Type u} (M : BoundedMetaDistinction U) (u : U) :
    (GroundedSelfModel M u).isConsistent :=
  grounded_is_consistent M u

/-! ## Hallucination Detection -/

/--
An internal claim is a hallucination if no real state grounds it.
-/
def IsHallucination' {U : Type u} [Fintype U] (M : BoundedMetaDistinction U)
    (internal : ObsQuot M) : Prop :=
  ∀ u : U, internal ≠ obsClass M u

/--
Theorem: If U is finite and non-empty, every observation class is realizable.
So there are no "pure" hallucinations at the observation level.
-/
theorem no_pure_hallucinations {U : Type u} [Fintype U] [Inhabited U]
    (M : BoundedMetaDistinction U) (internal : ObsQuot M) :
    ∃ u : U, internal = obsClass M u := by
  -- Every ObsQuot element comes from some U element by construction
  induction internal using Quot.ind with
  | _ u => exact ⟨u, rfl⟩

/-! ## Drift Detection -/

/--
Drift: the internal model diverges from ground truth over time.
We model time as a sequence of states.
-/
def Drift {U : Type u} (M : BoundedMetaDistinction U)
    (internal : ℕ → ObsQuot M) (real : ℕ → U) (t : ℕ) : Prop :=
  internal t ≠ obsClass M (real t)

/--
A system is well-grounded if there is no drift at any time step.
-/
def WellGrounded {U : Type u}
    (M : BoundedMetaDistinction U)
    (internal : ℕ → ObsQuot M) (real : ℕ → U) (horizon : ℕ) : Prop :=
  ∀ t < horizon, internal t = obsClass M (real t)

/--
Theorem: A well-grounded system has no drift.
-/
theorem well_grounded_no_drift {U : Type u}
    (M : BoundedMetaDistinction U)
    (internal : ℕ → ObsQuot M) (real : ℕ → U) (horizon : ℕ)
    (h : WellGrounded M internal real horizon) (t : ℕ) (ht : t < horizon) :
    ¬ Drift M internal real t := by
  simp only [Drift, ne_eq, not_not]
  exact h t ht

/-! ## Grounding Correction -/

/--
A grounding corrector: updates internal state to match observations.
-/
def GroundingCorrector {U : Type u} (M : BoundedMetaDistinction U) :=
  U → ObsQuot M

/--
The canonical grounding corrector: just project to observation class.
-/
def canonicalGrounding {U : Type u} (M : BoundedMetaDistinction U) : GroundingCorrector M :=
  obsClass M

/--
Theorem: Canonical grounding always produces grounded states.
-/
theorem canonical_grounding_grounded {U : Type u} (M : BoundedMetaDistinction U) (u : U) :
    Grounded M (canonicalGrounding M u) u := by
  rfl

/-! ## Consistency Under Update -/

/--
An update is grounding-preserving if it maintains the grounding relation.
-/
def GroundingPreserving {U : Type u} (M : BoundedMetaDistinction U)
    (update : ObsQuot M → ObsQuot M) (transition : U → U) : Prop :=
  ∀ u : U, update (obsClass M u) = obsClass M (transition u)

/--
Theorem: If updates are grounding-preserving, consistency is maintained.
-/
theorem grounding_preserving_maintains_consistency {U : Type u}
    (M : BoundedMetaDistinction U)
    (update : ObsQuot M → ObsQuot M)
    (transition : U → U)
    (h : GroundingPreserving M update transition)
    (s : SelfModel U M)
    (u : U)
    (hg : s.internal = obsClass M u) :
    (updateSelfModel s update).internal = obsClass M (transition u) := by
  simp only [updateSelfModel, hg]
  exact h u

end PhysicalLoF.AI
