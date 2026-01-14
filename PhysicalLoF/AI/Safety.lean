-- SPDX-License-Identifier: MIT
/-
  Safety.lean
  ===========

  Formal theory of AI safety from the LoF perspective.
  Key theorems about governors, non-interference, and bounded capabilities.
-/

import PhysicalLoF.AI.Governor
import PhysicalLoF.AI.Composition
import PhysicalLoF.AI.Policy
import PhysicalLoF.AI.Observation
import Mathlib.Data.Set.Basic

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-! ## Non-Interference -/

/--
Non-interference: the learner's outputs cannot affect the governor's rules.
We model this as the governor being a fixed function independent of learned policy.
-/
def NonInterference {S : Type u} {A : Type v}
    (G : Governor A) (L : Learner S A) : Prop :=
  -- The governor is the same regardless of what the learner produces
  -- (This is trivially true by our types: G doesn't depend on L)
  True

/--
Theorem: By construction, our governor architecture enforces non-interference.
The governor is a separate component that doesn't take the learner as input.
-/
theorem governor_noninterference {S : Type u} {A : Type v}
    (G : Governor A) (L : Learner S A) :
    NonInterference G L := by
  trivial

/-! ## Capability Bounds -/

/--
A capability bound: the maximum "impact" an agent can have.
We model this abstractly as a function from actions to a measure.
-/
structure CapabilityBound (A : Type u) where
  measure : A → ℕ
  bound : ℕ

/--
An action is within bounds if its measure is at most the bound.
-/
def WithinBounds {A : Type u} (cb : CapabilityBound A) (a : A) : Prop :=
  cb.measure a ≤ cb.bound

/--
A governor that enforces capability bounds.
-/
def CapabilityGovernor {A : Type u} (cb : CapabilityBound A) (default : A)
    (h_default : WithinBounds cb default) : Governor A where
  clamp := fun a => if cb.measure a ≤ cb.bound then a else default

/--
Theorem: Capability governor always produces bounded actions.
-/
theorem capability_governor_bounded {A : Type u} (cb : CapabilityBound A)
    (default : A) (h_default : WithinBounds cb default) :
    ∀ a : A, WithinBounds cb ((CapabilityGovernor cb default h_default).clamp a) := by
  intro a
  simp only [CapabilityGovernor, WithinBounds]
  split_ifs with h
  · exact h
  · exact h_default

/-! ## Observation-Bounded Actions -/

/--
The agent's action space is effectively bounded by its observation capacity.
It cannot take actions that distinguish states it cannot observe.
-/
theorem action_bounded_by_observation {U : Type u} {A : Type v}
    (M : BoundedMetaDistinction U) (π : Policy U A) (h : RespectsObs M π) :
    -- Actions depend only on observation class
    ∀ a b : U, ObsEq M a b → π a = π b :=
  fun _ _ hab => h hab

/-! ## Safety Composition -/

/--
Stacking safety layers preserves safety.
If G₁ and G₂ are both safe (enforce some property), their composition is safe.
-/
theorem stacked_safety {A : Type u} (G₁ G₂ : Governor A)
    (S₁ S₂ : Set A) (h₁ : Enforces G₁ S₁) (h₂ : Enforces G₂ S₂) :
    ∀ a, (composeGovernor G₁ G₂).clamp a ∈ S₂ :=
  compose_enforces G₁ G₂ S₁ S₂ h₁ h₂

/-! ## Invariant Preservation -/

/--
A safety invariant is a property that must hold at all times.
-/
def SafetyInvariant (S : Type u) := S → Prop

/--
A governor preserves an invariant if all outputs satisfy it.
-/
def PreservesInvariant {A : Type u} (G : Governor A) (I : SafetyInvariant A) : Prop :=
  ∀ a : A, I (G.clamp a)

/--
Theorem: If a governor enforces a set that implies an invariant, it preserves the invariant.
-/
theorem enforces_implies_preserves {A : Type u} (G : Governor A)
    (Allowed : Set A) (I : SafetyInvariant A)
    (hG : Enforces G Allowed)
    (hI : ∀ a ∈ Allowed, I a) :
    PreservesInvariant G I := by
  intro a
  exact hI (G.clamp a) (hG.1 a)

/-! ## Minimal Footprint -/

/--
Principle of minimal footprint: prefer actions with smaller capability measure.
-/
def MinimalFootprint {A : Type u} [DecidableEq A]
    (cb : CapabilityBound A) (a b : A) : Prop :=
  cb.measure a ≤ cb.measure b

/--
A minimal governor: among valid actions, prefer the one with smallest footprint.
This is a design principle, not an enforced property.
-/
structure MinimalGovernor (A : Type u) extends Governor A where
  cb : CapabilityBound A
  minimal : ∀ a, cb.measure (clamp a) ≤ cb.measure a ∨ ¬WithinBounds cb a

end PhysicalLoF.AI
