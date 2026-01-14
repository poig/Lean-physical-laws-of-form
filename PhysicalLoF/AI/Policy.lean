-- SPDX-License-Identifier: MIT
/-
  Policy.lean
  ===========
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Policies as Functions that Respect Observation Equivalence

  EMERGENCE FROM FOUNDATIONS:
  - Foundation provides: BoundedMetaDistinction (capacity-limited observation)
  - Observation.lean provides: ObsEq equivalence relation, ObsQuot quotient
  - This module proves: Valid policies MUST factor through observation

  Key theorem: `factors_through_observe` - the policy space is bounded by Capacity,
  not by the size of the universe. This is why learning is possible.
-/

import PhysicalLoF.AI.Observation

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-- A policy maps (latent) world states to actions/outputs. -/
def Policy (U : Type u) (A : Type v) : Type (max u v) := U → A

/-- A policy is well-defined w.r.t. the observer if it cannot depend on unobservable differences. -/
def RespectsObs {U : Type u} {A : Type v} (M : BoundedMetaDistinction U) (π : Policy U A) : Prop :=
  ∀ {a b : U}, ObsEq M a b → π a = π b

/-- Any observation-respecting policy canonically lifts to the observation quotient. -/
def liftPolicy {U : Type u} {A : Type v}
    (M : BoundedMetaDistinction U) (π : Policy U A) (h : RespectsObs M π) : ObsQuot M → A :=
  Quot.lift π (by
    intro a b hab
    exact h hab)

@[simp] theorem liftPolicy_class {U : Type u} {A : Type v}
    (M : BoundedMetaDistinction U) (π : Policy U A) (h : RespectsObs M π) (u : U) :
    liftPolicy M π h (obsClass M u) = π u := by
  rfl

/-- If observations are surjective onto the finite keyspace, a respecting policy factors through keys. -/
theorem factors_through_observe
    {U : Type u} {A : Type v} [Inhabited U]
    (M : BoundedMetaDistinction U)
    (π : Policy U A)
    (h : RespectsObs M π)
    (h_surj : Function.Surjective M.observe) :
    ∃ f : (Fin M.Capacity → A), ∀ u : U, π u = f (M.observe u) := by
  classical
  refine ⟨fun k => π (Classical.choose (h_surj k)), ?_⟩
  intro u
  have hk : M.observe (Classical.choose (h_surj (M.observe u))) = M.observe u :=
    Classical.choose_spec (h_surj (M.observe u))
  -- Use the respectfulness to rewrite across observation equivalence
  exact (h hk).symm

end PhysicalLoF.AI
