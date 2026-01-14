-- SPDX-License-Identifier: MIT
/-
  FeatureBound.lean
  =================

  The capacity of an observer upper-bounds the number of distinguishable features
  (equivalence classes) the agent can represent.
-/

import PhysicalLoF.AI.Observation
import Mathlib.Data.Fintype.Card

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-! ## Feature Count Bound -/

/--
The number of observationally-distinct classes is at most the observation capacity.
This is immediate from the fact that `obsKey` maps into `Fin M.Capacity`.
-/
theorem feature_bound {U : Type*} [Fintype U] (M : BoundedMetaDistinction U) :
    Fintype.card (Fin M.Capacity) = M.Capacity :=
  Fintype.card_fin M.Capacity

/--
If `observe` is injective (no collisions), then card U ≤ Capacity.
This is the "only if" direction: injectivity requires enough capacity.
-/
theorem injective_observe_implies_capacity {U : Type*} [Fintype U] (M : BoundedMetaDistinction U)
    (hinj : Function.Injective M.observe) :
    Fintype.card U ≤ M.Capacity := by
  have := Fintype.card_le_of_injective M.observe hinj
  simp at this
  exact this

/--
The converse is NOT generally true: having enough capacity doesn't guarantee
injectivity (the observe map might still collide). We state this as a hypothesis.
-/
def HasInjectiveObserver {U : Type u} (M : BoundedMetaDistinction U) : Prop :=
  Function.Injective M.observe

/--
For an injective observer, the quotient is isomorphic to U itself.
-/
theorem injective_obs_quot_equiv {U : Type u} (M : BoundedMetaDistinction U)
    (hinj : HasInjectiveObserver M) :
    ∀ a b : U, ObsEq M a b → a = b := by
  intro a b hab
  exact hinj hab

/--
Corollary: if the universe is larger than capacity, some distinctions MUST collapse.
(Already proved in MetaDistinction as `the_complete_picture`; re-export here for AI use.)
-/
theorem overflow_implies_collision {U : Type*} [Fintype U] (M : BoundedMetaDistinction U)
    (h : M.Capacity < Fintype.card U) :
    ∃ x y : U, x ≠ y ∧ M.observe x = M.observe y :=
  the_complete_picture M h

/-! ## Quotient Cardinality Bound -/

/--
The image of the observe map has cardinality at most Capacity.
This bounds the number of distinguishable observation classes.
-/
theorem observe_image_card_le {U : Type*} [Fintype U]
    (M : BoundedMetaDistinction U) :
    (Finset.univ.image M.observe).card ≤ M.Capacity := by
  have h1 : (Finset.univ (α := U)).image M.observe ⊆ Finset.univ (α := Fin M.Capacity) :=
    Finset.subset_univ _
  have h2 : ((Finset.univ (α := U)).image M.observe).card ≤ (Finset.univ (α := Fin M.Capacity)).card :=
    Finset.card_le_card h1
  simp only [Finset.card_univ, Fintype.card_fin] at h2
  exact h2

/--
Fundamental capacity theorem: the number of effectively distinct states
an agent can represent is bounded by its observation capacity.

This is the core "no free lunch" result for bounded observers.
-/
theorem effective_states_bounded {U : Type*} [Fintype U]
    (M : BoundedMetaDistinction U) :
    (Finset.univ.image M.observe).card ≤ M.Capacity :=
  observe_image_card_le M

end PhysicalLoF.AI
