-- SPDX-License-Identifier: MIT
/-
  Observation.lean
  ================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Observation-Induced Equivalence Classes

  EMERGENCE FROM FOUNDATIONS:
  - Foundation provides: BoundedMetaDistinction with `observe : U → Fin Capacity`
  - This module builds: The quotient structure (ObsQuot) and equivalence (ObsEq)
  - NOT duplicating: The Observer/Capacity/observe are Foundation primitives

  The key insight: `observe` induces an equivalence relation, and the quotient
  is the agent's effective state space (what it can actually distinguish).
-/

import PhysicalLoF.Foundations.System.MetaDistinction

namespace PhysicalLoF.AI

open PhysicalLoF.Foundations

/-- Observation-equivalence induced by a bounded observer. -/
def ObsEq {U : Type u} (M : BoundedMetaDistinction U) : U → U → Prop :=
  fun a b => M.observe a = M.observe b

theorem obsEq_refl {U : Type u} (M : BoundedMetaDistinction U) (a : U) : ObsEq M a a := by
  rfl

theorem obsEq_symm {U : Type u} (M : BoundedMetaDistinction U) {a b : U} :
    ObsEq M a b → ObsEq M b a := by
  intro h
  simpa [ObsEq] using h.symm

theorem obsEq_trans {U : Type u} (M : BoundedMetaDistinction U) {a b c : U} :
    ObsEq M a b → ObsEq M b c → ObsEq M a c := by
  intro hab hbc
  simpa [ObsEq] using hab.trans hbc

/-- Package the equivalence proof for use with `Quot`. -/
def obsEq_equiv {U : Type u} (M : BoundedMetaDistinction U) : Equivalence (ObsEq M) where
  refl := obsEq_refl M
  symm := obsEq_symm M
  trans := obsEq_trans M

/-- The agent's epistemic state space: world states quotiented by indistinguishability. -/
def ObsQuot {U : Type u} (M : BoundedMetaDistinction U) : Type u :=
  Quot (ObsEq M)

/-- Inject a concrete world state into its observation-equivalence class. -/
def obsClass {U : Type u} (M : BoundedMetaDistinction U) (u : U) : ObsQuot M :=
  Quot.mk _ u

/-- Every observation-equivalence class has a canonical observable key. -/
def obsKey {U : Type u} (M : BoundedMetaDistinction U) : ObsQuot M → Fin M.Capacity :=
  Quot.lift M.observe (by
    intro a b hab
    simpa [ObsEq] using hab)

theorem obsKey_class {U : Type u} (M : BoundedMetaDistinction U) (u : U) :
    obsKey M (obsClass M u) = M.observe u := by
  rfl

end PhysicalLoF.AI
