-- SPDX-License-Identifier: MIT
/-
  MetaDistinction.lean
  ====================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  The Unified Theory: Constraints on Distinction
  Extended with CAPACITY LIMITS (inspired by DLA dimension bounds)
-/

import PhysicalLoF.Foundations.Distinction
import PhysicalLoF.Foundations.Transformation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole

namespace PhysicalLoF.Foundations

/-! ## Core Meta-Distinction -/

structure MetaDistinction (Universe : Type u) where
  Allow : Universe → Universe → Prop
  Cost : Universe → Universe → Nat

def RealDistinction {U : Type u} (M : MetaDistinction U) (a b : U) : Prop :=
  M.Allow a b ∧ Distinguishable a b

/-! ## Specific Constraints -/

def TimeConstraint {U : Type u} (RefFrame : U → Nat) : MetaDistinction U where
  Allow := fun a b => RefFrame a < RefFrame b
  Cost := fun a b => RefFrame b - RefFrame a

structure Observer where
  velocity : Float

def RelativityConstraint (_ : Observer) (TimeOf : U → Float) : MetaDistinction U where
  Allow := fun a b => TimeOf b - TimeOf a > 0
  Cost := fun _ _ => 1

def ComplexityConstraint {U : Type u} (_ : Nat) : MetaDistinction U where
  Allow := fun _ _ => True
  Cost := fun _ _ => 100

def EfficientlyDistinguishable {U : Type u} (M : MetaDistinction U) (a b : U) : Prop :=
  RealDistinction M a b ∧ M.Cost a b < 1000

/-! ## CAPACITY: The Missing Piece -/

/--
  Every Structure has a CAPACITY LIMIT.

  This is the maximum number of meaningful distinctions it can hold.
  We model this as a mapping from the Universe to a finite set of states (Fin Capacity).

  Physical/Computational Interpretations:
  - DLA Dimension in quantum circuits (paper 2508.05749)
  - Bekenstein Bound in black hole physics
  - Machine word size in computing
  - Channel capacity in information theory

  Theorem (from paper): DLA_dim ≤ m² where m = distinct eigenvalues
-/
structure BoundedMetaDistinction (Universe : Type u) extends MetaDistinction Universe where
  /-- The capacity limit: maximum simultaneous distinctions -/
  Capacity : Nat
  /-- The observation map: projects reality into finite capacity -/
  observe : Universe → Fin Capacity
  /-- Capacity must be positive to observe anything -/
  cap_pos : Capacity > 0

/--
  Observable Distinction:
  Two things are effectively distinct only if they map to different observable states.
-/
def ObservableDistinction {U : Type u} (M : BoundedMetaDistinction U) (a b : U) : Prop :=
  M.observe a ≠ M.observe b ∧ Distinguishable a b

/--
  The Overflow Theorem (formerly Axiom):
  If the number of input items EXCEEDS capacity, some must COLLAPSE.

  Proof: Uses the Pigeonhole Principle (Fintype.exists_ne_map_eq_of_card_lt).
-/
theorem overflow_collapse {U : Type u} (M : BoundedMetaDistinction U)
    (S : Finset U) (h_overflow : S.card > M.Capacity) :
    ∃ a b, a ∈ S ∧ b ∈ S ∧ Distinguishable a b ∧ ¬ObservableDistinction M a b := by
  -- 1. We have a map S -> Fin Capacity
  let f : S → Fin M.Capacity := fun x => M.observe x

  -- 2. Cardinality of domain (S) > cardinality of codomain (Capacity)
  have h_card : Fintype.card S > Fintype.card (Fin M.Capacity) := by
    simp
    exact h_overflow

  -- 3. Apply Pigeonhole Principle
  have exists_collision := Fintype.exists_ne_map_eq_of_card_lt f h_card

  -- 4. Extract witnesses
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, h_neq, h_eq⟩ := exists_collision

  -- 5. Construct proof
  use a, b
  refine ⟨ha, hb, ?_, ?_⟩
  · -- Distinguishable a b
    intro h_iden
    apply h_neq
    apply Subtype.ext
    exact h_iden
  · -- Not Observable (observe a = observe b)
    intro h_obs
    apply h_obs.1
    exact h_eq

/--
  The Expansion Principle:
  The universe can INCREASE its capacity over time (cosmic inflation).
-/
def ExpandedCapacity {U : Type u} (M : BoundedMetaDistinction U) (factor : Nat) (h_fac : factor ≥ 1) :
    BoundedMetaDistinction U where
  Allow := M.Allow
  Cost := M.Cost
  Capacity := M.Capacity * factor
  observe := fun u =>
    -- We can embed the old observation into the larger space
    let old_idx := M.observe u
    Fin.castLE (Nat.le_mul_of_pos_right _ (Nat.lt_of_succ_le h_fac)) old_idx
  cap_pos := Nat.mul_pos M.cap_pos (Nat.lt_of_succ_le h_fac)

/-! ## The Grand Unification -/

theorem unification_of_time_and_structure :
    ∀ (U : Type) (a b : U),
    (∃ M : MetaDistinction U, RealDistinction M a b) ↔
    Distinguishable a b := by
  intro U a b
  apply Iff.intro
  · intro h
    cases h with
    | intro M hreal =>
      exact hreal.2
  · intro hdist
    refine ⟨{ Allow := fun _ _ => True, Cost := fun _ _ => 0 }, ⟨True.intro, hdist⟩⟩

/--
  The Complete Picture:

  1. DISTINCTION exists (primitive)
  2. META-DISTINCTION constrains what can be observed
  3. CAPACITY limits how many distinctions fit in a structure
  4. OVERFLOW causes collapse → new emergent structure
  5. EXPANSION makes room for more distinctions

  This is the LOOP that drives reality.
-/
theorem the_complete_picture {U : Type*} [Fintype U] (M : BoundedMetaDistinction U) :
    M.Capacity < Fintype.card U → ∃ x y : U, x ≠ y ∧ M.observe x = M.observe y := by
  intro hcap
  -- Use pigeonhole: more elements than observation values
  have h_card_obs : Fintype.card (Fin M.Capacity) = M.Capacity := Fintype.card_fin M.Capacity
  -- If observe were injective, we'd have card U ≤ Capacity
  by_contra h_all
  push_neg at h_all
  -- h_all : ∀ x y, x ≠ y → M.observe x ≠ M.observe y
  -- This means M.observe is injective
  have hinj : Function.Injective M.observe := by
    intro x y heq
    by_contra hne
    exact h_all x y hne heq
  have := Fintype.card_le_of_injective M.observe hinj
  rw [h_card_obs] at this
  omega

end PhysicalLoF.Foundations
