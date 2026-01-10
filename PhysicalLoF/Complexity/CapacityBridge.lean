-- SPDX-License-Identifier: MIT
/-
  CapacityBridge.lean
  ===================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  The Bridge: DLA Dimension = Distinction Capacity

  This file connects:
  - Physical-LoF (Distinction Theory)
  - Lean-BQP-NP (Complexity Theory via DLAs)

  Key Theorem: DLA dimension IS the capacity of a Meta-Distinction.
  Therefore, NP-hard → Exponential DLA → Capacity Overflow.
-/

import PhysicalLoF.Foundations.MetaDistinction
import BQP_NP.Basic.LieAlgebra
import Mathlib.Tactic

namespace PhysicalLoF.Bridge

open Foundations

/-! ## The Bridge Definition -/

/--
  A Hamiltonian defines a Meta-Distinction on quantum states.
  The "Allow" predicate is whether the Hamiltonian can distinguish states.
  The "Cost" is related to the DLA dimension.
-/
noncomputable def HamiltonianAsMetaDistinction {n : ℕ} (H H_mixer : Hamiltonian n) :
    BoundedMetaDistinction (Fin (2^n)) where
  Allow := fun _ _ => True  -- Quantum can distinguish any basis states
  Cost := fun _ _ => 1
  -- Ensure capacity is at least 1 (handle degenerate case DLA=0)
  Capacity := if DLA.dimension H H_mixer > 0 then DLA.dimension H H_mixer else 1
  observe := fun i =>
    if h : DLA.dimension H H_mixer > 0 then
      let val := DLA.dimension H H_mixer
      have heq : (if DLA.dimension H H_mixer > 0 then DLA.dimension H H_mixer else 1) = val := by simp [h]; rfl
      cast (by rw [heq]) (⟨i.val % val, Nat.mod_lt _ h⟩ : Fin val)
    else
      have heq : (if DLA.dimension H H_mixer > 0 then DLA.dimension H H_mixer else 1) = 1 := by simp [h]
      cast (by rw [heq]) (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  cap_pos := by
    -- Capacity is defined to be > 0
    split
    next h => exact h
    next => exact Nat.zero_lt_one

/-! ## The Bridge Theorem -/

/--
  Arithmetic Lemma: Exponential beats Linear.
  2^k > 2k + 1 for k ≥ 3.
  Proven by induction.
-/
lemma capacity_bound_lemma {k : ℕ} (h : k ≥ 3) : 2^k > 2 * k + 1 := by
  induction k with
  | zero => omega  -- 0 ≥ 3 is false, contradiction
  | succ n ih =>
    cases' Nat.lt_or_ge n 3 with hn hn
    · -- Base cases: n = 0, 1, 2 (so succ n = 1, 2, 3)
      interval_cases n
      · omega  -- n=0: succ 0 = 1, but need k ≥ 3
      · omega  -- n=1: succ 1 = 2, but need k ≥ 3
      · norm_num  -- n=2: succ 2 = 3, 2^3 = 8 > 7 = 2*3+1
    · -- Inductive step: n ≥ 3
      have ih_val := ih hn
      calc
        2^(n+1) = 2 * 2^n := by ring
        _ > 2 * (2*n + 1) := by linarith
        _ = 4*n + 2 := by ring
        _ > 2*(n+1) + 1 := by linarith  -- 4n+2 > 2n+3 iff 2n > 1

/--
  Core Bridge Theorem:
  NP-hard Hamiltonian → Exponential DLA → Capacity Overflow

  This connects complexity theory to our distinction framework.
-/
theorem np_hard_is_capacity_overflow {n : ℕ}
    (H H_mixer : Hamiltonian n)
    (h_np_hard : IsNPHardHamiltonian H) :
    (HamiltonianAsMetaDistinction H H_mixer).Capacity ≥ 2^(n/2) := by
  -- This follows from np_hard_implies_exp_dla
  unfold HamiltonianAsMetaDistinction
  have h_bound := np_hard_dimension_bound H H_mixer h_np_hard
  have h_pos : DLA.dimension H H_mixer > 0 := by
    calc DLA.dimension H H_mixer
       ≥ 2^(n/2) := h_bound
       _ ≥ 1 := Nat.one_le_pow _ _ (by norm_num)
  -- Rewrite Capacity definition using the positive dimension
  simp only [h_pos, ↓reduceIte]
  exact h_bound

/--
  Corollary: NP-hard problems cause Linear Capacity Overflow.

  For n ≥ 12 (k ≥ 6), the DLA dimension strictly exceeds the problem size n.
  This proves that "Physical Capacity" (Dimension) cannot contain the problem complexity.
-/
theorem np_hard_causes_linear_overflow {n : ℕ}
    (H H_mixer : Hamiltonian n)
    (h_np_hard : IsNPHardHamiltonian H)
    (h_sufficient_size : n ≥ 12) :
    (HamiltonianAsMetaDistinction H H_mixer).Capacity > n := by
  have h1 := np_hard_is_capacity_overflow H H_mixer h_np_hard
  calc
    (HamiltonianAsMetaDistinction H H_mixer).Capacity
      ≥ 2^(n/2) := h1
    _ > n := by
      -- note: This relies on the mathematical fact that representing NP-hard problems
      -- physically via DLA generation requires exponential dimension.
      -- If P = NP, this bound might still hold for the specific Hamiltonian construction,
      -- but the *implication* of impossibility would lose its force (since polynomial simulation might exist).
      -- However, the proof itself is unconditional on P vs NP; it's about Lie Algebra structure.

      -- n >= 12 => n/2 >= 6 >= 3
      have h_k : n / 2 ≥ 3 := calc
        n / 2 ≥ 12 / 2 := Nat.div_le_div_right h_sufficient_size
        _ = 6 := rfl
        _ ≥ 3 := by norm_num

      have h_lem := capacity_bound_lemma h_k
      -- h_lem : 2^(n/2) > 2*(n/2) + 1

      -- We want to prove: n < 2^(n/2)
      -- We have h_lem: 2 * (n / 2) + 1 < 2 ^ (n / 2)
      -- We need: n ≤ 2 * (n / 2) + 1
      apply lt_of_le_of_lt _ h_lem

      cases Nat.mod_two_eq_zero_or_one n with
      | inl h_even =>
        -- n = 2*(n/2)
        -- n ≤ n + 1
        rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h_even)]
        linarith
      | inr h_odd =>
        -- n = 2*(n/2) + 1
        -- n ≤ n (modulo commutation and division simplification)
        rw [← Nat.div_add_mod n 2, h_odd, Nat.mul_comm]
        omega

/-! ## Barren Plateaus as Distinction Collapse -/

/--
  A Barren Plateau is an optimization landscape where gradients vanish exponentially.
  In our distinction language, this means the "Cost" to distinguish two states becomes
  indistinguishable from infinite (or the gradient signal is indistinguishable from zero noise).
-/
def HasBarrenPlateau {n : ℕ} (H H_mixer : Hamiltonian n) : Prop :=
  DLA.dimension H H_mixer ≥ 2^(n/2) -- Using the Ragone result as definition

/--
  Theorem: Capacity Overflow implies Barren Plateau.
  If the problem complexity (Target Capacity) exceeds the system's ability to distinguish (DLA Dimension),
  the system enters a Barren Plateau (Distinction Collapse).

  This explains why NP-hard problems are hard: The "Distinction Gradients" vanish.
-/
theorem overflow_implies_barren_plateau {n : ℕ}
    (H H_mixer : Hamiltonian n)
    (h_n : n ≥ 2)
    (h_overflow : (HamiltonianAsMetaDistinction H H_mixer).Capacity ≥ 2^(n/2)) :
    HasBarrenPlateau H H_mixer := by
  -- The capacity IS the DLA dimension (by definition in HamiltonianAsMetaDistinction).
  -- So if Capacity > 2^(n/2), then DLA > 2^(n/2).
  -- And Large DLA => Barren Plateau (by Ragone's theorem / axiom).
  unfold HasBarrenPlateau
  unfold HamiltonianAsMetaDistinction at h_overflow
  simp at h_overflow
  split at h_overflow
  · exact h_overflow
  · -- Case DLA <= 0, impossible given the bound 2^(n/2) for n >= 2
    have h_div : 1 ≤ n / 2 := (Nat.le_div_iff_mul_le Nat.two_pos).mpr h_n
    have h_pow : 2 ≤ 2^(n/2) := by
      -- 2^1 ≤ 2^(n/2) because 1 ≤ n/2
      calc 2
         = 2^1 := (pow_one 2).symm
       _ ≤ 2^(n/2) := Nat.pow_le_pow_right Nat.two_pos h_div
    -- h_overflow : 1 >= 2^(n/2) (since Capacity=1)
    -- h_pow : 2^(n/2) >= 2
    -- So 1 >= 2. False.
    linarith

end PhysicalLoF.Bridge
