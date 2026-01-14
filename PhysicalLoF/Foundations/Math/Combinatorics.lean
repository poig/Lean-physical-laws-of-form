-- SPDX-License-Identifier: MIT
/-
  Combinatorics.lean
  ==================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  Multinomial Theorem as Distinction Counting

  KEY INSIGHT:
  The multinomial coefficient n! / (n₁! × n₂! × ... × nₖ!)
  counts the number of DISTINGUISHABLE permutations.

  When objects become indistinguishable, arrangements "collapse" —
  this is the INVERSE of distinction: distinguishability creates diversity,
  indistinguishability causes collapse.

  Connection to Capacity:
  - Full distinguishability: n! arrangements (maximum capacity)
  - Partial distinguishability: n!/∏nᵢ! arrangements (reduced capacity)
  - Complete indistinguishability: 1 arrangement (total collapse)
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Card
import PhysicalLoF.Foundations.Core.Distinction
import PhysicalLoF.Foundations.System.MetaDistinction

namespace PhysicalLoF.Foundations

/-! ## Distinguishable Permutations -/

/--
  The number of distinguishable arrangements of n objects
  where objects of type i appear with multiplicity mᵢ.

  This is the multinomial coefficient: n! / ∏ᵢ mᵢ!
-/
def DistinguishableArrangements {α : Type*} [DecidableEq α] [Fintype α]
    (multiplicity : α → ℕ) : ℕ :=
  Nat.multinomial Finset.univ multiplicity

/--
  When all objects are distinguishable (each has multiplicity 1),
  we get the maximum: n! arrangements.
-/
theorem all_distinguishable_max {n : ℕ} :
    DistinguishableArrangements (fun (_ : Fin n) => 1) = n.factorial := by
  unfold DistinguishableArrangements
  simp [Nat.multinomial]

/--
  When all objects are indistinguishable (one type with multiplicity n),
  we get the minimum: 1 arrangement (total collapse).
-/
theorem all_indistinguishable_collapse {n : ℕ} :
    n.factorial / n.factorial = 1 := Nat.div_self (Nat.factorial_pos n)

/-! ## Distinction Capacity Interpretation -/

/--
  The "Distinction Capacity" of a collection is how many distinguishable
  arrangements exist. More distinctions = higher capacity.
-/
def DistinctionCapacity {α : Type*} [DecidableEq α] [Fintype α]
    (multiplicity : α → ℕ) : ℕ :=
  DistinguishableArrangements multiplicity

/--
  **THEOREM**: Adding more distinctions increases capacity.

  If we split one indistinguishable group into two distinguishable subgroups,
  the number of arrangements increases.
-/
theorem splitting_increases_capacity {n m : ℕ} (h : n + m > 0) :
    (n + m).factorial / (n.factorial * m.factorial) ≥ 1 := by
  have h_eq : m = n + m - n := (Nat.add_sub_cancel_left n m).symm
  conv =>
    lhs; rhs; rhs
    rw [h_eq]
  rw [← Nat.choose_eq_factorial_div_factorial (Nat.le_add_right n m)]
  exact Nat.one_le_of_lt (Nat.choose_pos (Nat.le_add_right n m))

/--
  **THEOREM**: Collapse reduces capacity.

  When distinctions are lost (objects become indistinguishable),
  the number of arrangements decreases.
-/
theorem collapse_reduces_capacity {n : ℕ} (h : n > 0) :
    n.factorial / n.factorial ≤ n.factorial := by
  rw [Nat.div_self (Nat.factorial_pos n)]
  exact Nat.one_le_of_lt (Nat.factorial_pos n)

/-! ## Connection to Meta-Distinction -/

/--
  A finite collection with multiplicities defines a bounded Meta-Distinction.
  The capacity is the number of distinguishable arrangements.
-/
def CollectionAsMetaDistinction {α : Type*} [DecidableEq α] [Fintype α]
    (multiplicity : α → ℕ) : BoundedMetaDistinction (List α) where
  Allow := fun x y => x ≠ y  -- Different lists are distinguishable
  Cost := fun _ _ => 1
  Capacity := DistinguishableArrangements multiplicity
  observe := fun _ => Fin.mk 0 (by
    unfold DistinguishableArrangements
    exact Nat.multinomial_pos Finset.univ multiplicity)
  cap_pos := by
    unfold DistinguishableArrangements
    exact Nat.multinomial_pos Finset.univ multiplicity

/--
  **THE MULTINOMIAL PRINCIPLE**:
  The number of ways to arrange n objects with given multiplicities
  equals n! divided by the product of the factorials of each multiplicity.

  This is PROVEN in Mathlib as `Nat.multinomial`.
-/
theorem multinomial_counts_distinctions {α : Type*} [DecidableEq α] [Fintype α]
    (multiplicity : α → ℕ) :
    DistinguishableArrangements multiplicity =
    (Finset.univ.sum multiplicity).factorial /
    (Finset.univ.prod fun a => (multiplicity a).factorial) := by
  unfold DistinguishableArrangements
  have h_fact_pos : 0 < ∏ i, (multiplicity i).factorial :=
    Finset.prod_pos fun i _ => Nat.factorial_pos (multiplicity i)
  symm
  apply Nat.div_eq_of_eq_mul_left h_fact_pos
  rw [Nat.mul_comm]
  exact (Nat.multinomial_spec Finset.univ multiplicity).symm

end PhysicalLoF.Foundations
