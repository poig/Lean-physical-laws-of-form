-- SPDX-License-Identifier: MIT
/-
  Structure.lean
  ==============
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  The Emergence of Structure.

  We derive Geometry (Vertex, Edge, Face) from Foundation (Stability, Transformation).

  Definitions:
  - Vertex: A Stable Pattern (Fixed Point of Recursive Observation).
  - Edge: A Transformation between Stable Patterns.
  - Face: A Commutative Diagram (Closure of Transformations).
-/

import PhysicalLoF.Foundations.System.Emergence
import PhysicalLoF.Foundations.System.Transformation
import PhysicalLoF.Foundations.Math.Combinatorics
import PhysicalLoF.Foundations.Core.SelfGrounding
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Card

namespace PhysicalLoF.Foundations

variable [CompleteLattice Concept] [Fintype Concept] [DecidableEq Concept]

/-! ## 1. Vertex: The Stable Point -/

/--
  A Vertex is a Fixed Point of the emergent order.
  It is a distinction that persists under the system's dynamics.
-/
structure Vertex (T : Concept →o Concept) where
  pattern : StablePattern (Classical.choose (selection_principle T)) T

/-! ## 2. Edge: The Relation -/

/-- An Edge is a transformation that maps one stable state to another. -/
structure Edge (src dst : Concept) where
  transform : Transformation src dst

/-! ## 3. Face: The Closure -/

/-- A Face is a cycle of edges that commutes to Identity. -/
structure Face {v : Concept} (loop : Endomorphism v) where
  is_closed : loop = idTransform v

/-! ## 4. The Genesis Theorems (Existence) -/

/--
  **Genesis Theorem 1: Vertices MUST Exist**
  In any Finite, Complete Universe with dynamics T,
  Vertices (Stable Points) MUST exist.
-/
theorem vertices_must_exist (T : Concept →o Concept) : Nonempty (Vertex T) := by
  have h_loop := TheLoop T
  obtain ⟨p, hp⟩ := h_loop
  have stable : StablePattern (Classical.choose (selection_principle T)) T :=
    structure_emerges_from_stability T |> Classical.choice
  exact ⟨⟨stable⟩⟩

/-! ## 5. Natural Emergence of Structure (Combinatorial Capacity) -/

/--
  **The Orbit of a Concept**
  The set of all states reachable from `start` under dynamics `T`.
-/
def Orbit (T : Concept →o Concept) (start : Concept) : Set Concept :=
  { x | ∃ n : ℕ, (T^[n]) start = x }

/--
  **Structural Capacity**
  We define the "size" of a structure not by counting, but by **Arrangement**.
  The Capacity is the number of Distinguishable Arrangements of the Orbit.

  (See `Foundations/Combinatorics.lean`)
-/
noncomputable def OrbitCapacity (T : Concept →o Concept) (start : Concept) : ℕ :=
  let n := Set.ncard (Orbit T start)
  n.factorial

/--
  **Emergence Level 1: The One (Vertex)**
  A Vertex has an Orbit of size 1.
  The number of arrangements of 1 item is 1! = 1.
-/
-- omit [Fintype Concept] [DecidableEq Concept] in
theorem vertex_has_minimal_capacity (T : Concept →o Concept) :
    OrbitCapacity T (Classical.choose (selection_principle T)) = 1 := by
  let p := Classical.choose (selection_principle T)
  have h_fixed : T p = p := Classical.choose_spec (selection_principle T)

  -- The orbit is {p}
  have h_orbit : Orbit T p = {p} := by
    ext x
    constructor
    . intro h; obtain ⟨n, hn⟩ := h
      have h_iter : ∀ k, (T^[k]) p = p := by
        intro k; induction k with | zero => rfl | succ _ ih' => rw [Function.iterate_succ_apply', ih', h_fixed]
      rw [h_iter n] at hn
      exact hn.symm
    . intro h; rw [h]; use 0; rfl

  unfold OrbitCapacity
  have h_card : Set.ncard (Orbit T p) = 1 := by
    rw [h_orbit]
    rw [Set.ncard_singleton]

  rw [h_card]
  exact Nat.factorial_one

/--
  **Emergence Level 2: The Many (Edge)**
  If there is *any* transformation that moves (Edge),
  The Orbit has size >= 2.
  The number of arrangements is >= 2! = 2.
-/
theorem edge_implies_higher_capacity (T : Concept →o Concept)
    (u v : Concept) (h_diff : u ≠ v) (h_edge : T u = v) :
    OrbitCapacity T u ≥ 2 := by
  have h_u : u ∈ Orbit T u := ⟨0, rfl⟩
  have h_v : v ∈ Orbit T u := ⟨1, h_edge⟩

  unfold OrbitCapacity

  -- We just need to show card >= 2
  have h_card : Set.ncard (Orbit T u) ≥ 2 := by
    have h_subset : {u, v} ⊆ Orbit T u := by
      intro x hx
      cases hx with
      | inl hu => rw [hu]; exact h_u
      | inr hv => rw [hv]; exact h_v

    have h_pair_card : Set.ncard {u, v} = 2 := by
      rw [Set.ncard_insert_of_notMem]
      . rw [Set.ncard_singleton]
      . rw [Set.mem_singleton_iff]; exact h_diff

    calc 2 = Set.ncard {u, v} := h_pair_card.symm
         _ ≤ Set.ncard (Orbit T u) := Set.ncard_le_ncard h_subset (Set.toFinite (Orbit T u))

  -- Factorial is monotonic: 2 <= n -> 2! <= n!
  apply Nat.monotone_factorial h_card


/--
  **Emergence Level 3: The Closure (Cycle)**
  A "Face" is a closed orbit. In general, a cycle of length n
  generates a capacity of n! (the number of ways to arrange the cycle distinctively).

  This is where "Higher Dimensions" emerge.
  - Triangle (3-Cycle) -> Capacity 6.
  - Tetrahedron (4-Cycle) -> Capacity 24.
  - N-Cycle -> Capacity N!.
-/
theorem cycle_implies_n_capacity (T : Concept →o Concept) (c : Concept)
    (n : ℕ)
    (h_cycle_len : Set.ncard (Orbit T c) = n) :
    OrbitCapacity T c = n.factorial := by
  unfold OrbitCapacity
  rw [h_cycle_len]

end PhysicalLoF.Foundations
