-- SPDX-License-Identifier: MIT
/-
  Topology.lean
  =============

  Basic building blocks for composing agents into different network topologies.
  This is the "before scaling up" layer: nodes, edges, message passing stubs.
-/

import PhysicalLoF.AI.Observation
import PhysicalLoF.AI.Policy
import PhysicalLoF.AI.Governor

namespace PhysicalLoF.AI.Topology

open PhysicalLoF.Foundations
open PhysicalLoF.AI

/-! ## Node: A single agent with observation + policy + optional governor -/

/--
A Node is a single agent unit with:
- its own observation capacity
- a policy
- an optional safety governor
-/
structure Node (U : Type u) (A : Type v) where
  observer : BoundedMetaDistinction U
  policy : Policy U A
  governor : Option (Governor A)
  /-- Policy must respect observation -/
  policy_valid : RespectsObs observer policy

/-- The effective action of a node: policy output, possibly clamped. -/
def Node.act {U : Type u} {A : Type v} (n : Node U A) (u : U) : A :=
  match n.governor with
  | none => n.policy u
  | some g => g.clamp (n.policy u)

/-! ## Edge: Communication channel between nodes -/

/--
An edge represents a communication channel from one node's output to another's input.
The channel may have its own capacity limit (lossy communication).
-/
structure Edge (A : Type u) where
  /-- Channel capacity: how many distinct messages can be transmitted -/
  capacity : Nat
  /-- The channel encoding: maps output to a finite channel symbol -/
  encode : A → Fin capacity
  /-- Capacity must be positive -/
  cap_pos : capacity > 0

/-- Two messages are channel-equivalent if they encode to the same symbol. -/
def Edge.equiv {A : Type u} (e : Edge A) (a₁ a₂ : A) : Prop :=
  e.encode a₁ = e.encode a₂

/-! ## Simple Topologies -/

/-- A chain of nodes: output of node i feeds input of node i+1. -/
def Chain (U : Type u) (A : Type v) := List (Node U A)

/-- A tree: one root node, multiple children. -/
inductive Tree (U : Type u) (A : Type v)
  | leaf (n : Node U A)
  | branch (n : Node U A) (children : List (Tree U A))

/-- A fully connected layer: all nodes in the layer see all outputs from previous layer. -/
structure Layer (U : Type u) (A : Type v) where
  nodes : List (Node U A)

/--
A simple feed-forward network: a sequence of layers.
Each layer's output is broadcast to all nodes in the next layer.
-/
def FeedForward (U : Type u) (A : Type v) := List (Layer U A)

/-! ## Recurrent / Self-loop -/

/--
A recurrent node: its output feeds back as part of its input (after one time step).
This is a stub; full dynamics need a time-indexed semantics.
-/
structure RecurrentNode (U : Type u) (A : Type v) where
  node : Node U A
  /-- Feedback channel from output to input -/
  feedback : Edge A

/-! ## Hierarchy (for "human-special" recursion)

A hierarchical structure: meta-level controls object-level.
This captures the "temporal depth" / "optimizer stack" idea from Intelligence.lean.

TODO: Add inductive Hierarchy definition once toolchain issue is resolved.
For now, we provide a simple two-level version.
-/

/-- A two-level hierarchy: one meta-controller over one base agent. -/
structure TwoLevelHierarchy (U : Type u) (A : Type v) where
  controller : Node U A
  base : Node U A

/-- Depth of a two-level hierarchy is always 1. -/
def TwoLevelHierarchy.depth {U : Type u} {A : Type v} (_ : TwoLevelHierarchy U A) : Nat := 1

end PhysicalLoF.AI.Topology
