-- SPDX-License-Identifier: MIT
/-
  PhysicalLoF.lean
  ================
  Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
  Repository: https://github.com/poig/Lean-physical-laws-of-form

  The Physical Laws of Form

  Foundation:
  1. Distinction       (The Primitive)
  2. Meta-Distinction  (The Unified Structure)
  3. Transformation    (Dynamics)

  The Grand Trilogy:
  4. Logic (Gödel)     -> PhysicalLoF.Logic
  5. Complexity (P/NP) -> PhysicalLoF.Complexity
  6. Emergence (Loop)  -> PhysicalLoF.Foundations.Emergence
-/

import PhysicalLoF.Foundations.Distinction
import PhysicalLoF.Foundations.Transformation
import PhysicalLoF.Foundations.MetaDistinction
import PhysicalLoF.Foundations.Collapse
import PhysicalLoF.Foundations.Existence
import PhysicalLoF.Foundations.Optimality
import PhysicalLoF.Foundations.LawsOfForm
import PhysicalLoF.Foundations.Emergence
import PhysicalLoF.Foundations.SelfGrounding      -- Self-reference
import PhysicalLoF.Foundations.SelfValidation     -- Self-validation
import PhysicalLoF.Foundations.CategoryTheory    -- Initial object
import PhysicalLoF.Foundations.Arithmetic        -- Peano axioms
import PhysicalLoF.Foundations.RelatedTheories   -- Quasi-Set, HoTT, etc.
import PhysicalLoF.Foundations.VolumeOfVoid      -- The Volume of Zero is One

import PhysicalLoF.ImpossibilityTheorems
import PhysicalLoF.Complexity.ComplexityBarrier
import PhysicalLoF.Complexity.CapacityBridge  -- Bridge to BQP-NP
import PhysicalLoF.Complexity.Automata        -- Myhill-Nerode
import PhysicalLoF.Complexity.ChomskyHierarchy -- Distinction capacity hierarchy
-- TEMPORARILY DISABLED: Foundation package conflicts with Mathlib on Matrix.map
-- See: https://github.com/FormalizedFormalLogic/Foundation/issues
-- import PhysicalLoF.Logic.Goedel
import PhysicalLoF.Foundations.Combinatorics  -- Multinomial
import PhysicalLoF.Foundations.Galois         -- Algebraic Indistinguishability
import PhysicalLoF.Cybernetica                -- The Grand Conjecture

namespace PhysicalLoF

open Foundations
open Complexity
open Cybernetica
-- open Logic  -- Disabled with Goedel.lean

end PhysicalLoF
