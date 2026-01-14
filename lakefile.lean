-- SPDX-License-Identifier: MIT
-- Copyright (C) 2026 Tan Jun Liang <junliang9339@hotmail.com>
-- Repository: https://github.com/poig/Lean-physical-laws-of-form

import Lake
open Lake DSL

package «physical-laws-of-form» where
  -- LeanCopilot removed - not installed

-- Mathlib for comprehensive mathematics (latest master)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

-- FormalizedFormalLogic for Gödel's theorems and logic foundations
require Foundation from git
  "https://github.com/FormalizedFormalLogic/Foundation" @ "master"

-- BQP-NP for complexity theory (DLA, Hamiltonians, NP-hardness)
-- Local dependency - bridges Distinction theory with Complexity theory
require BQP_NP from "../Lean-BQP-NP"
-- require BQP_NP from git
--   "https://github.com/poig/Lean-BQP-NP" @ "main"

lean_lib «PhysicalLoF» where
  -- add library configuration options here

@[default_target]
lean_exe «physical-laws-of-form» where
  root := `Main

-- Buildable core target focused on AI-facing theory.
-- Usage: `lake build physical-laws-of-form-ai`
lean_exe «physical-laws-of-form-ai» where
  root := `AIMain
