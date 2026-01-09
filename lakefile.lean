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

-- require Foundation from git
--   "https://github.com/poig/Lean-BQP-NP" @ "master"

lean_lib «PhysicalLoF» where
  -- add library configuration options here

@[default_target]
lean_exe «physical-laws-of-form» where
  root := `Main
