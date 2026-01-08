import Lake
open Lake DSL

package «physical-laws-of-form» where
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]

-- Mathlib for comprehensive mathematics (latest master)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

-- FormalizedFormalLogic for Gödel's theorems and logic foundations
-- Note: May need version alignment; uncomment when ready to integrate
-- require Foundation from git
--   "https://github.com/FormalizedFormalLogic/Foundation" @ "master"

lean_lib «PhysicalLoF» where
  -- add library configuration options here

@[default_target]
lean_exe «physical-laws-of-form» where
  root := `Main
