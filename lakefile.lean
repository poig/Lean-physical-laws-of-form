import Lake
open Lake DSL

package «physical-laws-of-form» where
  -- add package configuration options here

lean_lib «PhysicalLoF» where
  -- add library configuration options here

@[default_target]
lean_exe «physical-laws-of-form» where
  root := `Main
