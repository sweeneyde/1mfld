import Lake
open Lake DSL

package «OneMfld» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

@[default_target]
lean_lib «OneMfld» {
  -- add any library configuration options here
}
