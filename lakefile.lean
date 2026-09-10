import Lake
open Lake DSL

package «OneMfld» {
  -- add any package configuration options here
}

-- Pinned to the parent of the `v4.33.1` release tag: the same source, but a
-- commit on mathlib master (release-tag commits are not ancestors of master,
-- which the Palomar registry requires). Toolchain accordingly `v4.33.0`.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

@[default_target]
lean_lib «OneMfld» {
  -- add any library configuration options here
}

/-- Palomar statement module: `Challenge.lean` at the repository root. -/
@[default_target]
lean_lib «Challenge» {
}

/-- Palomar proof module: `Solution.lean` at the repository root. -/
@[default_target]
lean_lib «Solution» {
}
