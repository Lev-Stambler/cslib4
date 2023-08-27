import Lake
open Lake DSL


package «cslib» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Cslib» {
  -- add any library configuration options here
}

lean_lib «BooleanAnalysis» {
  -- add any package configuration options here
}