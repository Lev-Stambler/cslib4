import Lake
open Lake DSL

package «cslib» {
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require llmstep from git
  "https://github.com/wellecks/llmstep"

@[default_target]
lean_lib «Cslib» {
  -- add any library configuration options here
}

lean_lib «BooleanAnalysis» {
  -- moreLinkArgs := #["-L./lake-packages/LeanInfer/build/lib", "-lonnxruntime", "-lstdc++"]
}
