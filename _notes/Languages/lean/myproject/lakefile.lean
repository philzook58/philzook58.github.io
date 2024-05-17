import Lake
open Lake DSL

package «myproject» {
  -- add package configuration options here
}

lean_lib «Myproject» {
  -- add library configuration options here
}

@[default_target]
lean_exe «myproject» {
  root := `Main
}

require std from git "https://github.com/leanprover/std4" @ "v4.7.0"
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.7.0"
require aesop from git "https://github.com/JLimperg/aesop" @ "v4.7.0"
--require auto from git "https://github.com/leanprover-community/lean-auto.git" @ "main"
--require Duper from git "https://github.com/leanprover-community/duper.git" @ "main"
-- You should replace v0.0.3 with the latest version published under Releases
-- require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.35"
