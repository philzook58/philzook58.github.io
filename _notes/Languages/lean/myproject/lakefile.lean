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

require std from git "https://github.com/leanprover/std4" @ "main"
