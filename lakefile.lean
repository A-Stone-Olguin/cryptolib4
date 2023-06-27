import Lake
open Lake DSL

require mathlib from git
    "https://github.com/leanprover-community/mathlib4"

package «cryptolib4» {
  -- add package configuration options here
}

lean_lib «Cryptolib4» {
  -- add library configuration options here
}

@[default_target]
lean_exe «cryptolib4» {
  root := `Main
}
