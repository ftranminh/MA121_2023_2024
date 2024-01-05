import Lake
open Lake DSL

package «tuto» {
  -- add any package configuration options here
  moreLeanArgs := #[
    "-DautoImplicit=false",
    "-Dpp.unicode.fun=true" --,  -- pretty-prints `fun a ↦ b`
    --"-Dpush_neg.use_distrib=true"
  ]
}

lean_lib Esisar

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Tuto» {
  -- add any library configuration options here
}
