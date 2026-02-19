import Lake
open Lake DSL

package playground

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "main"

require Paperproof from git
  "https://github.com/Paper-Proof/paperproof.git" @"main"/"lean"

@[default_target]
lean_lib proofs

lean_exe runLinter where
  root := `scripts.run_linter
  supportInterpreter := true

set_option pp.unicode.fun true
set_option autoImplicit true
set_option relaxedAutoImplicit false
