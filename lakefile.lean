import Lake
open Lake DSL

package playground

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "d72a3c31ca863b32dfcb079f8ceef029123af9f0"

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "1f22a4f44c1726b61fab3c2c75e0651f35c795dc"

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
