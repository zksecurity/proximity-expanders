import Lake
open Lake DSL

package ldpc where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"
require Arklib from git
  "https://github.com/Verified-zkEVM/ArkLib.git" @ "v4.35.0"

@[default_target]
lean_lib LDPC
