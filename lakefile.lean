import Lake
open Lake DSL

package ldpc where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"
require Arklib from git
  "https://github.com/Verified-zkEVM/ArkLib.git" @ "65dea00c87d002f874c4cd0e90dd809fd80b5a65"

@[default_target]
lean_lib LDPC
