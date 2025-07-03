import Lake
open Lake DSL

package Kernel where
  -- A minimal Lean package inside artifact/proofs
  moreLeanArgs := #[]

require mathlib from
  git "https://github.com/leanprover-community/mathlib4" @ "v4.2.0"

lean_lib Kernel.Basic where
  srcDir := "./" 