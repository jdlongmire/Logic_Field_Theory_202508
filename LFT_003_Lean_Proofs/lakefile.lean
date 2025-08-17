import Lake
open Lake DSL

package LFT where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "308445d7985027f538e281e18df29ca16ede2ba3"

lean_lib LFT where
  srcDir := "."
  roots := #[`Basic, `Core.D01_Admissibility, `Core.D02_ComplexNecessity, `Core.D03_UnitaryEvolution, `Core.D04_BornRule, `Core.D05_StrainWeights]

@[default_target]
lean_exe App where
  root := `Main
