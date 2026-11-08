-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.AVenhance.Statements.Section3.SpaceAvgMat
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `timeAvgMat` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Homogenization
noncomputable section
namespace AVenhance
/-- Entrywise `⟨⟨F⟩⟩ = ∫_0^1 F dt` (line 922; `e.Kbarm.def`, label 2983: `∫_0^1 J dt = ⟨⟨·⟩⟩`). -/
def timeAvgMat (F : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ∫ t in (0 : ℝ)..1, F t i j
end AVenhance
