-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v8c007b97386a.AVenhance.Statements.Section3.Flux
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `Khom` (Section3).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Homogenization
noncomputable section
namespace AVenhance
namespace Ingredients
variable {β : ℝ} (I : Ingredients β)
/-- `e.Kbarm.def` (label 2983): `K̄^κ_m := ∫_0^1 J^κ_m(t) dt`, as a matrix. -/
def Khom (κ : ℝ) (m : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  timeAvgMat fun t => I.flux κ m t
end Ingredients
end AVenhance
