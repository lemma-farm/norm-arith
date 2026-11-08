-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vd8c2bc0ddceb.AVenhance.Statements.Roots.UnitCube
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `IsPeriodicH1With` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Periodic `H¹` with an explicit gradient `Du`. -/
def IsPeriodicH1With (u : Vec 2 → ℝ) (Du : Vec 2 → Vec 2) : Prop :=
  IsZ2Periodic u ∧ IsZ2Periodic Du ∧ MemL2On unitCube u ∧ GradMemL2On unitCube Du ∧
    HasWeakGradientOn Set.univ u Du
end AVenhance
