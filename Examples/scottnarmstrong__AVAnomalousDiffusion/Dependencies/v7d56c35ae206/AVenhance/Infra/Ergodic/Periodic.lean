-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.Homogenization.Ambient.Basic
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Periodicity for functions on Euclidean space

This local predicate records invariance under the integer lattice.  The
ergodic lemmas use it for scalar functions on `Vec d`.
-/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open MeasureTheory
noncomputable section
local instance avInfraErgodicPeriodicMeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicPeriodicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicPeriodicIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def latticeVector {d : ℕ} (k : Fin d → ℤ) : Homogenization.Vec d :=
  fun i => (k i : ℝ)
end
end AVenhance.Infra.Ergodic
