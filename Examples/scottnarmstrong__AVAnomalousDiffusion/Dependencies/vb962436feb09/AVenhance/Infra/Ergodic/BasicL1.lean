-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vb962436feb09.AVenhance.Infra.Ergodic.Periodic
public import Mathlib
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Fourier coefficient bounds for the basic ergodic estimate -/
@[expose] public section
namespace AVenhance.Infra.Ergodic
open MeasureTheory
noncomputable section
local instance avInfraErgodicBasicL1MeasureSpace1 : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicBasicL1MeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicBasicL1IsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
def IsFastFrequency {d : ℕ} (N : ℕ) (k : Fin d → ℤ) : Prop :=
  ∀ i, (N : ℤ) ∣ k i
instance fastFrequencyDecidable {d N : ℕ} (k : Fin d → ℤ) :
    Decidable (IsFastFrequency N k) := by
  unfold IsFastFrequency
  infer_instance
end
end AVenhance.Infra.Ergodic
