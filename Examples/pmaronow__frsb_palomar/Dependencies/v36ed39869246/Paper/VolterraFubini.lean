module
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
@[expose] public section
/-! # Changing the order of integration on the Volterra time triangle -/
open Set MeasureTheory
namespace Paper
noncomputable def parisiTimeMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
instance : IsFiniteMeasure parisiTimeMeasure := by
  unfold parisiTimeMeasure
  infer_instance
end Paper
