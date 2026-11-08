module
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.ProbabilityKernelAverage
public import Examples.pmaronow__arbitrary_rsb_palomar.Dependencies.ve2311756e7bd.GeneralDepthPaper.CompactTiltKernel
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option autoImplicit false
@[expose] public section
/-! The literal integral over the auxiliary tilt interval is a norm-one
bounded-function linear operator. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction
namespace GeneralDepthPaper
def unitTiltMeasure : Measure ℝ := volume.restrict (Icc (0:ℝ) 1)
instance : IsProbabilityMeasure unitTiltMeasure where
  measure_univ := by simp [unitTiltMeasure,Real.volume_Icc]
end GeneralDepthPaper
