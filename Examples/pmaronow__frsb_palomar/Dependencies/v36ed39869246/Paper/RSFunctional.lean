module
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.Gaussian
public import Examples.pmaronow__frsb_palomar.Dependencies.v36ed39869246.Paper.Variational
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
@[expose] public section
/-!
# Concrete Parisi measures and replica-symmetric functional

`ParisiMeasure` is the actual type of probability measures on `[0,1]`.
The functional is parameterized by a potential `u`; this file does not claim
that an arbitrary supplied potential is the weak Parisi PDE solution.
-/
open Set MeasureTheory
namespace Paper
abbrev Overlap := Set.Icc (0 : ℝ) 1
abbrev ParisiMeasure := ProbabilityMeasure Overlap
noncomputable def parisiCDF (μ : ParisiMeasure) (s : ℝ) : ℝ :=
  ((μ : Measure Overlap) {t : Overlap | (t : ℝ) ≤ s}).toReal
lemma hasDerivAt_log_cosh (x : ℝ) :
    HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))
end Paper
