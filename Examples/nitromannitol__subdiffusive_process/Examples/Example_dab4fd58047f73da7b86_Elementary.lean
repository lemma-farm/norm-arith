module
public import Examples.nitromannitol__subdiffusive_process.Dependencies.v7b3498f0da44.SubdiffusiveProcess.ResponseMoments.Forms
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Response moment elementary estimates

Small deterministic facts used by the resampling and comparison chain of
`mfd:sec-resampling`.

* the ramp `χ_{a,b}` of `mfd:sec-resampling` and its two endpoint values;
* `(x+y)^2 ≤ 2x^2 + 2y^2`, `mfd:sec-resampling`;
* the geometric sums used for the all-chain tail, `mfd:sec-resampling`;
* the Efron--Stein sum of `mfd:sec-resampling`.
-/
open Finset Filter Topology
noncomputable section
namespace SubdiffusiveProcess
namespace ResponseMoments
theorem abs_ramp_sub_ramp_le {a b x y : ℝ} (hab : a < b) :
    |ramp a b x - ramp a b y| ≤ |x - y| / (b - a) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hmin : |min 1 (max 0 ((x - a) / (b - a))) - min 1 (max 0 ((y - a) / (b - a)))|
      ≤ |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := by
    have h := abs_min_sub_min_le_max (1:ℝ) (max 0 ((x - a) / (b - a))) 1
      (max 0 ((y - a) / (b - a)))
    have heq : max |(1:ℝ) - 1| |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))|
        = |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := by
      simp
    rwa [heq] at h
  have hmax : |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))|
      ≤ |(x - a) / (b - a) - (y - a) / (b - a)| := by
    have h := abs_max_sub_max_le_max (0:ℝ) ((x - a) / (b - a)) 0 ((y - a) / (b - a))
    have heq : max |(0:ℝ) - 0| |(x - a) / (b - a) - (y - a) / (b - a)|
        = |(x - a) / (b - a) - (y - a) / (b - a)| := by
      simp
    rwa [heq] at h
  have huv : (x - a) / (b - a) - (y - a) / (b - a) = (x - y) / (b - a) := by
    rw [← sub_div]; ring
  have habs : |(x - a) / (b - a) - (y - a) / (b - a)| = |x - y| / (b - a) := by
    rw [huv, abs_div, abs_of_pos hba]
  calc |ramp a b x - ramp a b y|
      = |min 1 (max 0 ((x - a) / (b - a))) - min 1 (max 0 ((y - a) / (b - a)))| := rfl
    _ ≤ |max 0 ((x - a) / (b - a)) - max 0 ((y - a) / (b - a))| := hmin
    _ ≤ |(x - a) / (b - a) - (y - a) / (b - a)| := hmax
    _ = |x - y| / (b - a) := habs
end ResponseMoments
end SubdiffusiveProcess
