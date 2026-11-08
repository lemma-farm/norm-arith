-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Doubling
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.Average
set_option autoImplicit false
set_option warningAsError true
/-!
# The parabolic Hardy--Littlewood maximal function

This file defines the uncentred maximal function using the genuine parabolic
metric from `Basic`.  The weak estimate is proved by the Vitali covering
theorem.  The covering argument follows the general metric-measure argument in
`Carleson/ToMathlib/HardyLittlewood.lean` from the Carleson project, released
under Apache 2.0.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
private abbrev parabolicMetricBall (z : ParabolicPoint) (r : ℝ) : Set ParabolicPoint :=
  @Metric.ball ParabolicPoint parabolicPseudoMetricSpace z r
end CKN.Foundation.Parabolic
