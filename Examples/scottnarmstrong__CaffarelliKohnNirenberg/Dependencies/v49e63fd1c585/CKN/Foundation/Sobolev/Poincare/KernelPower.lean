-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.KernelTime
set_option autoImplicit false
set_option warningAsError true
namespace CKN
open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise
/-!
# Weighted and Riesz power-mean bounds for the Poincare kernel integrand

First: a Hölder-type weighted power-mean inequality used to convert the
interval integral into an `L^p` bound.
Second: the final convex-domain Riesz-kernel bounds used by the Poincare
estimates.
-/
section WeightedPowerMean
end WeightedPowerMean
section RieszPowerMean
variable {d : ℕ} [NeZero d]
/-- Cache `Nontrivial (Vec d)` once per section. -/
private instance instNontrivialVecRiesz : Nontrivial (Vec d) := inferInstance
end RieszPowerMean
end CKN
