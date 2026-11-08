-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.KernelBasic
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option warningAsError true
namespace CKN
open MeasureTheory Metric
open scoped ENNReal NNReal Pointwise
/-!
# Segment change of variables for Riesz-kernel Poincare integrals

Pulls the segment-blend integrand `φ(segmentBlend x t y) * ‖x - y‖` through a
dilation change of variables into an integral against `(1 - t)^(-(d+1))`,
optionally localised to a closed ball around `x`.
-/
section SegmentChangeOfVariables
set_option linter.unusedSectionVars false
variable {d : ℕ} [NeZero d]
/-- File-level typeclass cache for `Nontrivial (Vec d)` under `[NeZero d]`.
Repeated inference of this head class dominates the file (~7s cumulative
typeclass before the cache). The cache fires during elaboration of theorems
in this section even when their type signatures don't use `[NeZero d]`,
because the variable-block instance is in scope for typeclass search. -/
private instance instNontrivialVecSegCV (d : ℕ) [NeZero d] :
    Nontrivial (Vec d) := inferInstance
end SegmentChangeOfVariables
end CKN
