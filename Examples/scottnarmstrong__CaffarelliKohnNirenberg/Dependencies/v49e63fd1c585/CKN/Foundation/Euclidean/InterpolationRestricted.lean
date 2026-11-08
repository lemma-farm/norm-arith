-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.Interpolation
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationLpChar
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationTruncBounds
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.InterpolationIndicator
set_option autoImplicit false
set_option warningAsError true
/-!
# Marcinkiewicz interpolation for operators defined on a restricted class

`interpolation_weak11_strong22` (`Interpolation.lean`) assumes sublinearity, the
weak `(1,1)` bound and the strong `(2,2)` bound for *every* measurable function.
A Calderón--Zygmund operator obtained as the `L^2`-extension of a singular
integral does not satisfy such hypotheses: outside `L^2` it is only defined by a
convention, so the endpoint estimates hold only on the classes on which the
operator is genuinely defined.

This file proves the same conclusion, with the same constant
`p · 2^p · (A₁/(p-1) + A₂²/(2-p))` for `1 < p < 2`, from hypotheses restricted to
the classes actually visited by the truncation argument.  Two variants are
provided:

* `interpolation_weak11_strong22_of_classes`, whose endpoint hypotheses are
  assumed for integrable functions (weak `(1,1)`) and for `L^2` functions
  (strong `(2,2)`), with sublinearity only for an (integrable, `L^2`) pair;
* `interpolation_weak11_strong22_of_l2_classes`, whose hypotheses are in
  addition confined to `L^2` inputs throughout, which is the form available for
  an operator constructed as an `L^2`-extension and only later extended to `L^p`
  by density.

Splitting `f` at the level `t/2` produces the two pieces `f·1_{|f| > t/2}` and
`f·1_{|f| ≤ t/2}`.  For `f ∈ L^p` with `1 < p < 2` the first is integrable and
the second lies in `L^2`; these two facts, proved here from the pointwise bounds
of `InterpolationTruncBounds.lean`, are what lets the restricted hypotheses be
applied.  Everything else is the argument of `Interpolation.lean`.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
/-! ### The two truncations of an `L^p` function -/
end CKN.Foundation.Euclidean
