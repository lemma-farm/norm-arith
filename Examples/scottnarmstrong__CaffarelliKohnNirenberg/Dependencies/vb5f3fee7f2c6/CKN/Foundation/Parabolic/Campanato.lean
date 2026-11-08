-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Holder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Doubling
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Integration.Slice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
set_option autoImplicit false
set_option warningAsError true
/-!
# Campanato oscillations on parabolic cylinders

The `L^p` oscillation of a function on a parabolic cylinder, the Campanato
bound it satisfies on a region, the tail constant of the dyadic geometric
series, and the comparison of the average of `|f|` on a subset with the
average on the ambient set.  The oscillations use genuine space-time averages.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
def parabolicCampanatoTailConstant (α : ℝ) : ℝ :=
  1 / (1 - (2 : ℝ) ^ (-α))
end CKN.Foundation.Parabolic
