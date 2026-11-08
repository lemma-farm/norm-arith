-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Foundation.Parabolic.Campanato
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vb5f3fee7f2c6.CKN.Statements.ParabolicHolderVecOn
set_option autoImplicit false
set_option warningAsError true
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
def parabolicCampanatoHolderConstant (α p : ℝ) : ℝ :=
  (2 * parabolicCampanatoTailConstant α + 1) *
    (2 : ℝ) ^ (5 / p) * (8 : ℝ) ^ α
end CKN.Foundation.Parabolic
