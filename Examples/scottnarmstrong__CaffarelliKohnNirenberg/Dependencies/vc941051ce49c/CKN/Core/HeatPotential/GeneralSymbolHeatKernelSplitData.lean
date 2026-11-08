-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Core.HeatPotential.GeneralSymbolPairings
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Core.HeatPotential.GeneralSymbol
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Heat.CausalDistribution
set_option autoImplicit false
set_option warningAsError true
open scoped BigOperators ENNReal NNReal Topology Distributions
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Core.HeatPotential
open CKN.Foundation.Euclidean CKN.Foundation.Heat CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Morrey
open CKN.Core.HeatPotential
/- The smooth symbol class used by the split node. -/
def multiplierHeatShellSet (z : ParabolicPoint) (r : ℝ) (j : ℕ) : Set ParabolicPoint :=
  Metric.ball z ((2 : ℝ) ^ (j + 1) * r) \
    Metric.ball z ((2 : ℝ) ^ j * r)
end CKN.Core.HeatPotential
