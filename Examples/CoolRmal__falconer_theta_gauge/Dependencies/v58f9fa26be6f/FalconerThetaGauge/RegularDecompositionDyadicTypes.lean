/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularDecompositionCells
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularDecompositionSchedule
public import Mathlib
set_option autoImplicit false
/-!
# Actual bottom-up types of dyadic cells

The finite regular decomposition uses the original planar measure weights and
the manuscript's sampled depths. The count, discard and regularity conclusions
hold for the constructed cell types at every generation up to `N`.
-/
@[expose] public section
noncomputable section
open MeasureTheory Finset
open scoped Classical
namespace FalconerThetaGauge
open GaugeFrostman
end FalconerThetaGauge
