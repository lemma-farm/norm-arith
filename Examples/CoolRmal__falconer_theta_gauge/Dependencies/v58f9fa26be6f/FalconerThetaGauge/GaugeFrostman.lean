module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.Statement
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.GaugeFrostmanWeights
public import Mathlib
set_option autoImplicit false
/-!
# Gauge content and the finite ingredients of Frostman's lemma

These are ingredients of Lemma 5.1 of the manuscript. In particular, positive
gauge Hausdorff measure gives positive unrestricted Hausdorff content. The
probability measure and its ball bound are not yet constructed in this file.

The content-to-measure argument is adapted from `FalconerPacking.Content`
(original source credits Yongxi Lin, Apache 2.0), replacing powers by the manuscript's actual gauge.
Source: `CoolRmal/falconer-packing` commit `70140ccedfb6de71342299523a21b1550df69ab9`:
https://github.com/CoolRmal/falconer-packing/blob/70140ccedfb6de71342299523a21b1550df69ab9/FalconerPacking/Content.lean
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
namespace GaugeFrostman
/-- Side length of a dyadic square of generation `j`. -/
def dyadicRadius (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℝ))
end GaugeFrostman
end FalconerThetaGauge
