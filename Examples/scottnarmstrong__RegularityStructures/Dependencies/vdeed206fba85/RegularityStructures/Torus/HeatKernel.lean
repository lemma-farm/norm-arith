/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeed206fba85.RegularityStructures.Torus.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Heat kernels on the three-torus

* `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`, the heat kernel on `ℝ³`;
* `heatKernel t`, its periodisation `p_t` on `T³` (the statement, equation (2.1));
* `heatSemigroup s f`, the heat semigroup `P_s` acting on `C(T³)` by convolution with the Gaussian
  on `ℝ³`;
* `massiveHeatKernel`, the kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` of `(∂_t - Δ + 1)⁻¹`
  (equation (2.2)).

The lemmas show that `gaussKernel s` is a probability density for `s > 0`, so `P_s` is linear
and contracts the supremum norm.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open MeasureTheory Real
namespace RegularityStructures
end RegularityStructures
end
/-! ### The Gaussian density on `ℝ³` -/
public section
open MeasureTheory Real
namespace RegularityStructures
end RegularityStructures
end
