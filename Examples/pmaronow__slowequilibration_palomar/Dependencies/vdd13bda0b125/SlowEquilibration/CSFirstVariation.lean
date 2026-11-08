-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CSVariation
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.CSTwoAtom
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
set_option autoImplicit false
/-!
# Mixture derivatives and the necessary support criterion

Mixtures are ordinary nonnegative measures. Their functional is differentiated
within the interval of probability weights, including its boundary at zero.
-/
@[expose] public section
namespace SlowEquilibration.CrisantiSommers
open MeasureTheory Set Filter
open scoped Topology ENNReal
end SlowEquilibration.CrisantiSommers
