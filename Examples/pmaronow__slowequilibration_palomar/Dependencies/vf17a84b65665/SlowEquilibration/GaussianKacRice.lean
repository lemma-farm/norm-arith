-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianBlockFiber
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.CoefficientKacRice
set_option autoImplicit false
/-!
# Local marked Gaussian Kac--Rice with its canonical zero-fiber kernel

The genuine C1 coefficient-incidence area formula is converted to the literal
zero-observation Gaussian kernel using the proved coefficient graph Jacobian.
The mark retains arbitrary Borel dependence on the full coefficient vector.
-/
@[expose] public section
namespace SlowEquilibration.GaussianKacRice
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.GaussianBlockFiber
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
end
end SlowEquilibration.GaussianKacRice
