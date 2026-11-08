-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianObservationCoercivity
set_option autoImplicit false
@[expose] public section
/-! A genuine positive coercivity constant for every finite surjective observation. -/
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
end
end SlowEquilibration.GaussianObservationCoercivity
