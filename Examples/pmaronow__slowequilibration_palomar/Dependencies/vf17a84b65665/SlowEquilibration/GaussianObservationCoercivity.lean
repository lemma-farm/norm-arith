-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GaussianRegression
public import Mathlib.Analysis.InnerProductSpace.ProdL2
set_option autoImplicit false
@[expose] public section
/-! # Dimension-independent coercivity of true observation Gram operators -/
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
end
end SlowEquilibration.GaussianObservationCoercivity
