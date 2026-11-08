-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.v3f58d72b5afe.SlowEquilibration.Upstream.OAI.Computability.MinUncut.GaussianHermite
set_option autoImplicit false
/-! Genuine L² Gaussian Mehler noise and every Hermite coefficient. The
pinned source's bounded-test restriction is removed by actual product-L²
Cauchy–Schwarz, retaining the true rotated Gaussian law. -/
@[expose] public section
namespace SlowEquilibration.GaussianMaximalCorrelation
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped ENNReal Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {ι : Type*} [Fintype ι]
end
end SlowEquilibration.GaussianMaximalCorrelation
