-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vc262a07b63c3.SlowEquilibration.GaussianDiagonalQuadraticVariance
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vc262a07b63c3.SlowEquilibration.Upstream.OAI.MathematicalPhysics.CriticalSK.GaussianMoments
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vc262a07b63c3.SlowEquilibration.NonnegativeRealMoment
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option autoImplicit false
/-! Genuine centered Gaussian quadratic exponential moments. The exact
scalar Gaussian integral and true product Gaussian law yield dimension
independent normalized exponential control, for either sign of each weight. -/
@[expose] public section
namespace SlowEquilibration.GaussianQuadraticVariance
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end
end SlowEquilibration.GaussianQuadraticVariance
