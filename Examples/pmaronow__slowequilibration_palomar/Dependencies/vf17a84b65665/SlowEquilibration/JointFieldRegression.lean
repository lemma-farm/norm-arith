-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.WholeFieldRegression
public import Mathlib.LinearAlgebra.Matrix.Block
set_option autoImplicit false
/-!
# Joint score and tangent-gradient whole-field regression

The observation includes the value, radial derivative, and all tangent gradient
coordinates. Its block covariance and nondegeneracy come from the actual field.
-/
@[expose] public section
namespace SlowEquilibration.WholeFieldRegression
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open scoped RealInnerProductSpace ENNReal Topology
noncomputable section
end
end SlowEquilibration.WholeFieldRegression
