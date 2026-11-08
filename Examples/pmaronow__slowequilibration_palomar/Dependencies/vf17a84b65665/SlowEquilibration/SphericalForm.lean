module
-- SPDX-License-Identifier: Apache-2.0
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphericalGibbs
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.HardSphereDynamics
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.SphericalIntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Tactic
set_option autoImplicit false
@[expose] public section
/-!
# The actual spherical tangential gradient and Dirichlet form

The state space is the manuscript's `EuclideanSpace ℝ (Fin N)` and its sphere
of squared radius `N`. The tangent projection is the actual operator
`I - xxᵀ/N`, and the scalar gradient is its application to the ambient Riesz
gradient. Independence of ambient smooth extensions is proved using genuine
orthogonal exponential flows, rather than assumed. The form below is the
integral of the actual tangential gradients against the actual Gibbs law.

Completion, closability, compact embedding, and spectral realization are
separate construction stages, not hypotheses hidden in these definitions.
-/
namespace SlowEquilibration.SphericalForm
noncomputable section
open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology
end
end SlowEquilibration.SphericalForm
