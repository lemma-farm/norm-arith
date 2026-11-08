module
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.GaussianIntegrationByParts
public import Examples.pmaronow__aging_palomar.Dependencies.v4f130364bf1b.SphericalAging.LandscapeDerivatives
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.Trace
set_option autoImplicit false
public section
/-!
# Genuine cross-covariances of Hamiltonian derivatives

Every derivative is the actual iterated Fréchet derivative of the manuscript's
ordered Gaussian Hamiltonian. Their Gaussian laws and mixed covariance kernel
are proved by integration against the actual product disorder measure.
-/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace BigOperators
namespace SphericalAging.HamiltonianDerivativeCovariance
open FiniteModel GaussianIntegrationByParts
@[expose] def operatorTrace {N : ℕ} (U : Vector N →L[ℝ] Vector N) : ℝ :=
  LinearMap.trace ℝ (Vector N) U.toLinearMap
end SphericalAging.HamiltonianDerivativeCovariance
