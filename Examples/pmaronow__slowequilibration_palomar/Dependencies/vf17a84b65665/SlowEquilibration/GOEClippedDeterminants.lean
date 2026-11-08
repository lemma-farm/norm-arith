-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SpectralTraceLipschitz
set_option autoImplicit false
@[expose] public section
/-!
# Actual clipped GOE determinant logarithms

The clipped logarithm is the literal sum over actual ordered GOE eigenvalues.
Its Gaussian Lipschitz constant, centered MGF, exact relation to the ordinary
absolute determinant, and equality on the actual spectral confinement event
are derived. A fixed regularization is not substituted for the determinant.
-/
namespace SlowEquilibration.GOEClippedDeterminants
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics GOEEdgeConcentration SpectralTraceLipschitz
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
def clippedTrace (n : ℕ) (k rho : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  ∑ i, clippedLog k rho (realizedEigenvalues n A i)
def absoluteDet (n : ℕ) (k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  |(k • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) - GOEDeterminantMoments.realization n A).det|
end
end SlowEquilibration.GOEClippedDeterminants
