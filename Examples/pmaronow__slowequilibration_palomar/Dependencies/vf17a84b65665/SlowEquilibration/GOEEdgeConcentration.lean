-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GOEDeterminantMoments
set_option autoImplicit false
@[expose] public section
/-!
# Exponentially small actual GOE edge failure

Eigenvalue Lipschitz estimates and genuine Gaussian concentration strengthen
proved spectral confinement in probability to an eventual exponential tail.
-/
namespace SlowEquilibration.GOEEdgeConcentration
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology Matrix.Norms.Frobenius
def realizedEigenvalues (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : Fin (n + 1) → ℝ :=
  matrixOrderedEigenvalues (symmetrizeGaussianMatrix (goeScale n) A)
end
end SlowEquilibration.GOEEdgeConcentration
