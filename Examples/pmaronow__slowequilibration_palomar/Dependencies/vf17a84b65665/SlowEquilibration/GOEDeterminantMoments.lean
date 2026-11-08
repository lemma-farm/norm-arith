-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GOEAsymptotics
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Upstream.OAI.Probability.SKGap.Matrix.RegularizedLogDet
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SphericalAging.GaussianLipschitzConcentration
set_option autoImplicit false
@[expose] public section
/-!
# Actual regularized GOE determinant moments

The determinant here is the square root of the determinant of
`(k I - W)^T (k I - W) + gamma I`, for positive `gamma`. Gaussian concentration
is applied to its actual logarithm, using the proved Frobenius-Lipschitz
matrix log-determinant estimate. This is an auxiliary regularized result;
the manuscript's raw clipped determinant theorem is not identified with it.
-/
namespace SlowEquilibration.GOEDeterminantMoments
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open GOEAsymptotics OAI.CriticalSK
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology Matrix.Norms.Frobenius
def shiftedMatrix (n : ℕ) (sigma k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  k • 1 - gaussianToMatrix (symmetrizeGaussianMatrix sigma A)
def rawDet (n : ℕ) (sigma gamma k : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  Real.sqrt (OAI.SKGap.LogDet.regularizedGram gamma (shiftedMatrix n sigma k A)).det
def realization (n : ℕ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  gaussianToMatrix (symmetrizeGaussianMatrix (goeScale n) A)
end
end SlowEquilibration.GOEDeterminantMoments
