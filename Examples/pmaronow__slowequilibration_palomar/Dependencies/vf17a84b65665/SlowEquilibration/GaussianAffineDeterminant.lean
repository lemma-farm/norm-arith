module
-- SPDX-License-Identifier: Apache-2.0
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.GOEClippedDeterminants
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.Lemmas.SpinGlass.gaussian_concentration
set_option autoImplicit false
@[expose] public section
/-! # Literal affine symmetric Gaussian determinant moments

The clipped logarithm and ordinary determinant are actual functions of the
original Gaussian coefficients. The clipping event is the actual largest
eigenvalue event, and all normalized moments refer to the raw determinant's
own expectation.
-/
namespace SlowEquilibration.GaussianAffineDeterminant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
open Set MeasureTheory ProbabilityTheory Filter
open OAI.CriticalSK GOEAsymptotics GOEEdgeConcentration SpectralTraceLipschitz
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
/-- The actual affine random matrix, with the original Gaussian source. -/
def affineMatrix (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (g : EuclideanSpace ℝ ι) : GOEAsymptotics.GaussianMatrix (n+1) := C + W g
def clippedTrace (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k ρ : ℝ) (g : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, clippedLog k ρ (matrixOrderedEigenvalues (affineMatrix C W g) i)
/-- Literal raw absolute determinant of the actual affine matrix. -/
def absoluteDet (C : GOEAsymptotics.GaussianMatrix (n+1))
    (W : EuclideanSpace ℝ ι →L[ℝ] GOEAsymptotics.GaussianMatrix (n+1))
    (k : ℝ) (g : EuclideanSpace ℝ ι) : ℝ :=
  |(k • (1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) - gaussianToMatrix (affineMatrix C W g)).det|
end
end SlowEquilibration.GaussianAffineDeterminant
