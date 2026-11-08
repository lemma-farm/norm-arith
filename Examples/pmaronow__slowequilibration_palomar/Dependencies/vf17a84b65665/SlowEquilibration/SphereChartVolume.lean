-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.SphereVolume
set_option autoImplicit false
/-!
# Arbitrary-dimensional actual round sphere chart volume

Adapted from the genuine explicit differential, determinant, and cone-Jacobian
proofs in OAI/MeasureTheory/FalconerCompletion/Sphere/SphereChartScale.lean,
Estimates/ConeJacobianMatrix.lean, and Fourier/SphereConeToLp.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
All maps, derivatives, and Lebesgue measures here are ordinary Mathlib objects.
-/
@[expose] public section
namespace SlowEquilibration.SphereChartVolume
open Set MeasureTheory Metric Module
open scoped RealInnerProductSpace Topology ENNReal Pointwise
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end
section Matrix
variable {n : ℕ}
end Matrix
end
end SlowEquilibration.SphereChartVolume
