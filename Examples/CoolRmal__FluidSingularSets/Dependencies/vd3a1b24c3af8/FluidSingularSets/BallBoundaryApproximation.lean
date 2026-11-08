-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.FluidSingularSets.PolynomialBallDivergence
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.FluidSingularSets.LocalStokesEnergy
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.CKN.Foundation.Euclidean.SmoothIBP
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.CKN.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# Interior test approximations for the weighted ball fields

Actual smooth cutoff functions remove a shrinking boundary layer. Multiplying
by the vanishing ball weight gives compact tests supported strictly inside the
ball. Uniform gradient majorants and dominated convergence prove that the
actual derivative of the weighted smooth field has zero ball integral.
-/
@[expose] public section
open CKN MeasureTheory Set Filter
open CKN.Foundation.Parabolic
open scoped BigOperators ENNReal Topology
set_option autoImplicit false
noncomputable section
namespace FluidSingularSets
/-- The fixed closed unit ball, described by its polynomial boundary weight. -/
def weightedClosedUnitBall : Set Vec3 := {x | 0 ≤ ballBoundaryWeight 0 1 x}
theorem weightedClosedUnitBall_isCompact : IsCompact weightedClosedUnitBall := by
  have hc : IsClosed weightedClosedUnitBall :=
    isClosed_le continuous_const (ballBoundaryWeight_contDiff 0 1).continuous
  apply (isCompact_closedBall (0 : Vec3) 1).of_isClosed_subset hc
  intro x hx
  have hs : (∑ i : Fin 3, x i ^ 2) ≤ 1 := by
    simpa [weightedClosedUnitBall, ballBoundaryWeight] using hx
  have he : vec3EuclideanNorm x ≤ 1 := by
    unfold vec3EuclideanNorm
    exact (Real.sqrt_le_sqrt hs).trans (by norm_num)
  simpa using (norm_le_vec3EuclideanNorm x).trans he
end FluidSingularSets
