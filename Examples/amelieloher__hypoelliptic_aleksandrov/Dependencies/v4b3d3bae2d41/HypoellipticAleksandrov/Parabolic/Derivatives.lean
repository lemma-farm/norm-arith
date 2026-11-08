module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Module.Determinant
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Time--velocity derivatives

This module supplies velocity-only coordinate derivatives of scalar functions
on the product carrier `TimeVelocity d`, together with the coordinate bridge
for determinants of continuous linear endomorphisms of that carrier.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open Filter Matrix
open scoped BigOperators Topology
def timeDerivative {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : ℝ :=
  fderiv ℝ u z (1, 0)
def velocityHessian {d : ℕ} (u : TimeVelocity d → ℝ) (z : TimeVelocity d) : PDE.Mat d :=
  fun i j ↦
    fderiv ℝ (fderiv ℝ u) z (0, Pi.single i 1) (0, Pi.single j 1)
end HypoellipticAleksandrov.Parabolic
namespace HypoellipticAleksandrov.Parabolic
open Filter Matrix
open scoped BigOperators Topology
end HypoellipticAleksandrov.Parabolic
