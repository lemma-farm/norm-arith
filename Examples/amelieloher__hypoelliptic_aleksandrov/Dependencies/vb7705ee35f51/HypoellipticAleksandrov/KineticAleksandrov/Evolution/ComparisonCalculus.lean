module
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Linarith
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.KineticAleksandrov.Operator
import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb7705ee35f51.HypoellipticAleksandrov.Parabolic.MinimumPrinciple
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Pointwise maximum calculus for the viscous transported operator

For `0 ≤ ε` the viscous transported operator is
`L_ε = ∂σ + B : D_y² + b(y) · ∇_z + ε Δ_z`.  This module proves the pointwise
sign of `L_ε w` at a point where `w` is `C²` and is maximal among all nearby
points of no earlier time.  This is the pointwise step of the usual maximum
argument used for Proposition 2.1.  No derivative of any
moving boundary curve is involved.

## Main definitions

* `viscousTransportedOperator`: the operator `L_ε`.
* `sliceHessian`: the Hessian matrix of a scalar function on `PDE.Vec n`, in the
  project's gradient convention.

## Main results

* `viscousTransportedOperator_nonpos_of_future_localMax`.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Filter Set Matrix
open scoped MatrixOrder Topology
structure IsSliceRegularAt {n : ℕ} (w : KineticPoint n → ℝ) (p : KineticPoint n) : Prop where
  /-- Differentiability of the time slice. -/
  time : DifferentiableAt ℝ (fun t => w ⟨t, p.position, p.velocity⟩) p.time
  /-- `C²` regularity of the diffused-coordinate slice. -/
  position : ContDiffAt ℝ 2 (fun y => w ⟨p.time, y, p.velocity⟩) p.position
  /-- `C²` regularity of the transported-coordinate slice. -/
  velocity : ContDiffAt ℝ 2 (fun z => w ⟨p.time, p.position, z⟩) p.velocity
end HypoellipticAleksandrov.KineticAleksandrov
