import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Fintype.EquivFin

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Dependencies.v66af89a70520.SparseStackV3.Base.MatrixTail ====
section
/-
Copyright (c) 2026 Diar Heidary. All rights reserved.
Released under the MIT license.

VENDORED BASE MODULE.  This file is copied verbatim (apart from its import
paths and this header) from the author's Version 2.0 formalization at
https://github.com/DiarHaidary/Nelson-Nguyen-conjecture-upper-bound-palomar
(`SparseFockFormal/MatrixTail.lean`).  The sketch distribution, the Parseval-frame
encoding of `U`, the finite-probability API and the operator-norm/trace
bridge are unchanged between Version 2.0 and Version 3.0 of the manuscript,
so they are reused rather than reproved.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
namespace SparseFock
namespace MatrixTail
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def quadraticForm (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) : ℝ :=
  ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) A x, x⟫_ℝ
/-- For a real symmetric matrix, L2 operator-norm control is exactly uniform
control of its homogeneous quadratic form. -/
axiom opNorm_le_iff_quadraticForm (A : Matrix ι ι ℝ)
    (hA : A.IsHermitian) (ε : ℝ) (hε : 0 ≤ ε) :
    ‖A‖ ≤ ε ↔
      ∀ x : EuclideanSpace ℝ ι,
        |quadraticForm A x| ≤ ε * ‖x‖ ^ 2

universe u_m u_n

end
end MatrixTail
end SparseFock

end

-- ==== Examples.DiarHaidary__Improved_SparseStack_Constants.Examples.Example_bfd9e7caff5574814f70_Spectator ====
/- Copyright (c) 2026 Diar Heidary. Released under the MIT license. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
namespace SparseStackV3.ConcreteSharedFactor
noncomputable section
variable {ρ η : Type*} [Fintype ρ] [Fintype η] [DecidableEq ρ] [DecidableEq η]
def spectator (A : Matrix η η ℝ) : Matrix (ρ × η) (ρ × η) ℝ :=
  fun x y => if x.1 = y.1 then A x.2 y.2 else 0
def fiber (z : EuclideanSpace ℝ (ρ × η)) (r : ρ) : EuclideanSpace ℝ η :=
  WithLp.toLp 2 (fun i => WithLp.ofLp z (r,i))
axiom spectator_hermitian (A : Matrix η η ℝ) (hA : A.IsHermitian) :
    (spectator (ρ := ρ) A).IsHermitian
axiom quadratic_spectator (A : Matrix η η ℝ) (z : EuclideanSpace ℝ (ρ × η)) :
    SparseFock.MatrixTail.quadraticForm (spectator A) z =
      ∑ r, SparseFock.MatrixTail.quadraticForm A (fiber z r)
axiom sum_fiber_norm_sq (z : EuclideanSpace ℝ (ρ × η)) :
    (∑ r, ‖fiber z r‖^2) = ‖z‖^2
theorem spectator_norm_le (A : Matrix η η ℝ) (hA : A.IsHermitian) :
    ‖spectator (ρ := ρ) A‖ ≤ ‖A‖ := by
  rw [SparseFock.MatrixTail.opNorm_le_iff_quadraticForm _
    (spectator_hermitian A hA) _ (norm_nonneg _)]
  intro z
  rw [quadratic_spectator]
  calc
    |∑ r, SparseFock.MatrixTail.quadraticForm A (fiber z r)| ≤
        ∑ r, |SparseFock.MatrixTail.quadraticForm A (fiber z r)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r, ‖A‖ * ‖fiber z r‖^2 := by
      apply Finset.sum_le_sum
      intro r _
      exact (SparseFock.MatrixTail.opNorm_le_iff_quadraticForm A hA ‖A‖
        (norm_nonneg A)).mp le_rfl (fiber z r)
    _ = ‖A‖ * ‖z‖^2 := by rw [← Finset.mul_sum,sum_fiber_norm_sq]
end
end SparseStackV3.ConcreteSharedFactor
