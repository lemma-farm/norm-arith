/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.QuadForm
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Regularity
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Resolvent
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Finite-volume restrictions of a kernel plus a potential

Generic setting for infinite-volume Green functions: an index type `X`, a kernel
`a : X → X → ℂ` (the "hopping" part) and a real potential `v : X → ℝ`.

For a finite set
`Λ : Finset X`, `restrictedOp a v Λ` is the matrix `a|_Λ + diagonal v|_Λ` on the subtype `Λ`, and
`resolventColumn a v Λ z y` is the column `y` of `(restrictedOp a v Λ - z • 1)⁻¹`, extended by
zero outside `Λ`.

Motivation: the finite-volume Hamiltonians `H_Λ` and Green functions `G_Λ` of
Fröhlich–Spencer (1983), (1.9), (1.28)–(1.29), Fröhlich–Spencer (1983); no lattice or
Laplacian is defined here.
-/
@[expose] public section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X]
/-- The matrix `a|_Λ + diagonal v|_Λ` on the finite set `Λ`. -/
noncomputable def restrictedOp (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) : Matrix Λ Λ ℂ :=
  Matrix.of (fun x y : Λ => a x y) + Matrix.diagonal (fun x : Λ => (v x : ℂ))
/-- Column `y` of the finite-volume resolvent `(restrictedOp a v Λ - z • 1)⁻¹`, extended by zero
outside `Λ` (and identically zero if `y ∉ Λ`). -/
noncomputable def resolventColumn (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (z : ℂ) (y : X) :
    X → ℂ :=
  fun x => if h : x ∈ Λ ∧ y ∈ Λ then
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, h.1⟩ ⟨y, h.2⟩ else 0
theorem restrictedOp_apply (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (x y : Λ) :
    restrictedOp a v Λ x y = a x y + if x = y then (v x : ℂ) else 0 := by
  simp [restrictedOp, Matrix.diagonal_apply]
theorem isHermitian_restrictedOp {a : X → X → ℂ} (ha : ∀ x y, a y x = star (a x y))
    (v : X → ℝ) (Λ : Finset X) : (restrictedOp a v Λ).IsHermitian := by
  refine isHermitian_add_diagonal (Matrix.IsHermitian.ext fun x y => ?_) (fun x : Λ => v x)
  simp only [Matrix.of_apply]
  rw [ha x y, star_star]
theorem resolventColumn_of_mem (a : X → X → ℂ) (v : X → ℝ) {Λ : Finset X} (z : ℂ) {x y : X}
    (hx : x ∈ Λ) (hy : y ∈ Λ) :
    resolventColumn a v Λ z y x =
      ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [resolventColumn, hx, hy]
end FroehlichSpencer.Infra
