/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.DirichletLaplacian
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Finite-volume Hamiltonian -/
open scoped Matrix
public section
namespace FroehlichSpencer
/-- The finite-volume Hamiltonian `-Δ_Λ + v χ_Λ`. -/
@[expose] noncomputable def hamiltonian (ν : ℕ) (Λ : Finset (Site ν))
    (v : Site ν → ℝ) : Matrix {x : Site ν // x ∈ Λ} {x : Site ν // x ∈ Λ} ℂ := by
  classical
  exact -dirichletLaplacian ν Λ + Matrix.diagonal (fun x => (v x.1 : ℂ))
end FroehlichSpencer
end
