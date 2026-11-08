/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.CP.Basic
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Kernel.Data
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Kernel.Main
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.M.Config
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.M.Elim
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
@[expose] public section
/-!
# Feature factorisation `M = FFᵀ + L` and the Schur complement of `E`

`SC01`–`SC07` record the weights `q i`, `γ`, the feature matrix `F`, the
weighted Laplacian `L`, the `E`-block `L_EE` and its inverse, and the
reduced data `L_red`, `𝒰` of `docs/sol.tex` §4.

After block elimination replaces `L` by `diag(L_EE, L_red)` and the feature
rows by `(F_E, 𝒰)`, the Schur complement of the first block is
`L_red + 𝒰 (I - F_Eᵀ (L_EE + F_E F_Eᵀ)⁻¹ F_E) 𝒰ᵀ`. The bracket equals
`(I + F_Eᵀ L_EE⁻¹ F_E)⁻¹` by the Woodbury companion identity
(paper (eq:Schur)).
-/
open Matrix
open scoped Matrix
namespace BN
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {R : Type*} [CommRing R]
set_option linter.unusedSectionVars false
noncomputable section
end
/-! ### Configuration-dependent Schur data (SC01–SC07) -/
noncomputable section
open Finset
variable {k p : ℕ}
/-! ### SC01 — weights `q i` and `γ` -/
variable (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
section PairCopy
variable {n : Type*} [Fintype n] [DecidableEq n]
variable [LinearOrder n]
end PairCopy
end
end BN
