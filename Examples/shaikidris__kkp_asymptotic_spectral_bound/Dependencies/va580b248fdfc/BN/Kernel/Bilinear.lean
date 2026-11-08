/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Kernel.Data
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Kernel.SM
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.Adjugate
@[expose] public section
/-!
# Bilinear expansion of `𝒦`

Completing squares in coordinates `2,1,0` yields `eq:bilinear`, and
substituting `U` yields the factorization `eq:factor` of `docs/sol.tex` §3.
-/
namespace BN
open Matrix
open scoped Matrix
noncomputable section
variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)
/-! ### Fin 3 expansions -/
end
end BN
