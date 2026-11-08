/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Kernel.Bilinear
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Kernel.Signs
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Kernel.N
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.CP.Basic
@[expose] public section
/-!
# The three-column kernel lemma

Package of the sign bounds `N ≥ 1`, `P ≥ 0`, `Z ≥ 0` with the bilinear
factorization of `docs/sol.tex` §3 (`lem:kernel`, `eq:factor`), and the
resulting three-column completely positive Gram of `U`.
-/
namespace BN
open Matrix
open scoped Matrix
noncomputable section
variable {k : ℕ} (t : Fin k → ℝ) (q : Fin k → ℝ)
/-! ### KR26: `lem:kernel` -/
end
end BN
