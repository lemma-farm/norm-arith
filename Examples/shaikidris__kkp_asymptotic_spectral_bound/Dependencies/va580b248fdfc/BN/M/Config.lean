/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.M.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
@[expose] public section
/-!
# Planar configuration and block entries of `M`

The normalized configuration of `docs/sol.tex` §4 (`eq:coordinates`,
`eq:blocks`): `z₀ = (1,0)`, `zᵢ = √sᵢ (-1, tᵢ)`, `yⱼ = √ρⱼ (xⱼ, 1)`.

Indices are identified with `Option (Fin k) ⊕ Fin p` via `configIdxEquiv`:
`none` is `z₀`, `some i` is `zᵢ`, and `Sum.inr j` is `yⱼ`. The carrier is
`Fin (k + 1 + p)`, which supplies `LinearOrder` for `M`.
-/
namespace BN
open Matrix Finset Function
open scoped Matrix
noncomputable section
variable {k p : ℕ}
variable (s t : Fin k → ℝ) (ρ x : Fin p → ℝ)
end
end BN
