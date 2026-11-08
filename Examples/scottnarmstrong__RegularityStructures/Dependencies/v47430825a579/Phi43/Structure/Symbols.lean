/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Finset.Sym
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The finite Φ⁴₃ symbol sector

This is the finite part of Hairer's structure for the dynamical Φ⁴₃ equation
which is needed by the fixed point and by the two counterterms.  The source is
Hairer, *A theory of regularity structures*, arXiv:1303.5113v4 (`Hai14`).
The construction follows §8.1 and the concrete choice (9.2).  The positive
symbol `I(Ψ)` is retained because it occurs in Hairer's renormalisation table
(9.3), even though it is above the fixed-point cutoff.  We use
`α = -5/2-κ`, `κ ∈ (0,1/16)`, and `γ = 1+3κ` as in §9.4.

The symbols `XᵢΨ`, `XᵢXⱼ`, and `XᵢΨ²` are retained in the finite product
table.  The first and third occur in the Taylor expansion of the products
`I(Ψ)Ψ` and `I(Ψ)Ψ²`; the second is the polynomial product required for the
structure-group action.  `X₀` is included with parabolic degree two, although
it lies above this cutoff.
-/
@[expose] public noncomputable section
open Set
namespace RegularityStructures.Phi43
/-- The admissible noise parameter, corresponding to Hairer §9.2. -/
abbrev Kappa : Type := Ioo (0 : ℝ) (1 / 16)
inductive Symbol where
  | one
  | noise
  | x0
  | x (i : Fin 3)
  | xMul (p : Sym2 (Fin 3))
  | psi
  | iPsi
  | psiSq
  | psiCube
  | psiX (i : Fin 3)
  | psiSqX (i : Fin 3)
  | iPsiSq
  | iPsiCube
  | iPsiPsi
  | iPsiPsiSq
  | iPsiSqPsi
  | iPsiSqPsiSq
  | iPsiCubePsi
  | iPsiCubePsiSq
  | iPsiCubeSq
  deriving DecidableEq, Fintype
def productSymbol : Symbol → Symbol → Option Symbol
  | .one, b => some b
  | a, .one => some a
  | .x i, .x j => some (.xMul s(i, j))
  | .x j, .psi => some (.psiX j)
  | .psi, .x j => some (.psiX j)
  | .x j, .psiSq => some (.psiSqX j)
  | .psiSq, .x j => some (.psiSqX j)
  | .psi, .psi => some .psiSq
  | .psi, .psiSq => some .psiCube
  | .psiSq, .psi => some .psiCube
  | .psiX i, .psi => some (.psiSqX i)
  | .psi, .psiX i => some (.psiSqX i)
  | .iPsi, .psi => some .iPsiPsi
  | .psi, .iPsi => some .iPsiPsi
  | .iPsi, .psiSq => some .iPsiPsiSq
  | .psiSq, .iPsi => some .iPsiPsiSq
  | .iPsiPsi, .psi => some .iPsiPsiSq
  | .psi, .iPsiPsi => some .iPsiPsiSq
  | .iPsiSq, .psi => some .iPsiSqPsi
  | .psi, .iPsiSq => some .iPsiSqPsi
  | .iPsiCube, .psi => some .iPsiCubePsi
  | .psi, .iPsiCube => some .iPsiCubePsi
  | .iPsiSq, .psiSq => some .iPsiSqPsiSq
  | .psiSq, .iPsiSq => some .iPsiSqPsiSq
  | .iPsiSqPsi, .psi => some .iPsiSqPsiSq
  | .psi, .iPsiSqPsi => some .iPsiSqPsiSq
  | .iPsiCube, .psiSq => some .iPsiCubePsiSq
  | .psiSq, .iPsiCube => some .iPsiCubePsiSq
  | .iPsiCubePsi, .psi => some .iPsiCubePsiSq
  | .psi, .iPsiCubePsi => some .iPsiCubePsiSq
  | .iPsiCube, .iPsiCube => some .iPsiCubeSq
  | _, _ => none
end RegularityStructures.Phi43
end
