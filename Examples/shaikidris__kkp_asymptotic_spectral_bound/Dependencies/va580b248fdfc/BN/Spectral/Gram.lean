/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Basic.Inner
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Basic.Spectrum
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.va580b248fdfc.BN.Spectral.Weighted
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Rank
@[expose] public section
/-!
# Edge-supported positive part and the Gram form

If `X` is symmetric then `B = A_G ⊙ X₊` is symmetric, entrywise nonnegative,
zero-diagonal, and supported on the edges of `G`. Pairing against `X` or `B`
gives the same Frobenius mass. Combined with the weighted Motzkin–Straus bound
and the rank-two variational lemma, this yields `thm:gram`.

`BN.Spectral.Variational` cannot be imported here: it shares `inner_vecMulVec`
with `BN.MS.Basic` (pulled in by `Weighted`), and also overlaps Weighted on
`inner_smul_vecMulVec`, `inner_vecMulVec_vecMulVec`, and
`eigenvectorBasis_dotProduct`. The CG03 argument is therefore reproduced in
`GramAux`.
-/
namespace BN
open Matrix
open scoped Matrix
/-! ### CG03, locally, to avoid public import clashes with `Weighted` -/
namespace GramAux
open Finset
open scoped InnerProductSpace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}
set_option linter.unusedSectionVars false
noncomputable section
end
end GramAux
variable {V : Type*}
variable {G : SimpleGraph V} [DecidableRel G.Adj]
end BN
