import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.Fin.Basic
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Mul
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.Topology.Sequences
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.InnerProductSpace.PiL2

-- ==== Examples.ShengtongZhang_alt__BN.Examples.Example_9251c7e3843857b15921_Gram ====
/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
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
/-! ### CG03, locally, to avoid import clashes with `Weighted` -/
namespace GramAux
open Finset
open scoped InnerProductSpace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}
set_option linter.unusedSectionVars false
noncomputable section


lemma bessel_two {u v x : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) :
    (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set a := u ⬝ᵥ x
  set b := v ⬝ᵥ x
  set w := a • u + b • v
  set y := x - w
  have hy : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct]
    exact sum_nonneg fun _ _ ↦ mul_self_nonneg _
  have hxu : x ⬝ᵥ u = a := by rw [dotProduct_comm]
  have hxv : x ⬝ᵥ v = b := by rw [dotProduct_comm]
  have hxw : x ⬝ᵥ w = a ^ 2 + b ^ 2 := by
    simp [w, dotProduct_add, dotProduct_smul, hxu, hxv, pow_two]
  have hvu : v ⬝ᵥ u = 0 := by rw [dotProduct_comm, huv]
  have hww : w ⬝ᵥ w = a ^ 2 + b ^ 2 := by
    simp [w, dotProduct_add, dotProduct_smul, smul_dotProduct, hu, hv, huv, hvu]
    ring
  have hexpand : y ⬝ᵥ y = x ⬝ᵥ x - 2 * (x ⬝ᵥ w) + w ⬝ᵥ w := by
    simp [y, dotProduct_sub, dotProduct_comm w x]
    ring
  linarith

end
end GramAux
variable {V : Type*}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

end BN
