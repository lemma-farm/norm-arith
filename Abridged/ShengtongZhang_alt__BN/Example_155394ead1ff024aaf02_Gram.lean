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

-- ==== Examples.ShengtongZhang_alt__BN.Dependencies.v73d7b6e7a9e2.BN.Basic.Spectrum ====
section
/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Ordered spectrum of a Hermitian matrix

This file records the ordered real spectrum of a Hermitian matrix, matching the
conventions in `docs/sol.tex`. The ordered family is Mathlib's antitone
`eigenvalues₀`, which is the paper's `λ₁ ≥ ⋯ ≥ λₙ` with `λ₁` at index `0`.
`F` is the sum of squares of the two largest positive eigenvalues, with missing
terms replaced by zero.
-/
namespace BN
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}
/-- The eigenvalues of a Hermitian matrix in nonincreasing order. The value at
`i` is the paper's `λ_{i+1}`. -/
noncomputable def eigs₀ (hA : A.IsHermitian) : Fin (Fintype.card n) → ℝ :=
  hA.eigenvalues₀

/-- The largest eigenvalue `λ₁(A)`. -/
noncomputable def lambdaMax (hA : A.IsHermitian) [Nonempty n] : ℝ :=
  eigs₀ hA ⟨0, Fintype.card_pos⟩
/-- The second-largest eigenvalue `λ₂(A)`. -/
noncomputable def lambdaSecond (hA : A.IsHermitian) [Nontrivial n] : ℝ :=
  eigs₀ hA ⟨1, Fintype.one_lt_card⟩

/-! ### N11 — Adjacency Frobenius mass -/
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

end BN

end

-- ==== Examples.ShengtongZhang_alt__BN.Examples.Example_155394ead1ff024aaf02_Gram ====
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

set_option linter.unusedVariables false in
axiom _root_.BN.GramAux.sum_antitone_le_two_largest._proof_2 : ∀ {m : ℕ}, 2 ≤ m → ¬1 < m → False
set_option linter.unusedVariables false in
axiom _root_.BN.GramAux.sum_antitone_le_two_largest._proof_1 : ∀ {m : ℕ}, 2 ≤ m → ¬0 < m → False
set_option linter.unusedVariables false in
axiom _root_.BN.GramAux.sum_antitone_le_two_largest : ∀ {m : ℕ} (hm : 2 ≤ m) (lam q : Fin m → ℝ),
  Antitone lam →
    (∀ (i : Fin m), 0 ≤ q i) →
      (∀ (i : Fin m), q i ≤ 1) →
        ∑ i : Fin m, q i = 2 →
          ∑ i : Fin m, lam i * q i ≤
            lam
                ⟨0,
                  Decidable.byContradiction fun (a : ¬0 < m) ↦
                    BN.GramAux.sum_antitone_le_two_largest._proof_1 hm a⟩ +
              lam
                ⟨1,
                  Decidable.byContradiction fun (a : ¬1 < m) ↦
                    BN.GramAux.sum_antitone_le_two_largest._proof_2 hm a⟩
set_option linter.unusedVariables false in
lemma orthonormal_pair_le_lambdaMax_add_lambdaSecond [Nontrivial n]
    (hB : B.IsHermitian) {u v : n → ℝ}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (huv : u ⬝ᵥ v = 0) 
    (h_BN_GramAux_eigenvectorBasis_dotProduct_self : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {B : Matrix n n ℝ} (hB : B.IsHermitian)
      (i : n),
      ((hB.eigenvectorBasis : n → EuclideanSpace ℝ n) i).ofLp ⬝ᵥ
          ((hB.eigenvectorBasis : n → EuclideanSpace ℝ n) i).ofLp =
        1)
    (h_BN_GramAux_bessel_two : ∀ {n : Type u_1} [inst : Fintype n] [DecidableEq n] {u v x : n → ℝ},
      u ⬝ᵥ u = 1 → v ⬝ᵥ v = 1 → u ⬝ᵥ v = 0 → (u ⬝ᵥ x) ^ 2 + (v ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x)
    (h_BN_GramAux_isHermitian_quadratic : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {B : Matrix n n ℝ} (hB : B.IsHermitian)
      (x : n → ℝ),
      x ⬝ᵥ B.mulVec x =
        ∑ k : n, hB.eigenvalues k * (((hB.eigenvectorBasis : n → EuclideanSpace ℝ n) k).ofLp ⬝ᵥ x) ^ 2)
    (h_BN_GramAux_parseval_eigenvectorBasis : ∀ {n : Type u_1} [inst : Fintype n] [inst_1 : DecidableEq n] {B : Matrix n n ℝ} (hB : B.IsHermitian)
      (x : n → ℝ), ∑ k : n, (((hB.eigenvectorBasis : n → EuclideanSpace ℝ n) k).ofLp ⬝ᵥ x) ^ 2 = x ⬝ᵥ x)
    :
    u ⬝ᵥ B *ᵥ u + v ⬝ᵥ B *ᵥ v ≤ lambdaMax hB + lambdaSecond hB := by
  rw [h_BN_GramAux_isHermitian_quadratic hB, h_BN_GramAux_isHermitian_quadratic hB, ← sum_add_distrib]
  let e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  let p : n → ℝ := fun k ↦
    ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
      ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2
  have hterm (k : n) :
      hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ u) ^ 2 +
          hB.eigenvalues k * ((hB.eigenvectorBasis k : n → ℝ) ⬝ᵥ v) ^ 2 =
        hB.eigenvalues k * p k := by
    simp [p]
    ring
  simp_rw [hterm]
  let q : Fin (Fintype.card n) → ℝ := fun i ↦ p (e i)
  have hsumq : ∑ i, q i = 2 := by
    have hre := Fintype.sum_equiv e (fun i => p (e i)) p (fun _ => rfl)
    have hu' := h_BN_GramAux_parseval_eigenvectorBasis hB u
    have hv' := h_BN_GramAux_parseval_eigenvectorBasis hB v
    have hsump : ∑ k, p k = 2 := by
      simp only [p, sum_add_distrib]
      rw [hu', hv', hu, hv]
      norm_num
    simpa [q] using hre.trans hsump
  have hq0 (i : Fin (Fintype.card n)) : 0 ≤ q i :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hq1 (i : Fin (Fintype.card n)) : q i ≤ 1 := by
    have := h_BN_GramAux_bessel_two hu hv huv (x := (hB.eigenvectorBasis (e i) : n → ℝ))
    simpa [q, p, h_BN_GramAux_eigenvectorBasis_dotProduct_self hB, dotProduct_comm] using this
  have hreindex :
      ∑ k, hB.eigenvalues k * p k = ∑ i, hB.eigenvalues₀ i * q i := by
    have := Fintype.sum_equiv e
      (fun i ↦ hB.eigenvalues (e i) * p (e i))
      (fun k ↦ hB.eigenvalues k * p k) (fun _ ↦ rfl)
    refine this.symm.trans (Finset.sum_congr rfl fun i _ ↦ ?_)
    simp [q, IsHermitian.eigenvalues, e]
  rw [hreindex]
  have htwo : 2 ≤ Fintype.card n := Nat.succ_le_of_lt Fintype.one_lt_card
  have hbound :=
    sum_antitone_le_two_largest htwo hB.eigenvalues₀ q hB.eigenvalues₀_antitone
      hq0 hq1 hsumq
  simpa [lambdaMax, lambdaSecond, eigs₀] using hbound

end
end GramAux
variable {V : Type*}
variable {G : SimpleGraph V} [DecidableRel G.Adj]

end BN
