module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.Fin.Basic
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Sequences
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix

-- ==== Examples.shaikidris__kkp_asymptotic_spectral_bound.Examples.Example_76660a21dfa606025f73_SingularTruncation ====
@[expose] public section
/-!
# Right singular truncation

The retained right space is constructed from the spectral theorem for the
Gram matrix. This works for rectangular matrices, including empty dimensions.
All matrix norms in this module are Euclidean operator norms.
-/
namespace KKPAsymptotic
open Matrix Unitary
open scoped Classical Matrix.Norms.L2Operator
variable {H R : Type*} [Fintype H] [DecidableEq H] [Fintype R] [DecidableEq R]
/-- Diagonal functional calculus in the fixed orthonormal eigenbasis. -/
noncomputable def spectralMap {C : Matrix R R ℝ} (hC : C.IsHermitian)
    (f : ℝ → ℝ) : Matrix R R ℝ :=
  conjStarAlgAut ℝ (Matrix R R ℝ) hC.eigenvectorUnitary
    (diagonal (fun i => f (hC.eigenvalues i)))

omit [DecidableEq H] in
set_option linter.unusedVariables false in
/-- The Euclidean operator norm is bounded by the Frobenius mass, for rectangular matrices. -/
theorem rectangular_opNorm_sq_le (B : Matrix H R ℝ) 
    (h_KKPAsymptotic_spectralMap_norm_le : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ} (hC : C.IsHermitian)
      (f : ℝ → ℝ) {c : ℝ},
      0 ≤ c → (∀ (i : R), |f (hC.eigenvalues i)| ≤ c) → ‖KKPAsymptotic.spectralMap hC f‖ ≤ c)
    (h_KKPAsymptotic_spectralMap_id : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ}
      (hC : C.IsHermitian), KKPAsymptotic.spectralMap hC id = C)
    :
    ‖B‖ ^ 2 ≤ ∑ i : H, ∑ j : R, B i j ^ 2 := by
  let C := Bᴴ * B
  have hC : C.PosSemidef := posSemidef_conjTranspose_mul_self B
  have ht : C.trace = ∑ i : H, ∑ j : R, B i j ^ 2 := by
    simp only [C, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      conjTranspose_eq_transpose_of_trivial, transpose_apply, ← pow_two]
    exact Finset.sum_comm
  have hn : ‖C‖ ≤ C.trace := by
    conv_lhs => rw [← h_KKPAsymptotic_spectralMap_id hC.isHermitian]
    apply h_KKPAsymptotic_spectralMap_norm_le hC.isHermitian id hC.trace_nonneg
    intro i
    simp only [id_eq, abs_of_nonneg (hC.eigenvalues_nonneg i)]
    rw [hC.isHermitian.trace_eq_sum_eigenvalues]
    exact Finset.single_le_sum (fun j _ => hC.eigenvalues_nonneg j) (Finset.mem_univ i)
  change ‖Bᴴ * B‖ ≤ _ at hn
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, ht] at hn
  simpa only [pow_two] using hn
end KKPAsymptotic
