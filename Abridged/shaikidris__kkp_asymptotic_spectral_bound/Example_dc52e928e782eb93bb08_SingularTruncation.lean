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

-- ==== Examples.shaikidris__kkp_asymptotic_spectral_bound.Examples.Example_dc52e928e782eb93bb08_SingularTruncation ====
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

/-- The right spectral projection retaining singular values strictly above `a`. -/
noncomputable def rightCutProjection (B : Matrix H R ℝ) (a : ℝ) : Matrix R R ℝ :=
  spectralMap (isHermitian_conjTranspose_mul_self B)
    (fun x => if a ^ 2 < x then 1 else 0)
/-- The inverse Gram operator on the retained space and zero on its complement. -/
noncomputable def rightCutInverse (B : Matrix H R ℝ) (a : ℝ) : Matrix R R ℝ :=
  spectralMap (isHermitian_conjTranspose_mul_self B)
    (fun x => if a ^ 2 < x then x⁻¹ else 0)


set_option linter.unusedVariables false in
/-- Applying a residual operator to the retained right space gains one inverse cutoff. -/
theorem mul_rightCutProjection_norm_le (B : Matrix H R ℝ) (D : Matrix R R ℝ)
    {a : ℝ} (ha : 0 < a) 
    (h_KKPAsymptotic_gram_mul_rightCutInverse : ∀ {H : Type u_1} {R : Type u_2} [inst : Fintype H] [inst_1 : Fintype R] [inst_2 : DecidableEq R]
      (B : Matrix H R ℝ) (a : ℝ),
      B.transpose * B * KKPAsymptotic.rightCutInverse B a = KKPAsymptotic.rightCutProjection B a)
    (h_KKPAsymptotic_rightCut_inverse_norm_le : ∀ {H : Type u_1} {R : Type u_2} [inst : Fintype H] [inst_1 : Fintype R] [inst_2 : DecidableEq R]
      (B : Matrix H R ℝ) {a : ℝ}, 0 < a → ‖B * KKPAsymptotic.rightCutInverse B a‖ ≤ a⁻¹)
    :
    ‖D * rightCutProjection B a‖ ≤ ‖D * Bᵀ‖ / a := by
  rw [← h_KKPAsymptotic_gram_mul_rightCutInverse B a]
  have hfactor : D * (Bᵀ * B * rightCutInverse B a) =
      (D * Bᵀ) * (B * rightCutInverse B a) := by simp only [Matrix.mul_assoc]
  rw [hfactor]
  apply (Matrix.l2_opNorm_mul _ _).trans
  simpa [div_eq_mul_inv] using
    (mul_le_mul_of_nonneg_left (h_KKPAsymptotic_rightCut_inverse_norm_le B ha) (norm_nonneg (D * Bᵀ)))
end KKPAsymptotic
