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

-- ==== Examples.shaikidris__kkp_asymptotic_spectral_bound.Examples.Example_0a88319166ab7dfd0861_SingularTruncation ====
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

omit [DecidableEq H] in
set_option linter.unusedVariables false in
/-- Retaining the right singular space does not increase the squared rectangular mass. -/
theorem rightCut_mass_le (B : Matrix H R ℝ) (a : ℝ) 
    (h_KKPAsymptotic_spectralMap_mul : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ} (hC : C.IsHermitian)
      (f g : ℝ → ℝ),
      KKPAsymptotic.spectralMap hC f * KKPAsymptotic.spectralMap hC g =
        KKPAsymptotic.spectralMap hC fun (x : ℝ) ↦ f x * g x)
    (h_KKPAsymptotic_rightCutProjection_transpose : ∀ {H : Type u_1} {R : Type u_2} [inst : Fintype H] [inst_1 : Fintype R] [inst_2 : DecidableEq R]
      (B : Matrix H R ℝ) (a : ℝ),
      (KKPAsymptotic.rightCutProjection B a).transpose = KKPAsymptotic.rightCutProjection B a)
    (h_KKPAsymptotic_spectralMap_trace : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ} (hC : C.IsHermitian)
      (f : ℝ → ℝ), (KKPAsymptotic.spectralMap hC f).trace = ∑ i : R, f (hC.eigenvalues i))
    (h_KKPAsymptotic_spectralMap_id : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ}
      (hC : C.IsHermitian), KKPAsymptotic.spectralMap hC id = C)
    :
    (∑ i : H, ∑ j : R, (B * rightCutProjection B a) i j ^ 2) ≤
      ∑ i : H, ∑ j : R, B i j ^ 2 := by
  let hC := isHermitian_conjTranspose_mul_self B
  let P := rightCutProjection B a
  have htrace (T : Matrix H R ℝ) : (Tᵀ * T).trace =
      ∑ i : H, ∑ j : R, T i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, transpose_apply, ← pow_two]
    exact Finset.sum_comm
  rw [← htrace (B * P), ← htrace B]
  have hPt : Pᵀ = P := h_KKPAsymptotic_rightCutProjection_transpose B a
  have hspec : Bᵀ * B = spectralMap hC id := by
    simpa using (h_KKPAsymptotic_spectralMap_id hC).symm
  have hprod : (B * P)ᵀ * (B * P) =
      spectralMap hC (fun x => if a ^ 2 < x then x else 0) := by
    rw [transpose_mul, hPt]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B P, hspec]
    dsimp [P, rightCutProjection]
    rw [h_KKPAsymptotic_spectralMap_mul, h_KKPAsymptotic_spectralMap_mul]
    congr 2
    funext x
    split_ifs <;> simp
  rw [hprod, h_KKPAsymptotic_spectralMap_trace, hspec, h_KKPAsymptotic_spectralMap_trace]
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · exact (posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg i

end KKPAsymptotic
