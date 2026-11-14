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

-- ==== Examples.shaikidris__kkp_asymptotic_spectral_bound.Examples.Example_d8c46ad967d15d701362_SingularTruncation ====
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
/-- The discarded rectangular block has operator norm at most the singular cutoff. -/
theorem rightCut_discard_norm_le (B : Matrix H R ℝ) {a : ℝ} (ha : 0 ≤ a) 
    (h_KKPAsymptotic_spectralMap_one : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ}
      (hC : C.IsHermitian), (KKPAsymptotic.spectralMap hC fun (x : ℝ) ↦ 1) = 1)
    (h_KKPAsymptotic_spectralMap_id : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ}
      (hC : C.IsHermitian), KKPAsymptotic.spectralMap hC id = C)
    (h_KKPAsymptotic_spectralMap_sub : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ} (hC : C.IsHermitian)
      (f g : ℝ → ℝ),
      KKPAsymptotic.spectralMap hC f - KKPAsymptotic.spectralMap hC g =
        KKPAsymptotic.spectralMap hC fun (x : ℝ) ↦ f x - g x)
    (h_KKPAsymptotic_spectralMap_norm_le : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ} (hC : C.IsHermitian)
      (f : ℝ → ℝ) {c : ℝ},
      0 ≤ c → (∀ (i : R), |f (hC.eigenvalues i)| ≤ c) → ‖KKPAsymptotic.spectralMap hC f‖ ≤ c)
    (h_KKPAsymptotic_rightCutProjection_transpose : ∀ {H : Type u_1} {R : Type u_2} [inst : Fintype H] [inst_1 : Fintype R] [inst_2 : DecidableEq R]
      (B : Matrix H R ℝ) (a : ℝ),
      (KKPAsymptotic.rightCutProjection B a).transpose = KKPAsymptotic.rightCutProjection B a)
    (h_KKPAsymptotic_projection_complement_transpose : ∀ {V : Type u_2} [inst : DecidableEq V] {P : Matrix V V ℝ},
      P.transpose = P → (1 - P).transpose = 1 - P)
    (h_KKPAsymptotic_spectralMap_mul : ∀ {R : Type u_2} [inst : Fintype R] [inst_1 : DecidableEq R] {C : Matrix R R ℝ} (hC : C.IsHermitian)
      (f g : ℝ → ℝ),
      KKPAsymptotic.spectralMap hC f * KKPAsymptotic.spectralMap hC g =
        KKPAsymptotic.spectralMap hC fun (x : ℝ) ↦ f x * g x)
    :
    ‖B * (1 - rightCutProjection B a)‖ ≤ a := by
  let hC := isHermitian_conjTranspose_mul_self B
  let P := rightCutProjection B a
  let Q := 1 - P
  have hQt : Qᵀ = Q := h_KKPAsymptotic_projection_complement_transpose (h_KKPAsymptotic_rightCutProjection_transpose B a)
  have hQspec : Q = spectralMap hC (fun x => if a ^ 2 < x then 0 else 1) := by
    dsimp [Q, P, rightCutProjection]
    rw [← h_KKPAsymptotic_spectralMap_one hC, h_KKPAsymptotic_spectralMap_sub]
    congr 2
    funext x
    split_ifs <;> norm_num
  have hspec : Bᵀ * B = spectralMap hC id := by
    simpa using (h_KKPAsymptotic_spectralMap_id hC).symm
  have hprod : (B * Q)ᴴ * (B * Q) =
      spectralMap hC (fun x => if a ^ 2 < x then 0 else x) := by
    have hQstar : Qᴴ = Q := by simpa using hQt
    rw [conjTranspose_mul, hQstar]
    simp only [conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᵀ B Q, hspec, hQspec,
      h_KKPAsymptotic_spectralMap_mul, h_KKPAsymptotic_spectralMap_mul]
    congr 2
    funext x
    split_ifs <;> simp
  have hn : ‖(B * Q)ᴴ * (B * Q)‖ ≤ a ^ 2 := by
    rw [hprod]
    apply h_KKPAsymptotic_spectralMap_norm_le hC _ (sq_nonneg a)
    intro i
    have hi := (posSemidef_conjTranspose_mul_self B).eigenvalues_nonneg i
    split_ifs with h
    · simp only [abs_zero]; exact sq_nonneg a
    · rw [abs_of_nonneg hi]
      exact le_of_not_gt h
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  change ‖B * Q‖ ≤ a
  nlinarith [norm_nonneg (B * Q)]

end KKPAsymptotic
