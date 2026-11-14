import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix

-- ==== Examples.DiarHaidary__Nelson_Nguyen_conjecture_upper_bound_palomar.Examples.Example_f0cbd23df25b79eea4f6_ConcreteLadderIteration ====
/-!
# Concrete finite ladder iteration

The three grade bands are actual finite Euclidean matrices.  This file
expands their powers into ordered words, inserts the exact grade projections,
and proves the closed vacuum-word estimate used by the moment method.
-/
namespace SparseFock.ConcreteLadderIteration
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section
variable {m n d b : ℕ}


/-- A single entry is bounded by the Euclidean L2 operator norm. -/
theorem abs_entry_le_l2_opNorm {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℝ) (i j : I) : |A i j| ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ I := EuclideanSpace.single j 1
  let y : EuclideanSpace ℝ I :=
    (EuclideanSpace.equiv I ℝ).symm (Matrix.mulVec A e)
  have hcoord : ‖y i‖ ≤ ‖y‖ := PiLp.norm_apply_le y i
  have hop : ‖y‖ ≤ ‖A‖ * ‖e‖ := by
    simpa [y] using Matrix.l2_opNorm_mulVec A e
  calc
    |A i j| = ‖y i‖ := by
      simp [y, e, Matrix.mulVec, Real.norm_eq_abs]
    _ ≤ ‖y‖ := hcoord
    _ ≤ ‖A‖ * ‖e‖ := hop
    _ = ‖A‖ := by simp [e]

end
end SparseFock.ConcreteLadderIteration
