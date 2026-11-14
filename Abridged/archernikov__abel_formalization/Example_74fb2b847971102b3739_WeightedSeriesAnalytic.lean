import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

-- ==== Examples.archernikov__abel_formalization.Examples.Example_74fb2b847971102b3739_WeightedSeriesAnalytic ====
/-! # Analytic expansions of absolutely summable coefficient series

Each multivariate monomial is the diagonal of a continuous multilinear map.
Grouping these maps by total degree supplies the actual convergent analytic
expansion of a weighted summable coefficient series.
-/
noncomputable section
open scoped BigOperators ENNReal
namespace AbelFormalization
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
/-- An ordered representative of a symmetric word. -/
def symmetricWord {n : ℕ} (s : Sym σ n) : Fin n → σ :=
  fun j => (s : Multiset σ).toList.get
    (Fin.cast (by rw [Multiset.length_toList]; exact s.property.symm) j)

/-- A norm-at-most-one multilinear realization of a monomial. -/
def symmetricMonomialMap {n : ℕ} (s : Sym σ n) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => σ → ℝ) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin n) ℝ).compContinuousLinearMap
    (fun j => ContinuousLinearMap.proj (symmetricWord s j))

/-- The homogeneous multilinear expansion associated to a coefficient series. -/
def weightedSeriesExpansion (f : MvPowerSeries σ ℝ) :
    FormalMultilinearSeries ℝ (σ → ℝ) ℝ := fun n =>
  ∑ s : Sym σ n, MvPowerSeries.coeff (s : Multiset σ).toFinsupp f •
    symmetricMonomialMap s
set_option linter.unusedVariables false in
theorem weightedSeriesExpansion_norm_le (f : MvPowerSeries σ ℝ) (n : ℕ) 
    (h_AbelFormalization_symmetricMonomialMap_norm_le : ∀ {σ : Type u_1} [inst : Fintype σ] {n : ℕ} (s : Sym σ n),
      ‖AbelFormalization.symmetricMonomialMap s‖ ≤ 1)
    :
    ‖weightedSeriesExpansion f n‖ ≤
      ∑ s : Sym σ n, ‖MvPowerSeries.coeff (s : Multiset σ).toFinsupp f‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (h_AbelFormalization_symmetricMonomialMap_norm_le s)

end AbelFormalization
