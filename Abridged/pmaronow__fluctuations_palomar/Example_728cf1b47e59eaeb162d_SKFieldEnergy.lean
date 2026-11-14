module

public import Mathlib
public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Matrix.Stochastic
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Abel
public import Mathlib.Analysis.Normed.Module.Seminorm.Norm
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.MeasureTheory.Measure.Real

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.FiniteGibbs ====
public section
public section
noncomputable section
namespace SKConstants
/-- A configuration of `n` Boolean spins. The finite space has `2^n` elements. -/
abbrev Spin (n : ℕ) := Fin n → Bool
/-- Interpret `true` as `+1` and `false` as `-1`. -/
@[expose] def signedSpin {n : ℕ} (x : Spin n) (i : Fin n) : ℝ :=
  if x i then 1 else -1
/-- The completed quadratic spin Hamiltonian `H_W(x) = xᵀ W x / 2`.
No symmetry or probabilistic law for `W` is needed. -/
@[expose] def quadraticHamiltonian {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  (1 / ((2 : ℕ) : ℝ)) * ∑ i, ∑ j, signedSpin x i * W i j * signedSpin x j

end SKConstants

end
end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.GibbsComparison ====
public section
public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator RealInnerProductSpace
namespace SKConstants
@[expose] def spinEuclidean {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (signedSpin x)

end SKConstants

end
end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v0a4b81a5fb16.SKConstants.SpinGeometry ====
public section
public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
@[expose] def spinDifferenceSet {n : ℕ} (x y : Spin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ y i)
axiom spinEuclidean_distance_sq {n : ℕ} (x y : Spin n) :
    ‖spinEuclidean x - spinEuclidean y‖ ^ 2 = 4 * (hammingDist x y : ℝ)
end SKConstants

end
end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Examples.Example_728cf1b47e59eaeb162d_SKFieldEnergy ====
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical Matrix Matrix.Norms.L2Operator
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
def spinMatrixField {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n)
    (i : Fin n) : ℝ := ∑ j, W i j * signedSpin x j
axiom quadraticHamiltonian_difference_expansion {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsSymm) (x y : Spin n) :
    quadraticHamiltonian W y - quadraticHamiltonian W x =
      inner (𝕜 := ℝ) (spinEuclidean y - spinEuclidean x)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) W (spinEuclidean x)) +
      (1 / 2) * inner (𝕜 := ℝ) (spinEuclidean y - spinEuclidean x)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) W (spinEuclidean y - spinEuclidean x))
theorem quadraticHamiltonian_hamming_sparse_field_bound {n r : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (hW : W.IsSymm) (x y : Spin n)
    (hxy : hammingDist x y ≤ r) (A : ℝ)
    (hfields : ∀ I : Finset (Fin n), I.card ≤ r →
      ∑ i ∈ I, |spinMatrixField W x i| ≤ A) :
    |quadraticHamiltonian W y - quadraticHamiltonian W x| ≤ 2 * A + 2 * ‖W‖ * (r : ℝ) := by
  let d := spinEuclidean y - spinEuclidean x
  let L := Matrix.toEuclideanCLM (𝕜 := ℝ) W
  let I := spinDifferenceSet x y
  have hI : I.card ≤ r := hxy
  have hcross : |inner (𝕜 := ℝ) d (L (spinEuclidean x))| ≤ 2 * A := by
    rw [Matrix.inner_toEuclideanCLM]
    change |∑ i, (signedSpin y i - signedSpin x i) * spinMatrixField W x i| ≤ 2 * A
    rw [← Finset.sum_subset (Finset.subset_univ I) (fun i hi hiI => ?_)]
    · calc
        _ ≤ ∑ i ∈ I, |(signedSpin y i - signedSpin x i) * spinMatrixField W x i| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ I, 2 * |spinMatrixField W x i| := by
          apply Finset.sum_le_sum
          intro i hi
          rw [abs_mul]
          have hd : |signedSpin y i - signedSpin x i| ≤ (2 : ℝ) := by
            cases hy : y i <;> cases hx : x i <;> norm_num [signedSpin, hy, hx]
          exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
        _ ≤ 2 * A := by rw [← Finset.mul_sum]; linarith [hfields I hI]
    · have he : x i = y i := by
        simpa only [I, spinDifferenceSet, Finset.mem_filter, Finset.mem_univ,
          true_and, not_not] using hiI
      simp [signedSpin, he]
  have hquad : |inner (𝕜 := ℝ) d (L d)| ≤ 4 * ‖W‖ * (r : ℝ) := by
    have hop := L.le_opNorm d
    rw [show ‖L‖ = ‖W‖ from Matrix.l2_opNorm_toEuclideanCLM W] at hop
    have h := (abs_real_inner_le_norm d (L d)).trans
      (mul_le_mul_of_nonneg_left hop (norm_nonneg d))
    have hd : ‖d‖^2 ≤ 4 * (r : ℝ) := by
      rw [show ‖d‖^2 = 4 * (hammingDist y x : ℝ) from spinEuclidean_distance_sq y x,
        hammingDist_comm y x]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hxy) (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hd (norm_nonneg W)]
  rw [quadraticHamiltonian_difference_expansion W hW]
  calc
    _ ≤ |inner (𝕜 := ℝ) d (L (spinEuclidean x))| +
        |(1 / 2 : ℝ) * inner (𝕜 := ℝ) d (L d)| := abs_add_le _ _
    _ ≤ 2 * A + 2 * ‖W‖ * (r : ℝ) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      linarith
end SKConstants
