module

public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Kernel.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Independence.Integrable

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v7bd79a8ff60d.GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyFiltration ====
public section
@[expose] public section
/-! The actual whole Brownian-family past is a filtration. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
def ginibreBrownianFamilyPastSpace {Ω ι : Type*} (B : ι → ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω) inferInstance
axiom ginibreBrownianFamilyPastSpace_mono {Ω ι : Type*} (B : ι → ℝ≥0 → Ω → ℝ) :
    Monotone (ginibreBrownianFamilyPastSpace B)
axiom ginibreBrownianFamilyPastSpace_le {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (s : ℝ≥0) :
    ginibreBrownianFamilyPastSpace B s ≤ (inferInstance : MeasurableSpace Ω)

end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v7bd79a8ff60d.GinibrePoincare.Analysis.GinibreStochasticPastAugmentation ====
public section
@[expose] public section
/-! Genuine null augmentation of the actual joint Brownian past. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
def ginibreNullAugmentation {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω :=
  m ⊔ MeasurableSpace.generateFrom {s : Set Ω | P s = 0}

axiom ginibreNullAugmentation_le {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω) [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) :
    ginibreNullAugmentation (mAmbient := mAmbient) P m ≤ mAmbient

def ginibreBrownianAugmentedFiltration {Ω ι : Type*} [mAmbient : MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) : Filtration ℝ≥0 mAmbient where
  seq s := ginibreNullAugmentation (mAmbient := mAmbient) P (ginibreBrownianFamilyPastSpace B s)
  mono' s t hst := sup_le_sup_right (ginibreBrownianFamilyPastSpace_mono B hst) _
  le' s := ginibreNullAugmentation_le (mAmbient := mAmbient) P _ (ginibreBrownianFamilyPastSpace_le B P hB s)
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v7bd79a8ff60d.GinibrePoincare.Analysis.GinibreStochasticOrthogonalSquareSum ====
public section
@[expose] public section
/-! Finite square-moment expansion for genuinely orthogonal random errors. -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
axiom ginibre_integral_square_sum_of_cross_zero {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (P : Measure Ω)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P)
    (hcross : ∀ i j, i ≠ j → (∫ ω, X i ω * X j ω ∂P) = 0) :
    (∫ ω, (∑ i, X i ω)^2 ∂P) = ∑ i, ∫ ω, (X i ω)^2 ∂P
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Dependencies.v7bd79a8ff60d.GinibrePoincare.Analysis.GinibreBrownianIntegralLinear ====
public section
@[expose] public section
/-! Linear Brownian innovations with coefficients measurable in the genuine augmented past. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
axiom ginibreBrownian_augmented_linear_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F) :
    (∫ ω, (F ω*(B i (s+t) ω-B i s ω))^2 ∂P) =
      (t : ℝ)*(∫ ω, (F ω)^2 ∂P)
axiom ginibreBrownian_augmented_linear_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    MemLp (fun ω => F ω*(B i (s+t) ω-B i s ω)) 2 P
axiom ginibreBrownian_augmented_linear_disjoint_orthogonal {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t r v : ℝ≥0) (hst : s+t ≤ r) (i j : ι) (F G : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hG : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ G) :
    (∫ ω, (F ω*(B i (s+t) ω-B i s ω))*(G ω*(B j (r+v) ω-B j r ω)) ∂P) = 0
end
end GinibrePoincare

end
end

-- ==== Examples.djalilchafai__ginibre_poincare.Examples.Example_1111b3e12a3be3537301_GinibreBrownianIntegralIsometry ====
@[expose] public section
/-! Exact discrete Itô isometry for the actual augmented joint Brownian filtration. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
theorem ginibreBrownian_augmented_linear_sum_isometry {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (n : ℕ) (s t : Fin n → ℝ≥0)
    (hchron : ∀ i k, i < k → s i+t i ≤ s k) (F : Fin n → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) :
    (∫ ω, (∑ i, F i ω*(B j (s i+t i) ω-B j (s i) ω))^2 ∂P) =
      ∑ i, (t i : ℝ)*(∫ ω, (F i ω)^2 ∂P) := by
  let X := fun i ω => F i ω*(B j (s i+t i) ω-B j (s i) ω)
  have hX (i : Fin n) : MemLp (X i) 2 P :=
    ginibreBrownian_augmented_linear_memLp_two B P hB hind (s i) (t i) j (F i) (hF i) (hFi i)
  have hcross (i k : Fin n) (hne : i ≠ k) : (∫ ω, X i ω*X k ω ∂P) = 0 := by
    rcases lt_or_gt_of_ne hne with hik | hki
    · exact ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s i) (t i) (s k) (t k) (hchron i k hik) j j (F i) (F k) (hF i) (hF k)
    · simpa only [X, mul_comm] using ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s k) (t k) (s i) (t i) (hchron k i hki) j j (F k) (F i) (hF k) (hF i)
  change (∫ ω, (∑ i, X i ω)^2 ∂P) = _
  rw [ginibre_integral_square_sum_of_cross_zero P X hX hcross]
  apply Finset.sum_congr rfl
  intro i hi
  exact ginibreBrownian_augmented_linear_secondMoment B P hB hind (s i) (t i) j (F i) (hF i)

end
end GinibrePoincare
