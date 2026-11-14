import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Gamma

-- ==== Examples.scottnarmstrong__CoarseGraining.Dependencies.vb7e4f18e72ab.Homogenization.Probability.IndependentSums.WeakOrlicz ====
section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory
variable {Ω : Type*}
/-!
Weak-Orlicz tail notation for the independent-sums probability mini-library.

This file follows the Chapter 4 note-facing convention directly:

- `X ≤ O_Ψ(A)` means `P[X > A t] ≤ Ψ(t)⁻¹` for every `t ≥ 1`;
- `X = O_Ψ(A)` means the same bound for `|X|`;
- `Γ_σ` and `Ψ_σ` are the stretched-exponential and log-normal model classes.

The definitions are intentionally tail-based rather than Banach-space based:
the notes use a weak-tail calculus, and this is the theorem surface needed for
the later concentration arguments.
-/
/-- The upper-tail event `{X > a}`. -/
def upperTailEvent (X : Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | a < X ω}

variable [MeasurableSpace Ω]
/-- The weak-Orlicz upper-tail relation `X ≤ O_Ψ(A)` from the notes. -/
def IsBigOWith (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real (upperTailEvent X (A * t)) ≤ (Ψ t)⁻¹
/-- The symmetric weak-Orlicz relation `X = O_Ψ(A)`, defined through `|X|`. -/
def IsBigO (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  IsBigOWith μ Ψ (fun ω => |X ω|) A

/-- The stretched-exponential model tail function `Γ_σ(t) = exp(t^σ)`. -/
noncomputable def gammaSigma (σ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (t ^ σ)

end IndependentSums
end Homogenization

end

-- ==== Examples.scottnarmstrong__CoarseGraining.Dependencies.vb7e4f18e72ab.Homogenization.Probability.IndependentSums.PsiCalculus ====
section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
/-!
The first abstract calculus for Chapter 4 weak-Orlicz tails.

This file begins the formalization of the growth-condition arguments from the
notes. The immediate goal is Step 1 of the `O_Ψ` calculus: polynomial factors
can be absorbed into a dilation of the argument of `Ψ`.
-/

/-- A concrete growth constant for the stretched-exponential model class
`Γ_σ`, chosen so that the Chapter 4 growth hypothesis holds for every
`σ > 0`. -/
noncomputable def gammaGrowthConst (σ : ℝ) : ℝ :=
  max 2 ((1 + σ⁻¹) ^ (σ⁻¹))

end IndependentSums
end Homogenization

end

-- ==== Examples.scottnarmstrong__CoarseGraining.Dependencies.vb7e4f18e72ab.Homogenization.Probability.IndependentSums.Triangle ====
section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory
open scoped BigOperators
noncomputable section
variable {Ω ι : Type*}
/-!
Finite-sum reduction lemmas for the Chapter 4 weak-Orlicz triangle inequality.

This file formalizes the deterministic truncation step and the finite-family
Markov reduction from Step 5 of the notes. The one-variable tail integral bound
will plug into these lemmas downstream.
-/

section Measure
variable [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- The explicit stretched-exponential triangle constant obtained by feeding
the concrete `Γ_σ` growth witness into the general `O_Ψ` calculus. -/
noncomputable def gammaTriangleConst (σ : ℝ) : ℝ :=
  4 * gammaGrowthConst σ ^ (12 : ℝ)

end Measure
end
end IndependentSums
end Homogenization

end

-- ==== Examples.scottnarmstrong__CoarseGraining.Dependencies.vb7e4f18e72ab.Homogenization.Probability.IndependentSums.GammaSigma.Basic ====
section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}

/-- An explicit Chapter 4 moment-growth constant for the stretched-exponential
class `Γ_σ`. It is chosen large enough to absorb the elementary gamma-integral
bound used in the tail-to-moment direction. -/
noncomputable def gammaMomentConst (σ : ℝ) : ℝ :=
  (2 * Real.exp 1) * max 1 ((2 / (σ * Real.exp 1)) ^ σ⁻¹)
/-- Absolute `p^{1/σ}` moment growth with witness `M` for the stretched-
exponential Chapter 4 class. -/
def HasGammaMomentGrowthWith (μ : Measure Ω) (σ : ℝ) (X : Ω → ℝ) (M : ℝ) : Prop :=
  ∀ ⦃p : ℝ⦄, 1 ≤ p →
    Integrable (fun ω => |X ω| ^ p) μ ∧
      ∫ ω, |X ω| ^ p ∂μ ≤ (M * p ^ σ⁻¹) ^ p

end
end IndependentSums
end Homogenization

end

-- ==== Examples.scottnarmstrong__CoarseGraining.Examples.Example_d1a6bdfc86bd4b57e389_Operations ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
namespace Homogenization
namespace IndependentSums
open MeasureTheory
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω}
/-- The explicit `Γ_σ` moment-growth triangle constant obtained by combining
the Chapter 4 tail/moment bridge with the independent-sums `Γ_σ` triangle
inequality. -/
noncomputable def gammaMomentTriangleConst (σ : ℝ) : ℝ :=
  gammaMomentConst σ * Real.exp 1 * gammaTriangleConst σ


set_option linter.unusedVariables false in
/-- Finite-family generalized triangle inequality in witness-level
`Γ_σ` moment-growth form. -/
theorem hasGammaMomentGrowthWith_finset_sum
    {ι : Type*} (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) 
    (h_Homogenization_IndependentSums_gammaTriangleConst_pos : ∀ {σ : ℝ}, 0 < Homogenization.IndependentSums.gammaTriangleConst σ)
    (h_Homogenization_IndependentSums_isBigO_gammaSigma_of_hasGammaMomentGrowthWith : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ} {M σ : ℝ}
      [MeasureTheory.IsProbabilityMeasure μ],
      0 < σ →
        0 < M →
          Homogenization.IndependentSums.HasGammaMomentGrowthWith μ σ X M →
            Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ) X
              (Real.exp 1 * M))
    (h_Homogenization_IndependentSums_hasGammaMomentGrowthWith_of_isBigO_gammaSigma : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {X : Ω → ℝ} {K σ : ℝ}
      [MeasureTheory.IsProbabilityMeasure μ],
      0 < σ →
        0 < K →
          AEMeasurable X μ →
            Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ) X K →
              Homogenization.IndependentSums.HasGammaMomentGrowthWith μ σ X
                (Homogenization.IndependentSums.gammaMomentConst σ * K))
    (h_Homogenization_IndependentSums_isBigO_finset_sum_of_isBigO_gammaSigma : ∀ {Ω : Type u_1} {ι : Type u_2} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
      (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ} [MeasureTheory.IsFiniteMeasure μ],
      0 < σ →
        s.Nonempty →
          (∀ i ∈ s, 0 < a i) →
            (∀ i ∈ s,
                Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
                  (X i) (a i)) →
              (∀ i ∈ s, Measurable (X i)) →
                Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
                  (fun (ω : Ω) ↦ ∑ i ∈ s, X i ω)
                  (Homogenization.IndependentSums.gammaTriangleConst σ * s.sum a))
    :
    HasGammaMomentGrowthWith μ σ (fun ω => Finset.sum s (fun i => X i ω))
      (gammaMomentTriangleConst σ * Finset.sum s a) := by
  have hTail : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (Real.exp 1 * a i) := by
    intro i hi
    exact h_Homogenization_IndependentSums_isBigO_gammaSigma_of_hasGammaMomentGrowthWith
      (μ := μ) (X := X i) (M := a i) (σ := σ) hσ (ha i hi) (hX i hi)
  have hTailSum :
      IsBigO μ (gammaSigma σ) (fun ω => Finset.sum s (fun i => X i ω))
        (gammaTriangleConst σ * Finset.sum s (fun i => Real.exp 1 * a i)) := by
    refine h_Homogenization_IndependentSums_isBigO_finset_sum_of_isBigO_gammaSigma
      (μ := μ) (s := s) (X := X) (a := fun i => Real.exp 1 * a i) (σ := σ)
      hσ hs ?_ hTail hXm
    intro i hi
    exact mul_pos (by positivity) (ha i hi)
  have hScaledSum_pos : 0 < Finset.sum s (fun i => Real.exp 1 * a i) := by
    rcases hs with ⟨i₀, hi₀⟩
    refine Finset.sum_pos' ?_ ?_
    · intro i hi
      exact mul_nonneg (by positivity : 0 ≤ Real.exp 1) (ha i hi).le
    · refine ⟨i₀, hi₀, ?_⟩
      exact mul_pos (by positivity) (ha i₀ hi₀)
  have hTriangle_pos : 0 < gammaTriangleConst σ := h_Homogenization_IndependentSums_gammaTriangleConst_pos
  have hTailScale_pos :
      0 < gammaTriangleConst σ * Finset.sum s (fun i => Real.exp 1 * a i) := by
    exact mul_pos hTriangle_pos hScaledSum_pos
  have hSum_meas :
      AEMeasurable (fun ω => Finset.sum s (fun i => X i ω)) μ :=
    (Finset.measurable_sum (s := s) fun i hi => hXm i hi).aemeasurable
  have hMoment :=
    h_Homogenization_IndependentSums_hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := fun ω => Finset.sum s (fun i => X i ω))
      (K := gammaTriangleConst σ * Finset.sum s (fun i => Real.exp 1 * a i))
      (σ := σ) hσ hTailScale_pos hSum_meas hTailSum
  have hScaledSum :
      Finset.sum s (fun i => Real.exp 1 * a i) = Real.exp 1 * Finset.sum s a := by
    rw [← Finset.mul_sum]
  convert hMoment using 1
  rw [gammaMomentTriangleConst, hScaledSum]
  ring

end
end IndependentSums
end Homogenization
