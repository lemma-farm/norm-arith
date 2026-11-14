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

-- ==== Examples.scottnarmstrong__CoarseGraining.Examples.Example_94a9887b5e1f2ab850f6_Operations ====
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


set_option linter.unusedVariables false in
/-- Finite-maximum bound in witness-level `Γ_σ` moment-growth form. -/
theorem hasGammaMomentGrowthWith_finset_sup'_of_scales
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    [IsProbabilityMeasure μ]
    (hσ : 0 < σ) (hs_card : 2 ≤ s.card)
    (ha : ∀ i ∈ s, 0 < a i)
    (hX : ∀ i ∈ s, HasGammaMomentGrowthWith μ σ (X i) (a i))
    (hXm : ∀ i ∈ s, Measurable (X i)) 
    (h_Homogenization_IndependentSums_isBigO_gammaSigma_finset_sup__of_scales : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {ι : Type u_2}
      (s : Finset ι) (hs : s.Nonempty) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
      [MeasureTheory.IsFiniteMeasure μ],
      0 < σ →
        2 ≤ s.card →
          (∀ i ∈ s,
              Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
                (X i) (a i)) →
            Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ)
              (fun (ω : Ω) ↦ s.sup' hs fun (i : ι) ↦ X i ω)
              ((3 * Real.log (↑s.card : ℝ)) ^ σ⁻¹ * s.sup' hs a))
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
    :
    HasGammaMomentGrowthWith μ σ (fun ω => s.sup' hs (fun i => X i ω))
      (gammaMomentConst σ *
        (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) * (Real.exp 1 * s.sup' hs a))) := by
  have hTail : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (Real.exp 1 * a i) := by
    intro i hi
    exact h_Homogenization_IndependentSums_isBigO_gammaSigma_of_hasGammaMomentGrowthWith
      (μ := μ) (X := X i) (M := a i) (σ := σ) hσ (ha i hi) (hX i hi)
  have hTailSup :
      IsBigO μ (gammaSigma σ) (fun ω => s.sup' hs (fun i => X i ω))
        (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) *
          s.sup' hs (fun i => Real.exp 1 * a i)) := by
    exact h_Homogenization_IndependentSums_isBigO_gammaSigma_finset_sup__of_scales
      (μ := μ) (s := s) (hs := hs) (X := X) (a := fun i => Real.exp 1 * a i) (σ := σ)
      hσ hs_card hTail
  have hs_card_real : (2 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast hs_card
  have hlog_two_le : Real.log 2 ≤ Real.log (s.card : ℝ) := by
    exact Real.log_le_log (by norm_num) hs_card_real
  have hone_le_two_log : 1 ≤ 2 * Real.log (s.card : ℝ) := by
    nlinarith [Real.log_two_gt_d9, hlog_two_le]
  have hbase_one : 1 ≤ 3 * Real.log (s.card : ℝ) := by
    nlinarith [hone_le_two_log]
  have hbase_pos : 0 < 3 * Real.log (s.card : ℝ) := lt_of_lt_of_le zero_lt_one hbase_one
  have hCardFactor_pos : 0 < (3 * Real.log (s.card : ℝ)) ^ σ⁻¹ := by
    exact Real.rpow_pos_of_pos hbase_pos _
  have hs_nonempty : s.Nonempty := hs
  rcases hs with ⟨i₀, hi₀⟩
  have hSupScaled_pos : 0 < s.sup' hs_nonempty (fun i => Real.exp 1 * a i) := by
    exact lt_of_lt_of_le (mul_pos (by positivity) (ha i₀ hi₀))
      (Finset.le_sup' (fun i => Real.exp 1 * a i) hi₀)
  have hTailScale_pos :
      0 < ((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) *
        s.sup' hs_nonempty (fun i => Real.exp 1 * a i) := by
    exact mul_pos hCardFactor_pos hSupScaled_pos
  let Y : Ω → ℝ := s.sup' hs_nonempty X
  have hY_eq : Y = fun ω => s.sup' hs_nonempty (fun i => X i ω) := by
    funext ω
    change (s.sup' hs_nonempty X) ω = s.sup' hs_nonempty (fun i => X i ω)
    exact Finset.sup'_apply (C := fun _ => ℝ) hs_nonempty X ω
  have hSup_meas : AEMeasurable Y μ :=
    (Finset.measurable_sup' (hs := hs_nonempty) (f := X) fun i hi => hXm i hi).aemeasurable
  have hTailSup' :
      IsBigO μ (gammaSigma σ) Y
        (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) *
          s.sup' hs_nonempty (fun i => Real.exp 1 * a i)) := by
    simpa [hY_eq] using hTailSup
  have hMoment :=
    h_Homogenization_IndependentSums_hasGammaMomentGrowthWith_of_isBigO_gammaSigma
      (μ := μ) (X := Y)
      (K := ((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) *
        s.sup' hs_nonempty (fun i => Real.exp 1 * a i))
      (σ := σ) hσ hTailScale_pos hSup_meas hTailSup'
  have hScaledSup :
      s.sup' hs_nonempty (fun i => a i * Real.exp 1) = s.sup' hs_nonempty a * Real.exp 1 := by
    simpa using
      (Finset.sup'_mul₀ (a := Real.exp 1) (f := a) (s := s) (hs := hs_nonempty) (by positivity)).symm
  simpa [hY_eq, hScaledSup, mul_assoc, mul_left_comm, mul_comm] using hMoment
end
end IndependentSums
end Homogenization
