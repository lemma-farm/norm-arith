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

-- ==== Examples.scottnarmstrong__CoarseGraining.Dependencies.v1297d2aae338.Homogenization.Probability.IndependentSums.WeakOrlicz ====
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

@[simp] axiom mem_upperTailEvent {X : Ω → ℝ} {a : ℝ} {ω : Ω} :
    ω ∈ upperTailEvent X a ↔ a < X ω

variable [MeasurableSpace Ω]
/-- The weak-Orlicz upper-tail relation `X ≤ O_Ψ(A)` from the notes. -/
def IsBigOWith (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real (upperTailEvent X (A * t)) ≤ (Ψ t)⁻¹

/-- The stretched-exponential model tail function `Γ_σ(t) = exp(t^σ)`. -/
noncomputable def gammaSigma (σ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (t ^ σ)

axiom isBigOWith_gammaSigma_iff {μ : Measure Ω} {X : Ω → ℝ} {A σ : ℝ} :
    IsBigOWith μ (gammaSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (upperTailEvent X (A * t)) ≤ Real.exp (-(t ^ σ))

end IndependentSums
end Homogenization

end

-- ==== Examples.scottnarmstrong__CoarseGraining.Examples.Example_19b4cd12e50d97c389f0_Operations ====
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


/-- Finite-maximum bound in the stretched-exponential class. This is the
finite-family version of the Chapter 4 maximum lemma with the note-facing
constant `(3 log N)^{1/σ}`. -/
theorem isBigOWith_gammaSigma_finset_sup'
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {X : ι → Ω → ℝ} {A σ : ℝ} [IsFiniteMeasure μ]
    (hσ : 0 < σ) (hs_card : 2 ≤ s.card)
    (hX : ∀ i ∈ s, IsBigOWith μ (gammaSigma σ) (X i) A) :
    IsBigOWith μ (gammaSigma σ) (fun ω => s.sup' hs (fun i => X i ω))
      (((3 * Real.log (s.card : ℝ)) ^ σ⁻¹) * A) := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  let n : ℝ := s.card
  let L : ℝ := (3 * Real.log n) ^ σ⁻¹
  have hs_card_real : (2 : ℝ) ≤ n := by
    change (2 : ℝ) ≤ (s.card : ℝ)
    exact_mod_cast hs_card
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  have hlog_two_lt : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog_two_le : Real.log 2 ≤ Real.log n := by
    exact Real.log_le_log (by norm_num) hs_card_real
  have hone_le_two_log : 1 ≤ 2 * Real.log n := by
    nlinarith
  have hbase_one : 1 ≤ 3 * Real.log n := by
    nlinarith [hone_le_two_log]
  have hbase_nonneg : 0 ≤ 3 * Real.log n := le_trans zero_le_one hbase_one
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.rpow_nonneg hbase_nonneg _
  have hL_one : 1 ≤ L := by
    dsimp [L]
    exact Real.one_le_rpow hbase_one (inv_nonneg.mpr hσ.le)
  have hLt_one : 1 ≤ L * t := by
    nlinarith
  have hsubset :
      upperTailEvent (fun ω => s.sup' hs (fun i => X i ω)) ((L * A) * t) ⊆
        ⋃ i ∈ s, upperTailEvent (X i) (A * (L * t)) := by
    intro ω hω
    have hω' : A * (L * t) < s.sup' hs (fun i => X i ω) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hω
    rcases (Finset.lt_sup'_iff hs).1 hω' with ⟨i, hi, hiω⟩
    exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨hi, hiω⟩⟩
  have hLpow : L ^ σ = 3 * Real.log n := by
    dsimp [L]
    rw [Real.rpow_inv_rpow hbase_nonneg hσ.ne']
  have hmulpow : (L * t) ^ σ = (3 * Real.log n) * t ^ σ := by
    calc
      (L * t) ^ σ = L ^ σ * t ^ σ := by
        rw [Real.mul_rpow hL_nonneg (le_trans zero_le_one ht)]
      _ = (3 * Real.log n) * t ^ σ := by
        rw [hLpow]
  have htpow_one : 1 ≤ t ^ σ := Real.one_le_rpow ht hσ.le
  have hunion_ne_top :
      μ (⋃ i ∈ s, upperTailEvent (X i) (A * (L * t))) ≠ ⊤ :=
    measure_ne_top μ _
  calc
    μ.real (upperTailEvent (fun ω => s.sup' hs (fun i => X i ω)) (((3 * Real.log n) ^ σ⁻¹ * A) * t))
      ≤ μ.real (⋃ i ∈ s, upperTailEvent (X i) (A * (L * t))) := by
          simpa [L, mul_assoc, mul_left_comm, mul_comm] using
            (measureReal_mono hsubset hunion_ne_top)
    _ ≤ ∑ i ∈ s, μ.real (upperTailEvent (X i) (A * (L * t))) := by
          simpa using measureReal_biUnion_finset_le s
            (fun i => upperTailEvent (X i) (A * (L * t)))
    _ ≤ ∑ _i ∈ s, Real.exp (-((L * t) ^ σ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          simpa [gammaSigma, ← Real.exp_neg] using hX i hi hLt_one
    _ = n * Real.exp (-((L * t) ^ σ)) := by
          simp [n]
    _ = Real.exp (Real.log n - (L * t) ^ σ) := by
          calc
            n * Real.exp (-((L * t) ^ σ)) = Real.exp (Real.log n) * Real.exp (-((L * t) ^ σ)) := by
              rw [Real.exp_log hn_pos]
            _ = Real.exp (Real.log n + -((L * t) ^ σ)) := by
              rw [← Real.exp_add]
            _ = Real.exp (Real.log n - (L * t) ^ σ) := by
              simp [sub_eq_add_neg]
    _ ≤ Real.exp (-(t ^ σ)) := by
          refine (Real.exp_le_exp).2 ?_
          rw [hmulpow]
          nlinarith [hone_le_two_log, htpow_one]
    _ = Real.exp (-(t ^ σ)) := rfl
end
end IndependentSums
end Homogenization
