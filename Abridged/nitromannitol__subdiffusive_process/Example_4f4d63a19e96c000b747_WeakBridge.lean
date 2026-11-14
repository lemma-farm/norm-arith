module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Integral.Gamma

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.va91a43bb116f.SubdiffusiveProcess.Model.OGammaLE ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-!
# Stretched-exponential moment control

`OGammaLE μ σ A X` specifies integrability and an expectation at most two
for `exp ((A⁻¹ max X 0)^σ)`. The paper's probability interpretation uses
`μ` a probability measure and `σ > 0`, `A > 0`. The predicate remains defined
for other measures and parameters using Lean's total inverse and real power.
Its integrability conjunct is part of the definition; a bound on a totalized
real integral alone would not supply it. `SubdiffusiveProcess.Assumptions.OGammaBridge` gives
its probability-tail comparison under the corresponding domain hypotheses.
-/
open MeasureTheory
/-- The expectation convention for `X ≤ O_{Γ_σ}(A)` used in Appendix A. -/
def SubdiffusiveProcess.OGammaLE {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (σ A : ℝ) (X : Ω → ℝ) : Prop :=
  Integrable
      (fun ω ↦ Real.exp ((A⁻¹ * max (X ω) 0) ^ σ)) μ ∧
    ∫ ω, Real.exp ((A⁻¹ * max (X ω) 0) ^ σ) ∂μ ≤ 2

end
end

-- ==== Examples.nitromannitol__subdiffusive_process.Dependencies.va91a43bb116f.Homogenization.Probability.IndependentSums.WeakOrlicz ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
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
end

-- ==== Examples.nitromannitol__subdiffusive_process.Examples.Example_4f4d63a19e96c000b747_WeakBridge ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false
@[expose] public section
/-! One-sided expectation/tail bridges and two-sided tail control. -/
open MeasureTheory Homogenization.IndependentSums
noncomputable section
namespace SubdiffusiveProcess.Probability.Orlicz
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
set_option linter.unusedVariables false in
lemma isBigO_gammaSigma_of_two_sided {s A : ℝ} (hs : 1 ≤ s) (hA : 0 < A)
    {X : Ω → ℝ} (hm : AEMeasurable X μ) (hp : SubdiffusiveProcess.OGammaLE μ s A X)
    (hn : SubdiffusiveProcess.OGammaLE μ s A (fun ω => -X ω)) 
    (h_SubdiffusiveProcess_CoarseGrainingVocab_OGamma_ogammaLE_add : ∀ {Omega : Type u_1} [inst : MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
      {sigma A1 A2 : ℝ},
      0 < A1 →
        0 < A2 →
          1 ≤ sigma →
            ∀ {X Y : Omega → ℝ},
              AEMeasurable X mu →
                AEMeasurable Y mu →
                  SubdiffusiveProcess.OGammaLE mu sigma A1 X →
                    SubdiffusiveProcess.OGammaLE mu sigma A2 Y →
                      SubdiffusiveProcess.OGammaLE mu sigma (A1 + A2) fun (omega : Omega) ↦
                        X omega + Y omega)
    (h_SubdiffusiveProcess_OGammaBridge_isBigO_gammaSigma_of_ogammaLE : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω} {σ A : ℝ} {X : Ω → ℝ},
      0 < σ →
        0 < A →
          (∀ (ω : Ω), 0 ≤ X ω) →
            SubdiffusiveProcess.OGammaLE μ σ A X →
              Homogenization.IndependentSums.IsBigO μ (Homogenization.IndependentSums.gammaSigma σ) X
                ((1 + Real.log 2) ^ σ⁻¹ * A))
    :
    IsBigO μ (gammaSigma s) X ((1 + Real.log 2) ^ s⁻¹ * (2 * A)) := by
  have hpos : SubdiffusiveProcess.OGammaLE μ s A (fun ω => max (X ω) 0) := by
    simpa only [SubdiffusiveProcess.OGammaLE, max_assoc, max_self] using hp
  have hneg : SubdiffusiveProcess.OGammaLE μ s A (fun ω => max (-X ω) 0) := by
    simpa only [SubdiffusiveProcess.OGammaLE, max_assoc, max_self] using hn
  have habs : ∀ x : ℝ, max x 0 + max (-x) 0 = |x| := by
    intro x
    rcases le_total 0 x with h | h
    · simp only [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h, add_zero]
    · simp only [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h, zero_add]
  have ho := h_SubdiffusiveProcess_CoarseGrainingVocab_OGamma_ogammaLE_add hA hA hs
    (hm.max aemeasurable_const) (hm.neg.max aemeasurable_const) hpos hneg
  have ha : SubdiffusiveProcess.OGammaLE μ s (2 * A) (fun ω => |X ω|) := by
    simpa only [Pi.neg_def, habs, two_mul] using ho
  have h := h_SubdiffusiveProcess_OGammaBridge_isBigO_gammaSigma_of_ogammaLE
    (lt_of_lt_of_le zero_lt_one hs) (mul_pos (by norm_num) hA) (fun ω => abs_nonneg (X ω)) ha
  simpa only [IsBigO, abs_abs] using h
end SubdiffusiveProcess.Probability.Orlicz
