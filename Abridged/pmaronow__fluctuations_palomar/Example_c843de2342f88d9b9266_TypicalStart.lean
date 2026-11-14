module

public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v730c1c8f88c9.SKConstants.FiniteGibbs ====
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
/-- The actual finite partition function, with the inverse temperature
permitted to be any real number. -/
@[expose] def gibbsPartition {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ x : Spin n, Real.exp (beta * quadraticHamiltonian W x)
/-- The Gibbs probability of an individual spin configuration. -/
@[expose] def gibbsProbability {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) : ℝ :=
  Real.exp (beta * quadraticHamiltonian W x) / gibbsPartition beta W

end SKConstants

end
end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Dependencies.v730c1c8f88c9.SKConstants.JointGibbs ====
public section
public section
noncomputable section
open scoped ENNReal
open scoped Classical
open MeasureTheory ProbabilityTheory
namespace SKConstants
/-- The measure represented by a finite vector of real weights. -/
@[expose] def finiteWeightMeasure {V : Type*} [Fintype V] [MeasurableSpace V]
    (p : V → ℝ) : Measure V := ∑ x, ENNReal.ofReal (p x) • Measure.dirac x

set_option linter.unusedVariables false in
axiom _root_.SKConstants.measurable_finiteWeightMeasure.{w_u_1,w_u_2} : ∀ {A : Type w_u_1} {V : Type w_u_2} [inst : MeasurableSpace A] [inst_1 : Fintype V]
  [inst_2 : MeasurableSpace V] (p : A → V → ℝ),
  (∀ (x : V), Measurable fun (a : A) ↦ p a x) →
    Measurable fun (a : A) ↦ SKConstants.finiteWeightMeasure (p a)

set_option linter.unusedVariables false in
axiom _root_.SKConstants.continuous_gibbsProbability : ∀ {n : ℕ} (beta : ℝ) (x : SKConstants.Spin n),
  Continuous fun (W : Matrix (Fin n) (Fin n) ℝ) ↦ SKConstants.gibbsProbability beta W x
/-- The actual conditional Gibbs law, without an assumed sampling kernel. -/
@[expose] def gibbsKernel (n : ℕ) (beta : ℝ) :
    Kernel (Matrix (Fin n) (Fin n) ℝ) (Spin n) where
  toFun W := finiteWeightMeasure (gibbsProbability beta W)
  measurable' := measurable_finiteWeightMeasure _
    (fun x ↦ (continuous_gibbsProbability beta x).measurable)
set_option linter.unusedVariables false in
axiom _root_.SKConstants.gibbsKernel_isMarkov : ∀ (n : ℕ) (beta : ℝ), ProbabilityTheory.IsMarkovKernel (SKConstants.gibbsKernel n beta)
attribute [instance] _root_.SKConstants.gibbsKernel_isMarkov
/-- First draw the disorder from `μ`, then a spin from its actual Gibbs law. -/
@[expose] def jointGibbsMeasure {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) := μ ⊗ₘ gibbsKernel n beta
set_option linter.unusedVariables false in
axiom _root_.SKConstants.jointGibbsMeasure_isProbability : ∀ {n : ℕ} (beta : ℝ) (μ : MeasureTheory.Measure (Matrix (Fin n) (Fin n) ℝ))
  [MeasureTheory.IsProbabilityMeasure μ],
  MeasureTheory.IsProbabilityMeasure (SKConstants.jointGibbsMeasure beta μ)
attribute [instance] _root_.SKConstants.jointGibbsMeasure_isProbability

end SKConstants

end
end
end

-- ==== Examples.pmaronow__fluctuations_palomar.Examples.Example_c843de2342f88d9b9266_TypicalStart ====
public section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory
namespace SKConstants
set_option linter.unusedVariables false in
theorem jointGibbs_typical_start_bound {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ]
    (good : Set (Matrix (Fin n) (Fin n) ℝ)) (hgood : MeasurableSet good)
    (err : Matrix (Fin n) (Fin n) ℝ × Spin n → ℝ) (herr : Measurable err)
    (herr_nonneg : ∀ z, 0 ≤ err z) (herr_le_one : ∀ z, err z ≤ 1)
    (B delta : ℝ) (hB : 0 ≤ B) (hdelta : 0 < delta)
    (haverage : ∀ W ∈ good, ∑ x, gibbsProbability beta W x * err (W, x) ≤ B) 
    (h_SKConstants_integral_gibbsKernel : ∀ {n : ℕ} (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (f : SKConstants.Spin n → ℝ),
      ∫ (x : SKConstants.Spin n),
          f
            x ∂(SKConstants.gibbsKernel n beta :
              Matrix (Fin n) (Fin n) ℝ → MeasureTheory.Measure (SKConstants.Spin n))
            W =
        ∑ x : SKConstants.Spin n, SKConstants.gibbsProbability beta W x * f x)
    :
    (jointGibbsMeasure beta μ).real {z | delta < err z} ≤
      μ.real goodᶜ + B / delta := by
  let ν := jointGibbsMeasure beta μ
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let f : Matrix (Fin n) (Fin n) ℝ × Spin n → ℝ :=
    (Prod.fst ⁻¹' good).indicator err
  have hfmeas : Measurable f := herr.indicator (hgood.preimage measurable_fst)
  have hfnonneg : ∀ z, 0 ≤ f z := by
    intro z
    exact Set.indicator_nonneg (fun z _ ↦ herr_nonneg z) z
  have hfle : ∀ z, f z ≤ 1 := by
    intro z
    by_cases hz : z.1 ∈ good <;> simp [f, hz, herr_le_one z]
  have hfint : Integrable f ν :=
    (integrable_const (1 : ℝ)).mono' hfmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (hfnonneg z)] using hfle z)
  have hint : ∫ z, f z ∂ν ≤ B := by
    rw [show ν = μ ⊗ₘ gibbsKernel n beta from rfl, Measure.integral_compProd hfint]
    calc
      (∫ W, ∫ x, f (W, x) ∂gibbsKernel n beta W ∂μ) ≤ ∫ _, B ∂μ := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun W ↦ integral_nonneg (fun x ↦ hfnonneg (W, x)))
          (integrable_const B)
        apply Filter.Eventually.of_forall
        intro W
        by_cases hW : W ∈ good
        · simpa [f, hW, h_SKConstants_integral_gibbsKernel] using haverage W hW
        · simp [f, hW, hB]
      _ = B := by simp
  have hmarkov : ν {z | z.1 ∈ good ∧ delta < err z} ≤ ENNReal.ofReal (B / delta) := by
    refine ((hfint.div_const delta).measure_le_integral
      (Filter.Eventually.of_forall fun z ↦ div_nonneg (hfnonneg z) hdelta.le) ?_).trans ?_
    · intro z hz
      exact (le_div_iff₀ hdelta).mpr (by simpa [f, hz.1] using hz.2.le)
    · rw [integral_div]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hint hdelta.le)
  have hmarkovreal : ν.real {z | z.1 ∈ good ∧ delta < err z} ≤ B / delta := by
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hB hdelta.le) hmarkov
  have hbad : ν.real (Prod.fst ⁻¹' goodᶜ) = μ.real goodᶜ := by
    change ((μ ⊗ₘ gibbsKernel n beta) (Prod.fst ⁻¹' goodᶜ)).toReal = _
    rw [← Measure.fst_apply hgood.compl, Measure.fst_compProd]
    rfl
  calc
    ν.real {z | delta < err z} ≤
        ν.real ((Prod.fst ⁻¹' goodᶜ) ∪ {z | z.1 ∈ good ∧ delta < err z}) := by
      apply measureReal_mono ?_ (measure_ne_top ν _)
      intro z hz
      by_cases hg : z.1 ∈ good
      · exact Or.inr ⟨hg, hz⟩
      · exact Or.inl hg
    _ ≤ ν.real (Prod.fst ⁻¹' goodᶜ) + ν.real {z | z.1 ∈ good ∧ delta < err z} :=
      measureReal_union_le _ _
    _ ≤ μ.real goodᶜ + B / delta := by rw [hbad]; exact add_le_add le_rfl hmarkovreal
end SKConstants
