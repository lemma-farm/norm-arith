module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_3f4bc0f02c771a6b39b4_DensityFromTestsApproximation ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Compact approximation inside the smooth-test region

Multiplication by a fixed cutoff preserves compact interior support and contracts the
approximation error. The approximation measure may be the sum of reference and tested measures.
-/
@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

set_option linter.unusedVariables false in
/-- A compactly supported `Lp` function admits continuous approximants supported inside `U`. -/
theorem exists_continuous_test_approximation (η : Measure E)
    [η.Regular] {p : ℝ≥0∞} (hpt : p ≠ ∞)
    {f : E → ℝ} (hfp : MemLp f p η) {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) (hfK : Function.support f ⊆ K)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_exists_test_cutoff : ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
      {K U : Set E},
      IsCompact K →
        IsOpen U →
          K ⊆ U →
            ∃ (χ : E → ℝ),
              ContDiff ℝ (↑⊤ : WithTop ℕ∞) χ ∧
                HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ (∀ (x : E), 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∀ x ∈ K, χ x = 1)
    :
    ∃ g : E → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      eLpNorm (g - f) p η ≤ ε := by
  obtain ⟨χ, hs, hc, hχU, h01, h1⟩ := h_HypoellipticAleksandrov_KineticAleksandrov_Occupation_exists_test_cutoff hK hU hKU
  obtain ⟨a, _hac, han, ha, _hap⟩ :=
    hfp.exists_hasCompactSupport_eLpNorm_sub_le hpt hε
  refine ⟨fun x => χ x * a x, hs.continuous.mul ha, hc.mul_right,
    tsupport_mul_subset_left.trans hχU, ?_⟩
  have heq : (fun x => χ x * a x) - f = fun x => χ x * (a x - f x) := by
    funext x
    by_cases hx : f x = 0
    · simp [hx]
    · have hxK : x ∈ K := hfK hx
      simp [h1 x hxK]
  rw [heq]
  refine (eLpNorm_mono_ae (g := a - f)
    (hs.continuous.aestronglyMeasurable.mul (ha.aestronglyMeasurable.sub
      hfp.aestronglyMeasurable)) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
  · change ‖χ x * (a x - f x)‖ ≤ ‖a x - f x‖
    rw [norm_mul, Real.norm_of_nonneg (h01 x).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (h01 x).2
  · simpa only [eLpNorm_sub_comm] using han

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
