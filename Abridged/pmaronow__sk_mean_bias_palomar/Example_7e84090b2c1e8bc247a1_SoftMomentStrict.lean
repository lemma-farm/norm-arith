module

public import Mathlib
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Hyperbolic ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Hyperbolic identities and pointwise inequalities

The pointwise analytic ingredients of arXiv:2604.11921v2, Sections 3 and 4.
All hyperbolic functions are the actual real functions from mathlib.
-/
namespace Paper
noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

end Paper

end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.Gaussian ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Concrete Gaussian quantities

The expectations in the paper are Bochner integrals against mathlib's standard
Gaussian probability measure. We keep `q` explicit; existence and uniqueness of
the fixed point are proved separately in `FixedPointUnique.lean`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
noncomputable def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1
noncomputable def gaussianField (β h q z : ℝ) : ℝ := β * Real.sqrt q * z + h
noncomputable def overlapMap (β h q : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (gaussianField β h q z) ^ 2)
noncomputable def atParameter (β h q : ℝ) : ℝ :=
  β ^ 2 * gaussianExpectation (fun z => sech (gaussianField β h q z) ^ 4)
end Paper

end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.RSSoft ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# The explicit replica-symmetric heat solution before the interface

Both spatial derivatives and the backward heat PDE are verified for the
paper's actual Gaussian formula. Identifying this explicit formula with the
weak Parisi solution still requires the separately cited uniqueness theory.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper
noncomputable def rsSoftDx (β q t x : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (x + β * Real.sqrt (q - t) * z))

 
 
 
end Paper

end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Dependencies.vde6e39ad4a3d.Paper.SoftMoment ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Actual soft Gaussian moment and the left-hand bound

The second moment is the literal squared Gaussian conditional `tanh`
expectation, evaluated at the Gaussian field at time `t`. Gaussian Poincaré
and the independent-sum law are proved in the imported modules. This file
assumes neither a Poincaré estimate nor the desired moment sign.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace Paper
/-- The actual Gaussian conditional second moment before the RS interface. -/
def softSecondMoment (β h q t : ℝ) : ℝ :=
  gaussianExpectation (fun z => rsSoftDx β q t (gaussianField β h t z) ^ 2)

end Paper

end
end
end

-- ==== Examples.pmaronow__sk_mean_bias_palomar.Examples.Example_7e84090b2c1e8bc247a1_SoftMomentStrict ====
set_option autoImplicit false
@[expose] public section
/-!
# Strict left-hand moment bound and unique RS variational minimum

Strict Gaussian Poincaré remains strict after Gaussian averaging. Therefore
the soft second moment exceeds time even when the AT parameter equals one.
Together with the strict hard bound, the actual variational integral has its
unique minimum at the fixed-point overlap.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
namespace Paper

set_option linter.unusedVariables false in
theorem softSecondMoment_variance_bound_strict {β h q t : ℝ}
    (hβ : 0 < β) (ht : t ∈ Ico (0 : ℝ) q) 
    (h_Paper_sech_pos : ∀ (x : ℝ), 0 < Paper.sech x)
    (h_Paper_gaussian_continuous_tanh : Continuous Real.tanh)
    (h_Paper_probability_integral_lt : ∀ {μ : MeasureTheory.Measure ℝ} [MeasureTheory.IsProbabilityMeasure μ] {f g : ℝ → ℝ},
      MeasureTheory.Integrable f μ →
        MeasureTheory.Integrable g μ → (∀ (x : ℝ), f x < g x) → ∫ (x : ℝ), f x ∂μ < ∫ (x : ℝ), g x ∂μ)
    (h_Paper_integrable_softSecondMoment : ∀ (β h q t : ℝ),
      MeasureTheory.Integrable (fun (z : ℝ) ↦ Paper.rsSoftDx β q t (Paper.gaussianField β h t z) ^ 2)
        (ProbabilityTheory.gaussianReal 0 1))
    (h_Paper_soft_gaussian_terminal_collapse : ∀ (f : ℝ → ℝ) (β h q t C : ℝ),
      0 ≤ β →
        t ∈ Set.Icc 0 q →
          Continuous f →
            (∀ (x : ℝ), ‖f x‖ ≤ C) →
              (Paper.gaussianExpectation fun (z : ℝ) ↦
                  Paper.gaussianExpectation fun (w : ℝ) ↦
                    f (Paper.gaussianField β h t z + β * √(q - t) * w)) =
                Paper.gaussianExpectation fun (z : ℝ) ↦ f (Paper.gaussianField β h q z))
    (h_Paper_gaussian_continuous_sech : Continuous Paper.sech)
    (h_Paper_integrable_nested_gaussian_field : ∀ (f : ℝ → ℝ) (β h t a C : ℝ),
      Continuous f →
        (∀ (x : ℝ), ‖f x‖ ≤ C) →
          MeasureTheory.Integrable
            (fun (z : ℝ) ↦
              Paper.gaussianExpectation fun (w : ℝ) ↦ f (Paper.gaussianField β h t z + a * w))
            (ProbabilityTheory.gaussianReal 0 1))
    (h_Paper_sech_fourth_le_one : ∀ (x : ℝ), Paper.sech x ^ 4 ≤ 1)
    (h_Paper_tanh_sq_le_one : ∀ (x : ℝ), Real.tanh x ^ 2 ≤ 1)
    (h_Paper_gaussian_poincare_tanh_strict : ∀ (x a : ℝ),
      0 < a →
        (Paper.gaussianExpectation fun (z : ℝ) ↦ Real.tanh (x + a * z) ^ 2) -
            (Paper.gaussianExpectation fun (z : ℝ) ↦ Real.tanh (x + a * z)) ^ 2 <
          a ^ 2 * Paper.gaussianExpectation fun (z : ℝ) ↦ Paper.sech (x + a * z) ^ 4)
    :
    overlapMap β h q - softSecondMoment β h q t < atParameter β h q * (q - t) := by
  let a : ℝ := β * Real.sqrt (q - t)
  have ha : 0 < a := mul_pos hβ (Real.sqrt_pos.mpr (sub_pos.mpr ht.2))
  have hTanhBound : ∀ x, ‖Real.tanh x ^ 2‖ ≤ 1 := by
    intro x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h_Paper_tanh_sq_le_one x
  have hSechBound : ∀ x, ‖sech x ^ 4‖ ≤ 1 := by
    intro x
    rw [Real.norm_of_nonneg (pow_nonneg (h_Paper_sech_pos x).le 4)]
    exact h_Paper_sech_fourth_le_one x
  have hiT := h_Paper_integrable_nested_gaussian_field (fun x => Real.tanh x ^ 2) β h t a 1
    (h_Paper_gaussian_continuous_tanh.pow 2) hTanhBound
  have hiS := h_Paper_integrable_softSecondMoment β h q t
  have hi4 := h_Paper_integrable_nested_gaussian_field (fun x => sech x ^ 4) β h t a 1
    (h_Paper_gaussian_continuous_sech.pow 4) hSechBound
  have hineq := h_Paper_probability_integral_lt (hiT.sub hiS) (hi4.const_mul (a ^ 2)) (fun z => by
    have hp := h_Paper_gaussian_poincare_tanh_strict (gaussianField β h t z) a ha
    simpa only [rsSoftDx, Pi.sub_apply, a] using hp)
  simp only [Pi.sub_apply] at hineq
  rw [integral_sub hiT hiS, integral_const_mul] at hineq
  change gaussianExpectation (fun z => gaussianExpectation
      (fun w => Real.tanh (gaussianField β h t z + a * w) ^ 2)) - softSecondMoment β h q t <
    a ^ 2 * gaussianExpectation (fun z => gaussianExpectation
      (fun w => sech (gaussianField β h t z + a * w) ^ 4)) at hineq
  have hcollapse2 := h_Paper_soft_gaussian_terminal_collapse (fun x => Real.tanh x ^ 2)
    β h q t 1 hβ.le ⟨ht.1, ht.2.le⟩ (h_Paper_gaussian_continuous_tanh.pow 2) hTanhBound
  have hcollapse4 := h_Paper_soft_gaussian_terminal_collapse (fun x => sech x ^ 4)
    β h q t 1 hβ.le ⟨ht.1, ht.2.le⟩ (h_Paper_gaussian_continuous_sech.pow 4) hSechBound
  change gaussianExpectation (fun z => gaussianExpectation
    (fun w => Real.tanh (gaussianField β h t z + a * w) ^ 2)) = overlapMap β h q at hcollapse2
  change gaussianExpectation (fun z => gaussianExpectation
    (fun w => sech (gaussianField β h t z + a * w) ^ 4)) = _ at hcollapse4
  rw [hcollapse2, hcollapse4] at hineq
  have ha2 : a ^ 2 = β ^ 2 * (q - t) := by
    dsimp [a]
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr ht.2.le)]
  rw [ha2] at hineq
  unfold atParameter
  nlinarith [hineq]
end Paper
