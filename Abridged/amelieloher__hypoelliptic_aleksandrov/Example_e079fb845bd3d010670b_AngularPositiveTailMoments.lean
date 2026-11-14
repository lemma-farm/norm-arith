module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vdae55150572e.HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Interval integrations of the angular density and flux identities -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
/-- The oriented first angular moment from the source. -/
def bellmanAngularFirstMoment (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in 0..y, z * f z
/-- The oriented second angular moment from the source. -/
def bellmanAngularSecondMoment (f : ℝ → ℝ) (y : ℝ) : ℝ := ∫ z in 0..y, z ^ 2 * f z

end HypoellipticAleksandrov.KineticAleksandrov

end
end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_e079fb845bd3d010670b_AngularPositiveTailMoments ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Positive angular moment inequalities without pointwise density assumptions -/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set
set_option linter.unusedVariables false in
theorem bellmanAngularSecondMoment_le {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y : ℝ} (hy : 0 ≤ y) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_bellmanAngularMoment_intervalIntegrable : ∀ {f : ℝ → ℝ},
      MeasureTheory.LocallyIntegrable f MeasureTheory.MeasureSpace.volume →
        ∀ (a b : ℝ) (n : ℕ),
          IntervalIntegrable (fun (z : ℝ) ↦ z ^ n * f z) MeasureTheory.MeasureSpace.volume a b)
    :
    bellmanAngularSecondMoment f y ≤ y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularSecondMoment, bellmanAngularFirstMoment,
    ← intervalIntegral.integral_const_mul]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume 0 y := by
    simpa only [pow_one] using h_HypoellipticAleksandrov_KineticAleksandrov_bellmanAngularMoment_intervalIntegrable hi 0 y 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (h_HypoellipticAleksandrov_KineticAleksandrov_bellmanAngularMoment_intervalIntegrable hi 0 y 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.2) (mul_nonneg hzy.1 hz)]
end HypoellipticAleksandrov.KineticAleksandrov
