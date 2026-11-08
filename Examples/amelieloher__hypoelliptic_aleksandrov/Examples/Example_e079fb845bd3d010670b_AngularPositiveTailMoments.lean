module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vdae55150572e.HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import Mathlib.Tactic
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
theorem bellmanAngularSecondMoment_le {f : ℝ → ℝ}
    (hi : LocallyIntegrable f volume) (hf : ∀ᵐ z ∂volume, 0 ≤ f z)
    {y : ℝ} (hy : 0 ≤ y) :
    bellmanAngularSecondMoment f y ≤ y * bellmanAngularFirstMoment f y := by
  rw [bellmanAngularSecondMoment, bellmanAngularFirstMoment,
    ← intervalIntegral.integral_const_mul]
  have hfirst : IntervalIntegrable (fun z => z * f z) volume 0 y := by
    simpa only [pow_one] using bellmanAngularMoment_intervalIntegrable hi 0 y 1
  apply intervalIntegral.integral_mono_ae_restrict hy
    (bellmanAngularMoment_intervalIntegrable hi 0 y 2) (hfirst.const_mul y)
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  filter_upwards [hf] with z hz
  intro hzy
  nlinarith [mul_nonneg (sub_nonneg.mpr hzy.2) (mul_nonneg hzy.1 hz)]
end HypoellipticAleksandrov.KineticAleksandrov
