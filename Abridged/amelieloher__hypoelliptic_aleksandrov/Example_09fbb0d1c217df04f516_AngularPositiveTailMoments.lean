module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Tactic

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vb511bf2c3c61.HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus ====
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

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_09fbb0d1c217df04f516_AngularPositiveTailMoments ====
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
/-- The integrated angular identity bounds the positive first moment using nonnegative h. -/
theorem bellmanAngularFirstMoment_bound (β : ℝ) (f h J : ℝ → ℝ)
    (hβ : 3 ≤ β) (hi : LocallyIntegrable f volume)
    (hf : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    {y : ℝ} (hy : 0 < y) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_bellmanAngularSecondMoment_le : ∀ {f : ℝ → ℝ},
      MeasureTheory.LocallyIntegrable f MeasureTheory.MeasureSpace.volume →
        (∀ᵐ (z : ℝ), 0 ≤ f z) →
          ∀ {y : ℝ},
            0 ≤ y →
              HypoellipticAleksandrov.KineticAleksandrov.bellmanAngularSecondMoment f y ≤
                y * HypoellipticAleksandrov.KineticAleksandrov.bellmanAngularFirstMoment f y)
    :
    bellmanAngularFirstMoment f y ≤ 3 * (h 0 / y + J 0) := by
  have hm := h_HypoellipticAleksandrov_KineticAleksandrov_bellmanAngularSecondMoment_le hi hf hy.le
  have hp : 0 ≤ (β - 3) / 3 := by linarith
  have hb := mul_le_mul_of_nonneg_left hm hp
  have hn := hh y
  rw [he y] at hn
  apply le_of_mul_le_mul_right (a := y) _ hy
  have heq : (3 * (h 0 / y + J 0)) * y = 3 * (h 0 + J 0 * y) := by
    field_simp [hy.ne']
  rw [heq]
  nlinarith
end HypoellipticAleksandrov.KineticAleksandrov
