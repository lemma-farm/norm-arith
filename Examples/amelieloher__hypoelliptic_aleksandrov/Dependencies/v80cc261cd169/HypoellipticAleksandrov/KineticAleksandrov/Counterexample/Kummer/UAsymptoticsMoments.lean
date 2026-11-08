module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v80cc261cd169.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsTaylor
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gamma moments of the positive-axis expansion

This module evaluates the integral Taylor polynomial with the exact rising-factorial
coefficients of the source expansion.
-/
@[expose] public noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
theorem integral_gammaKernel (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a - 1)) =
      z ^ (-a) * Real.Gamma a := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hz
  rw [one_div, ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [mul_comm] using h
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
