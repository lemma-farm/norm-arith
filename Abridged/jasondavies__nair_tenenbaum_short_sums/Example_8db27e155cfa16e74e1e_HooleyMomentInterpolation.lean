module

public import Mathlib

-- ==== Examples.jasondavies__nair_tenenbaum_short_sums.Examples.Example_8db27e155cfa16e74e1e_HooleyMomentInterpolation ====
/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
set_option autoImplicit false
/-! # Interpolation of Hooley's integral moments

Weighted arithmetic-geometric means give the interpolation between `M₁=τ`
and `M_q`. This supplies the exponents of `τ` and `M_q` in the mixed-term
estimate used in the weighted mean proof.
-/
@[expose] public section
namespace NairTenenbaum
open Finset Real MeasureTheory
theorem moment_interpolation_pointwise {x A B a b : ℝ} {j q : ℕ}
    (hx : 0 ≤ x) (hA : 0 < A) (hB : 0 < B) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hexp : a + (q : ℝ) * b = j) (hj : 0 < j) :
    x ^ j ≤ A ^ a * B ^ b * (a * (x / A) + b * (x ^ q / B)) := by
  by_cases hx₀ : x = 0
  · rw [hx₀, zero_pow hj.ne']
    positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx₀)
  have H := mul_le_mul_of_nonneg_left
    (Real.geom_mean_le_arith_mean2_weighted ha hb (div_nonneg hx hA.le)
      (div_nonneg (pow_nonneg hx q) hB.le) hab)
    (show 0 ≤ A ^ a * B ^ b by positivity)
  have hAp : A ^ a ≠ 0 := (Real.rpow_pos_of_pos hA a).ne'
  have hBp : B ^ b ≠ 0 := (Real.rpow_pos_of_pos hB b).ne'
  have Hpower : (x ^ q) ^ b = x ^ ((q : ℝ) * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have Heq : A ^ a * B ^ b * ((x / A) ^ a * (x ^ q / B) ^ b) = x ^ j := by
    rw [Real.div_rpow hx hA.le, Real.div_rpow (pow_nonneg hx q) hB.le, Hpower]
    calc
      _ = x ^ a * x ^ ((q : ℝ) * b) := by field_simp
      _ = x ^ j := by rw [← Real.rpow_add hxpos, hexp, Real.rpow_natCast]
  rw [Heq] at H
  exact H

end NairTenenbaum
