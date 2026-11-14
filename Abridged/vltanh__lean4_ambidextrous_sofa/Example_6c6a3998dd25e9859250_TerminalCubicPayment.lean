module

public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.TerminalThreeSupports ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Three actual supports at a proper terminal angle

The two diagonal supports and the first terminal support give simultaneous
upper bounds for the actual cap roof and lower bounds for its actual
partial barrier. The latter retains the whole outgoing first wall.

The terminal position is obtained from the support maximum of the cap.
Its compatibility with the diagonal position is proved at actual support
points. The top-endpoint alternatives likewise come from actual points of
a height-one affine-middle joint maximum.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
def terminalSlope (α : ℝ) : ℝ := Real.cos α / Real.sin α

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CircleAverage ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Symmetric averages of the circle slope

On the positive unit interval the circle slope `x / sqrt (1 - x^2)`
is increasing and convex. Its symmetric interval average is consequently
increasing in the center and in the interval width, and convex in the
center. The average is also evaluated exactly as a difference of two
circle heights.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
def circleHeight (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)
def circleSlope (x : ℝ) : ℝ := x / circleHeight x
def circleAverage (q y : ℝ) : ℝ :=
  ∫ t in (-1 / 2 : ℝ)..(1 / 2 : ℝ), circleSlope (y + q * t)

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.TerminalCircleEndpoints ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Exact endpoint margins for the terminal circle comparison

Use the cosine of the established terminal-angle endpoint. Four unit-seed
Newton updates bound this root and its sine. The resulting gap is concave in
cap width, so two endpoint checks control the whole width interval.
The circle-height bounds at both endpoints use the same Newton formulas.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
/-- One Newton step gives an upper square-root bound; dividing the radicand
by that upper bound gives a lower bound. Both width endpoints use these same formulas. -/
def circleNewtonUpper (q x : ℝ) : ℝ := (x + q / x) / 2

/-- Use the unit circle's upper root bound as the starting value for every
endpoint root. All four updates are the same arithmetic operation. -/
def circleRootUpper (q : ℝ) : ℝ :=
  circleNewtonUpper q (circleNewtonUpper q (circleNewtonUpper q (circleNewtonUpper q 1)))
def circleRootLower (q : ℝ) : ℝ := q / circleRootUpper q
def terminalCircleCosine : ℝ := Real.sqrt (9 / 73)
def terminalCircleSine : ℝ := Real.sqrt (64 / 73)
/-- The common Newton procedure also supplies the sine price in the
cubic payment; no separate linear sine approximation is chosen. -/
def terminalCircleSineLower : ℝ := circleRootLower (64 / 73)

/-- The actual circle gap at a cap width. Its minimum is forced to an
endpoint by concavity; it is not an independently chosen tolerance. -/
def terminalCircleEndpointGap (C : ℝ) : ℝ :=
  (2 * C - terminalCircleCosine) / terminalCircleSine -
    circleAverage terminalCircleCosine (C - terminalCircleCosine ^ 3 / 8)
def terminalCircleGap : ℝ :=
  min (terminalCircleEndpointGap (1 / 2)) (terminalCircleEndpointGap (37 / 50))
/-- The normalized price required by the angular overlap's cubic moment. -/
def terminalCubicPrice : ℝ :=
  ((4 / 5) * (2 / 3) ^ 3 * (3 / 8) ^ 2) / (6 * (2 / 3) * terminalCircleSineLower)

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.ProperExcessBudget ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# One angular budget for the proper reflected excess

Compare the whole crossing-and-decay time with its zero-tilt baseline.
Differences of squares price changes in width, height and impulse energy.
The two middle orientations spend one common angular budget, and a single
Newton baseline check bounds the excess deadline linearly in terminal slope.
-/
noncomputable section
namespace AmbidextrousSofa.Analysis
abbrev properAngularDeadline (k : ℝ) : ℝ := 11 / 15 + 2 * k / 3
end AmbidextrousSofa.Analysis

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Examples.Example_6c6a3998dd25e9859250_TerminalCubicPayment ====
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# The exact weighted cubic payment for a late companion excess

The weighted error in the proper-terminal comparison is an ordinary
integral of the positive curvature excess. Its trigonometric kernel is
nonnegative before the selected prefix endpoint. A linear late-tail
envelope therefore pays a cubic amount, with all clipping retained.

The overlap is proportional to terminal slope, so its cubic moment
pays the terminal cosine margin throughout the slope range. The same
quadratic half-angle cosine bound supplies the prefix cut.
-/
noncomputable section
open Set Filter MeasureTheory
namespace AmbidextrousSofa
open Analysis
def terminalWeightedExcess (v : ℝ → ℝ) (θ : ℝ) : ℝ :=
  ∫ t in 0..θ, max (v t - 1) 0 *
    (Real.tan θ * Real.cos t - Real.sin t)


set_option linter.unusedVariables false in
/-- One angularly scaled cubic payment covers the entire terminal-slope range. -/
theorem terminalWeightedExcess_lt_allowance_of_angular_budget
    {v : ℝ → ℝ} {C T α : ℝ}
    (hCT : 0 ≤ C - T) (hCT1 : C - T ≤ 37 / 50)
    (hα0 : 0 < α) (hαL : α < Real.pi / 2) (hk1 : terminalSlope α ≤ 3 / 8)
    (hint : IntervalIntegrable (fun t : ℝ => max (v t - 1) 0 *
      (Real.tan (Real.arcsin (C - T)) * Real.cos t - Real.sin t))
        volume 0 (Real.arcsin (C - T)))
    (hbound : ∀ᵐ t ∂volume.restrict (Icc 0 (Real.arcsin (C - T))),
      max (v t - 1) 0 ≤ (4 / 5 : ℝ) *
        max (t - (Real.pi / 2 - properAngularDeadline (terminalSlope α))) 0) 
    (h_AmbidextrousSofa_terminalCircleSineLower_le_of_slope : ∀ {c s : ℝ},
      0 ≤ c → 0 < s → c ^ 2 + s ^ 2 = 1 → c ≤ 3 / 8 * s → AmbidextrousSofa.terminalCircleSineLower ≤ s)
    (h_AmbidextrousSofa_terminalWeightedExcess_le_cubic : ∀ {v : ℝ → ℝ} {θ t₀ K : ℝ},
      0 ≤ θ →
        θ < Real.pi / 2 →
          0 ≤ t₀ →
            0 ≤ K →
              IntervalIntegrable
                  (fun (t : ℝ) ↦ Max.max (v t - 1) 0 * (Real.tan θ * Real.cos t - Real.sin t))
                  MeasureTheory.MeasureSpace.volume 0 θ →
                (∀ᵐ (t : ℝ) ∂MeasureTheory.MeasureSpace.volume.restrict (Set.Icc 0 θ),
                    Max.max (v t - 1) 0 ≤ K * Max.max (t - t₀) 0) →
                  AmbidextrousSofa.terminalWeightedExcess v θ ≤
                    K * Max.max (θ - t₀) 0 ^ 3 / (6 * Real.cos θ))
    (h_AmbidextrousSofa_terminalSlope_pos : ∀ {α : ℝ}, 0 < α → α < Real.pi / 2 → 0 < AmbidextrousSofa.terminalSlope α)
    (h_AmbidextrousSofa_Analysis_eleven_fifteenths_lt_arccos_of_le : ∀ {C : ℝ}, -1 ≤ C → C ≤ 37 / 50 → 11 / 15 < Real.arccos C)
    (h_AmbidextrousSofa_terminalCircleGap_pos : 0 < AmbidextrousSofa.terminalCircleGap)
    (h_AmbidextrousSofa_sin_cos_pos_of_mem_quarter : ∀ {t : ℝ}, t ∈ Set.Ioo 0 (Real.pi / 2) → 0 < Real.sin t ∧ 0 < Real.cos t)
    (h_AmbidextrousSofa_terminalCircleGap_gt_cubicPrice : AmbidextrousSofa.terminalCubicPrice < AmbidextrousSofa.terminalCircleGap)
    (h_AmbidextrousSofa_terminalCircleSineLower_pos : 0 < AmbidextrousSofa.terminalCircleSineLower)
    :
    terminalWeightedExcess v (Real.arcsin (C - T)) < terminalCircleGap * Real.cos α := by
  have hk0 := h_AmbidextrousSofa_terminalSlope_pos hα0 hαL
  obtain ⟨hs, hc⟩ := h_AmbidextrousSofa_sin_cos_pos_of_mem_quarter ⟨hα0, hαL⟩
  have hcs : terminalSlope α * Real.sin α = Real.cos α := div_mul_cancel₀ _ hs.ne'
  have hc1 := mul_le_mul_of_nonneg_right hk1 hs.le
  rw [hcs] at hc1
  have hsin := h_AmbidextrousSofa_terminalCircleSineLower_le_of_slope hc.le hs
    (Real.cos_sq_add_sin_sq α) hc1
  have hcSlope : terminalCircleSineLower * terminalSlope α ≤ Real.cos α := by
    linarith only [hcs, mul_le_mul_of_nonneg_left hsin hk0.le]
  have hq : (2 / 3 : ℝ) < Real.cos (Real.arcsin (C - T)) := by
    rw [Real.cos_arcsin, Real.lt_sqrt (by norm_num)]
    nlinarith only [hCT, hCT1]
  have hcut := h_AmbidextrousSofa_Analysis_eleven_fifteenths_lt_arccos_of_le (by linarith only [hCT]) hCT1
  rw [Real.arccos_eq_pi_div_two_sub_arcsin] at hcut
  have hℓ : max (Real.arcsin (C - T) -
      (Real.pi / 2 - properAngularDeadline (terminalSlope α))) 0 ≤ (2 / 3) * terminalSlope α := by
    apply max_le
    · dsimp [properAngularDeadline]; linarith only [hcut]
    · positivity
  refine (h_AmbidextrousSofa_terminalWeightedExcess_le_cubic (K := (4 / 5 : ℝ))
    (Real.arcsin_nonneg.mpr hCT) (Real.arcsin_lt_pi_div_two.mpr (by linarith only [hCT1]))
    (by dsimp [properAngularDeadline]; linarith only [hk1, Real.pi_gt_three])
    (by norm_num) hint hbound).trans_lt ?_
  have hpow := pow_le_pow_left₀ (le_max_right _ _) hℓ 3
  have hcube : terminalSlope α ^ 3 ≤ (9 / 64) * terminalSlope α := by
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hk0.le hk1 2) hk0.le]
  have hprod := mul_le_mul hcSlope hq.le (by positivity : (0 : ℝ) ≤ (2 / 3)) hc.le
  rw [div_lt_iff₀ (by positivity)]
  have hcert : (4 / 5 : ℝ) * (2 / 3) ^ 3 * (3 / 8) ^ 2 <
      terminalCircleGap * (6 * (2 / 3) * terminalCircleSineLower) := by
    have h := h_AmbidextrousSofa_terminalCircleGap_gt_cubicPrice
    unfold terminalCubicPrice at h
    exact (div_lt_iff₀ (by have hp := h_AmbidextrousSofa_terminalCircleSineLower_pos; positivity)).mp h
  have hpriced := mul_lt_mul_of_pos_right hcert hk0
  have hproduct := mul_le_mul_of_nonneg_left hprod h_AmbidextrousSofa_terminalCircleGap_pos.le
  nlinarith only [hpow, hcube, hproduct, hpriced]
end AmbidextrousSofa
