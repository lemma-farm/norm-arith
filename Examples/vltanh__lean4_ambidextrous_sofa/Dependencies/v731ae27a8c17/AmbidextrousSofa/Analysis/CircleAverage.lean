module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.ExactEstimates
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
theorem circleHeight_pos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 < circleHeight x :=
  Real.sqrt_pos.mpr (by nlinarith [hx.1, hx.2])
theorem circleHeight_sq {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    circleHeight x ^ 2 = 1 - x ^ 2 :=
  Real.sq_sqrt (by nlinarith [hx.1, hx.2])
theorem hasDerivAt_circleHeight {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt circleHeight (-circleSlope x) x := by
  refine (((hasDerivAt_pow 2 x).const_sub 1).sqrt (by nlinarith [hx.1, hx.2])).congr_deriv ?_
  simp [circleSlope, circleHeight]
  ring
theorem hasDerivAt_circleSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt circleSlope (1 / circleHeight x ^ 3) x := by
  have h0 := (circleHeight_pos hx).ne'
  refine ((hasDerivAt_id x).div (hasDerivAt_circleHeight hx) h0).congr_deriv ?_
  simp only [circleSlope, id]
  field_simp
  linear_combination circleHeight_sq hx
theorem circleAverage_eq_height_difference {q y : ℝ} (hq : 0 < q)
    (hy : y ∈ Ioo (q / 2) (1 - q / 2)) :
    circleAverage q y = (circleHeight (y - q / 2) - circleHeight (y + q / 2)) / q := by
  have hmem : ∀ t ∈ uIcc (y - q / 2) (y + q / 2), t ∈ Ioo (0 : ℝ) 1 := fun t ht => by
    rw [uIcc_of_le (by linarith)] at ht
    exact ⟨by linarith [ht.1, hy.1], by linarith [ht.2, hy.2]⟩
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := -circleHeight)
    (fun t ht => by simpa using (hasDerivAt_circleHeight (hmem t ht)).neg)
    (HasDerivAt.continuousOn fun t ht => hasDerivAt_circleSlope (hmem t ht)).intervalIntegrable
  rw [circleAverage, intervalIntegral.integral_comp_add_mul circleSlope hq.ne' y,
    show y + q * (-1 / 2) = y - q / 2 by ring, show y + q * (1 / 2) = y + q / 2 by ring, h,
    Pi.neg_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring
end AmbidextrousSofa
