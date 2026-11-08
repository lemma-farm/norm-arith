module
public import Examples.scottnarmstrong__CoarseDeGiorgi.Dependencies.v3955459bdd7a.CoarseDeGiorgi.Statements.GaussianKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Elementary estimates for the Gaussian kernel

All distances here use `vecNormSq`, the Euclidean squared length on `Vec d`.
-/
@[expose] public section
open Homogenization MeasureTheory
open scoped BigOperators
namespace CoarseDeGiorgi.NegSobolev
theorem gaussianKernel_le_double_time {d : ℕ} (t : ℝ) (ht : 0 < t)
    (u v : Vec d) (h : vecNormSq v ≤ 2 * vecNormSq u + 2 * (d : ℝ) * t) :
    gaussianKernel t ht u ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp ((d : ℝ) / 4) *
        gaussianKernel (2 * t) (by positivity) v := by
  have hbase : 0 < 4 * Real.pi * t := by positivity
  have hpref : (4 * Real.pi * t) ^ (-((d : ℝ) / 2)) =
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2)) := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hbase.le]
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp only [add_neg_cancel, Real.rpow_zero, one_mul]
  have hexp : -(vecNormSq u) / (4 * t) ≤
      (d : ℝ) / 4 + -(vecNormSq v) / (4 * (2 * t)) := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * t)).mpr
    field_simp
    nlinarith only [h]
  unfold gaussianKernel
  rw [hpref]
  calc
    _ ≤ ((2 : ℝ) ^ ((d : ℝ) / 2) * (4 * Real.pi * (2 * t)) ^ (-((d : ℝ) / 2))) *
        Real.exp ((d : ℝ) / 4 + -(vecNormSq v) / (4 * (2 * t))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring
end CoarseDeGiorgi.NegSobolev
