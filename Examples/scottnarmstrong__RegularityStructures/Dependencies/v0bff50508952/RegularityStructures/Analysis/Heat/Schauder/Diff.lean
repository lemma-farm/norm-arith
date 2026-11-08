/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v0bff50508952.RegularityStructures.Analysis.Heat.Schauder.Shell
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# `L¹` size of the increments of a heat shell and of its generator

For the increment `h(w) = heatShell n w - heatShell n (w - e)` with `‖e‖_𝔰 ≤ 2^{-n}` we show
`∫ |h| ≲ 2^{-n} ‖e‖_𝔰` and `∫ |L h| ≲ 2^{3n} ‖e‖_𝔰` (`exists_heatShell_diff_bounds`), by exact
scaling from `n = 0` and `exists_integral_abs_sub_le`.
-/
public section
open MeasureTheory
open scoped ContDiff
namespace RegularityStructures
theorem contDiff_iteratedFDeriv_apply {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ)
    (v : ParabolicSpace) : ContDiff ℝ ∞ fun w => iteratedFDeriv ℝ k f w (fun _ => v) := by
  have h : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) := hf.iteratedFDeriv_right (by simp)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => ParabolicSpace) ℝ
    (fun _ => v)).contDiff.comp h
theorem contDiff_parabolicGenerator {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (parabolicGenerator f) := by
  unfold parabolicGenerator
  refine (contDiff_const.mul (contDiff_iteratedFDeriv_apply hf 2 timeDir)).sub
    (contDiff_const.mul ?_)
  exact ContDiff.sum fun i _ => contDiff_iteratedFDeriv_apply hf 4 (spaceDir i)
end RegularityStructures
end
