/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Kernel
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.DyadicPartition
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Parabolic.TestFunction
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Dyadic decomposition of the heat kernel on `ℝ⁴`

`heatShell n z = G(z) · dyadicBump (2^{n+3} N(z))` where `N = smoothParabolicNorm` and
`G = heatKernelR4`, and `heatRemainder z = G(z) · (1 - dyadicCutoff (2³ N(z)))`.  Then
`G = ∑_{n ≥ 0} heatShell n + heatRemainder` away from `0`, each `heatShell n` is smooth, supported in
`‖z‖_𝔰 ≤ 2^{-n}`, vanishes near `0`, and `heatShell n z = (2^n)^3 heatShell 0 (2^n z)`.

Source: Hairer, arXiv:1303.5113v4, Lemma 5.5.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The `n`-th dyadic piece of the heat kernel. -/
def heatShell (n : ℕ) (z : ParabolicSpace) : ℝ :=
  heatKernelR4 z * dyadicBump (2 ^ (n + 3) * smoothParabolicNorm z)
end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures
/-- A function smooth away from `0` times a smooth function vanishing near `0` is smooth. -/
theorem contDiff_mul_of_eventually_zero {f g : ParabolicSpace → ℝ}
    (hf : ∀ z, z ≠ 0 → ContDiffAt ℝ ∞ f z) (hg : ContDiff ℝ ∞ g) {ε : ℝ} (hε : 0 < ε)
    (h0 : ∀ z, smoothParabolicNorm z < ε → g z = 0) : ContDiff ℝ ∞ fun z => f z * g z := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    have hopen : IsOpen {w : ParabolicSpace | smoothParabolicNorm w < ε} :=
      isOpen_lt continuous_smoothParabolicNorm continuous_const
    have hmem : (0 : ParabolicSpace) ∈ {w : ParabolicSpace | smoothParabolicNorm w < ε} := by
      simpa [smoothParabolicNorm_eq_zero_iff.2 rfl] using hε
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hmem] with w hw
    simp [h0 w hw]
  · exact (hf z hz).mul hg.contDiffAt
theorem contDiff_heatShell (n : ℕ) : ContDiff ℝ ∞ (heatShell n) := by
  have hpos : (0 : ℝ) < 2 ^ (n + 3) := pow_pos (by norm_num) _
  refine contDiff_mul_of_eventually_zero (fun z hz => contDiffAt_heatKernelR4 hz)
    (contDiff_dyadicBump_smoothParabolicNorm (n + 3)) (ε := 1 / (2 * 2 ^ (n + 3)))
    (by positivity) ?_
  intro z hz
  refine dyadicBump_eq_zero_of_le ?_
  rw [lt_div_iff₀ (by positivity)] at hz
  linarith
theorem heatShell_eq_zero {n : ℕ} {z : ParabolicSpace} (h : (2 : ℝ)⁻¹ ^ n < parabolicNorm z) :
    heatShell n z = 0 := by
  have h4 := parabolicNorm_le_four_mul_smoothParabolicNorm z
  have hpos : (0 : ℝ) < 2 ^ (n + 3) := pow_pos (by norm_num) _
  have e : (2 : ℝ)⁻¹ ^ n = 4 * ((1 / 2) ^ 2 / 2 ^ n) := by
    rw [inv_pow]; field_simp; norm_num
  have h2 : 2 ≤ (2 : ℝ) ^ (n + 3) * smoothParabolicNorm z := by
    have hN : (1 / 2) ^ 2 / (2 : ℝ) ^ n < smoothParabolicNorm z := by linarith
    rw [div_lt_iff₀ (pow_pos (by norm_num) n)] at hN
    rw [pow_add]
    nlinarith
  simp [heatShell, dyadicBump_eq_zero_of_ge h2]
end RegularityStructures
end
