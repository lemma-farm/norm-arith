/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Decomposition
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Causal.Bump
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Scaled
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Causal polynomial-annihilating modification of the heat shells

The construction of `Analysis/Heat/Annihilating` with the correcting bump `ψ = annBumpC N`
supported in `{t > 0}` (`exists_moment_bump_causal`), so that every shell
`annShellC N n` and the remainder `annRemainderC N` are non-anticipative.  Contains the
decomposition `G = ∑ₙ annShellC N n + annRemainderC N` away from `0`
(`heatKernelR4_eq_tsum_annShellC`) and Assumption 5.1 with `β = 2`
(`isRegularisingDecomposition_annShellC`).

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5 and Section 7.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
theorem exists_annBumpC (N : ℕ) :
    ∃ ψ : ParabolicSpace → ℝ, ContDiff ℝ ∞ ψ ∧ (∀ z, 1 < parabolicNorm z → ψ z = 0) ∧
      (∀ z, z.1 ≤ 0 → ψ z = 0) ∧
      ∀ k : PolyIndex N, ∫ z, evalParabolic (MvPolynomial.monomial k.1 1) z * ψ z = annMoment k :=
  exists_moment_bump_causal N annMoment
/-- The causal correcting bump `ψ`. -/
def annBumpC (N : ℕ) : ParabolicSpace → ℝ := Classical.choose (exists_annBumpC N)
/-- The base kernel `K₀ = heatShell 0 - ψ + 2³ ψ(S² ·)` with the causal bump. -/
def annKernel0C (N : ℕ) (z : ParabolicSpace) : ℝ :=
  heatShell 0 z - annBumpC N z + 2 ^ 3 * annBumpC N (parabolicDilate 2 z)
/-- The `n`-th causal polynomial-annihilating shell `(2^n)^3 K₀(S^{2^n} z)`. -/
def annShellC (N n : ℕ) (z : ParabolicSpace) : ℝ := scaledShell (annKernel0C N) n z
end RegularityStructures
end
public section
open scoped ContDiff
namespace RegularityStructures
theorem contDiff_annBumpC (N : ℕ) : ContDiff ℝ ∞ (annBumpC N) :=
  (Classical.choose_spec (exists_annBumpC N)).1
theorem annBumpC_eq_zero {N : ℕ} {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annBumpC N z = 0 :=
  (Classical.choose_spec (exists_annBumpC N)).2.1 z hz
theorem contDiff_annKernel0C (N : ℕ) : ContDiff ℝ ∞ (annKernel0C N) := by
  unfold annKernel0C
  exact ((contDiff_heatShell 0).sub (contDiff_annBumpC N)).add
    (contDiff_const.mul ((contDiff_annBumpC N).comp (parabolicDilateCLM 2).contDiff))
theorem annKernel0C_eq_zero (N : ℕ) {z : ParabolicSpace} (hz : 1 < parabolicNorm z) :
    annKernel0C N z = 0 := by
  have h1 : heatShell 0 z = 0 := heatShell_eq_zero (by simpa using hz)
  have h2 : 1 < parabolicNorm (parabolicDilate 2 z) := by
    rw [parabolicNorm_parabolicDilate (by norm_num)]
    linarith [parabolicNorm_nonneg z]
  simp [annKernel0C, h1, annBumpC_eq_zero hz, annBumpC_eq_zero h2]
theorem contDiff_annShellC (N n : ℕ) : ContDiff ℝ ∞ (annShellC N n) :=
  contDiff_scaledShell (contDiff_annKernel0C N) n
theorem annShellC_eq_zero {N n : ℕ} {z : ParabolicSpace} (hz : (2 : ℝ)⁻¹ ^ n < parabolicNorm z) :
    annShellC N n z = 0 :=
  scaledShell_eq_zero (fun _ hz => annKernel0C_eq_zero N hz) hz
end RegularityStructures
end
