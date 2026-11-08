/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.PsiGaussianVectorContinuous
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI3PsiTestedMoment
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeI2Psi2Field
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeWickSquare
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.ChaosLimitMomentsFieldIntegral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Hypotheses of the all-moments theorem for the tree fields

For a regularised noise `ξ` at scale `ε > 0` the field `Ψ = hairerPsiField N ξ` has continuous
paths, is measurable in `ω` for every `z`, is almost surely `W (K_ε (z - ·))` and has variance
`Q_ε(0)`. The kernel increment `K(y - w) - K(x - w)` is jointly measurable and vanishes unless
`|y₀ - w₀| ≤ 1` or `|x₀ - w₀| ≤ 1`; for `y` in the time slab `|y₀ - z₀| ≤ lam²` of a test function
centred at `z`, it is supported in a fixed compact set (`hairerI2Psi2Kernel_chaos_support`). These
are the inputs of `integral_pow_two_mul_le_of_chaosIntegral`.
-/
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}
/-- The kernel increment vanishes unless `|y₀ - w₀| ≤ 1` or `|x₀ - w₀| ≤ 1`. -/
theorem hairerI2Psi2Kernel_ne_zero_time (N : ℕ) {x y w : SpaceTime}
    (h : hairerI2Psi2Kernel N x y w ≠ 0) : |y.1 - w.1| ≤ 1 ∨ |x.1 - w.1| ≤ 1 := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  apply h
  unfold hairerI2Psi2Kernel
  rw [hairerKernelTorus_eq_zero_of_one_lt_time N (by simpa using hcon.1),
    hairerKernelTorus_eq_zero_of_one_lt_time N (by simpa using hcon.2), sub_zero]
/-- A compact time slab containing the support of the test function and the kernel increments
that meet it. -/
theorem hairerI2Psi2Kernel_chaos_support (N : ℕ) (x z : SpaceTime) (lam : ℝ) :
    ∃ S : Set SpaceTime, IsCompact S ∧ S.Nonempty ∧
      (∀ y, |y.1 - z.1| ≤ lam ^ 2 → y ∈ S) ∧
      ∀ y, |y.1 - z.1| ≤ lam ^ 2 → ∀ w, hairerI2Psi2Kernel N x y w ≠ 0 → w ∈ S := by
  set T : ℝ := |z.1| + lam ^ 2 + |x.1| + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  refine ⟨Set.Icc (-T) T ×ˢ Set.univ, isCompact_Icc.prod isCompact_univ,
    ⟨(0, 0), ⟨by linarith, by linarith⟩, Set.mem_univ _⟩, fun y hy => ?_, fun y hy w hw => ?_⟩
  · refine ⟨?_, Set.mem_univ _⟩
    have h1 := abs_le.1 hy
    have h3 := le_abs_self z.1
    have h4 := neg_abs_le z.1
    have h5 := abs_nonneg x.1
    constructor <;> nlinarith [sq_nonneg lam]
  · refine ⟨?_, Set.mem_univ _⟩
    have h1 := abs_le.1 hy
    have h3 := le_abs_self z.1
    have h4 := neg_abs_le z.1
    have h5 := abs_nonneg x.1
    have h6 := le_abs_self x.1
    have h7 := neg_abs_le x.1
    rcases hairerI2Psi2Kernel_ne_zero_time N hw with h | h
    · have h8 := abs_le.1 h
      constructor <;> nlinarith [sq_nonneg lam]
    · have h8 := abs_le.1 h
      constructor <;> nlinarith [sq_nonneg lam, sq_nonneg z.1, abs_nonneg z.1]
end RegularityStructures.Phi43
end
