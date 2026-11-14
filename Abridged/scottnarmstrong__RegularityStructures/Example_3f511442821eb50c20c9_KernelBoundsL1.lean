module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeac217a0f20.Phi43.Mollifier ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Mollifiers and regularised noise

A mollifier is a smooth compactly supported function `ρ` on `ℝ × ℝ³` with `∫ ρ = 1`. It is
rescaled parabolically, `ρ_ε(t, x) = ε⁻⁵ ρ(ε⁻² t, ε⁻¹ x)`, and periodised in space. A regularised
noise at scale `ε` is a version of `z ↦ W(ρ_ε^♯(z - ·))` that is smooth in `z` for every `ω`.

Source: the statement, Definitions 2.3 and 2.4.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
def rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ε ^ (-5 : ℤ) * ρ (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • z.2)
end RegularityStructures.Phi43
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vdeac217a0f20.RegularityStructures.Analysis.Parabolic.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Parabolic geometry on `ℝ⁴ = ℝ × ℝ³`

Space-time `ℝ⁴` is the product `ℝ × (Fin 3 → ℝ)`, a time coordinate and three space coordinates,
with the parabolic scaling `𝔰 = (2, 1, 1, 1)`. We measure distances with the parabolic size
`‖z‖_𝔰 = |z₀|^{1/2} + |z₁| + |z₂| + |z₃|` of [Hos25, §2.1] (`‖x‖_s = ∑ᵢ |xᵢ|^{1/sᵢ}`), which is
comparable to Hairer's `|z|_𝔰 = |z₀|^{1/2} + |z'|` [Hai14, §2], and satisfies the triangle
inequality and exact scaling `‖(c² t, c x)‖_𝔰 = c ‖(t, x)‖_𝔰`.

Sources: [Hos25] = arXiv:2310.07396v2, §2.1; [Hai14] = arXiv:1303.5113v4, §2.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- Space-time `ℝ⁴ = ℝ × ℝ³`, with time first. -/
abbrev ParabolicSpace : Type := ℝ × (Fin 3 → ℝ)
def parabolicDilate (c : ℝ) (z : ParabolicSpace) : ParabolicSpace := (c ^ 2 * z.1, c • z.2)
end RegularityStructures
end
public section
namespace RegularityStructures
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_3f511442821eb50c20c9_KernelBoundsL1 ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Parabolic scaling of the mollifier

The rescaled mollifier has scale-independent total variation on Euclidean space.  This is the
Euclidean half of the uniform `L¹` estimate for its spatial periodisation.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
namespace Phi43
set_option linter.unusedVariables false in
theorem integral_abs_rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) {ε : ℝ} (hε : 0 < ε) 
    (h_RegularityStructures_integral_comp_parabolicDilate : ∀ (φ : RegularityStructures.ParabolicSpace → ℝ) {d : ℝ},
      0 < d →
        ∫ (w : RegularityStructures.ParabolicSpace), φ (RegularityStructures.parabolicDilate d w) =
          (d ^ 5)⁻¹ * ∫ (w : RegularityStructures.ParabolicSpace), φ w)
    :
    ∫ z, |rescale ρ ε z| = ∫ z, |ρ z| := by
  have hscale : ∀ z : ℝ × (Fin 3 → ℝ),
      |rescale ρ ε z| = ε ^ (-5 : ℤ) *
        |ρ (RegularityStructures.parabolicDilate ε⁻¹ z)| := by
    intro z
    unfold rescale RegularityStructures.parabolicDilate
    rw [abs_mul, abs_of_pos (zpow_pos hε _)]
    congr 2
    · norm_num
  simp_rw [hscale]
  rw [integral_const_mul,
    h_RegularityStructures_integral_comp_parabolicDilate (fun z => |ρ z|) (inv_pos.mpr hε)]
  have hpow : ε ^ (-5 : ℤ) * (ε⁻¹ ^ 5)⁻¹ = 1 := by
    rw [inv_pow, inv_inv]
    rw [show ε ^ 5 = ε ^ (5 : ℤ) by norm_num]
    rw [← zpow_add₀ (ne_of_gt hε)]
    norm_num
  calc
    ε ^ (-5 : ℤ) * ((ε⁻¹ ^ 5)⁻¹ * ∫ (w : ParabolicSpace), |ρ w|) =
        (ε ^ (-5 : ℤ) * (ε⁻¹ ^ 5)⁻¹) * ∫ (w : ParabolicSpace), |ρ w| := by ring
    _ = ∫ (w : ParabolicSpace), |ρ w| := by rw [hpow, one_mul]
end Phi43
end RegularityStructures
end
