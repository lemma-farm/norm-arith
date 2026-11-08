/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Constructions.Pi
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
