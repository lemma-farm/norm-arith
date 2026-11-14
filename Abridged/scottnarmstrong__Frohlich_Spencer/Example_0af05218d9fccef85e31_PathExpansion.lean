module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

-- ==== Examples.scottnarmstrong__Frohlich_Spencer.Examples.Example_0af05218d9fccef85e31_PathExpansion ====
/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Diagonal-dominance decay of finite-volume resolvents

If `|v x - z| ≥ N > K` on a finite volume `Λ`, where `K` bounds the row sums of the kernel `a`,
then `restrictedOp a v Λ - z • 1` is invertible and the resolvent column decays like
`(K / N) ^ ⌈d x y⌉₊ / (N - K)`, for every complex `z`.

The proof is by maximum propagation, with no
Neumann series.

Motivation: the base-scale mechanism of Fröhlich–Spencer (1983), Appendix A,
Fröhlich–Spencer (1983).
-/
@[expose] public section
open Matrix
namespace FroehlichSpencer.Infra
variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}
omit [DecidableEq X] in
private theorem norm_sum_mul_le (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K) (Λ : Finset X)
    (x : X) (g : X → ℂ) {B : ℝ} (hB : 0 ≤ B) (hg : ∀ w ∈ Λ, a x w ≠ 0 → ‖g w‖ ≤ B) :
    ‖∑ w ∈ Λ, a x w * g w‖ ≤ K * B := by
  calc ‖∑ w ∈ Λ, a x w * g w‖ ≤ ∑ w ∈ Λ, ‖a x w * g w‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ Λ, ‖a x w‖ * B := by
        refine Finset.sum_le_sum fun w hw => ?_
        rw [norm_mul]
        by_cases h : a x w = 0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left (hg w hw h) (norm_nonneg _)
    _ = (∑ w ∈ Λ, ‖a x w‖) * B := by rw [Finset.sum_mul]
    _ ≤ K * B := mul_le_mul_of_nonneg_right (hK x Λ) hB

end FroehlichSpencer.Infra
