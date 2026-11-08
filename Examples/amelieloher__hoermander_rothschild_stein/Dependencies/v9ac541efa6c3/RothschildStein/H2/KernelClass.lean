-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v9ac541efa6c3.RothschildStein.H2.VolumeComparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
/-- The radial weight d(x,y)^ν / V(x;y) from BB (7.6), p. 299.
The total extension is used only off the diagonal in the kernel bounds. -/
def kernelWeight (μ : Measure X) (ν : ℝ) (x y : X) : ℝ :=
  dist x y ^ ν / (volumeAt μ x y).toReal
/-- The two estimates of BB Definition 7.10, p. 299. Smoothness is in the
first variable only. Measurability is on E × E, with no restriction outside E. -/
structure KernelClass (μ : Measure X) (E : Set X) (β ν A S : ℝ)
    (K : X → X → ℝ) : Prop where
  measurable_E : MeasurableSet E
  measurable : Measurable (fun p : E × E => K p.1 p.2)
  β_pos : 0 < β
  β_le_one : β ≤ 1
  ν_nonneg : 0 ≤ ν
  A_nonneg : 0 ≤ A
  S_nonneg : 0 ≤ S
  size : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → |K x y| ≤ A * kernelWeight μ ν x y
  smooth : ∀ x₀ ∈ E, ∀ x ∈ E, ∀ y ∈ E, 2 * dist x₀ x < dist x₀ y →
    |K x₀ y - K x y| ≤ S * kernelWeight μ ν x₀ y * (dist x₀ x / dist x₀ y) ^ β
/-- Radial kernel weights are nonnegative. -/
theorem kernelWeight_nonneg (μ : Measure X) (ν : ℝ) (x y : X) :
    0 ≤ kernelWeight μ ν x y :=
  div_nonneg (Real.rpow_nonneg dist_nonneg _) ENNReal.toReal_nonneg
end RothschildStein.H2
