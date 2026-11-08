-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.G2.GaugeConsequences
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.G2.Measure
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v87c6fa8868bd.RothschildStein.G2.AnalyticStructure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)
/-- The fixed-gauge mean is taken over the closed unit-to-e shell
(BB Prop 6.26, p. 274). -/
def kernelMean (ν f : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ x in {x | 1 ≤ ν x ∧ ν x ≤ Real.exp 1}, f x
/-- The function version of the type-zero class in Chapter 8:
smoothness off the origin, degree minus Q, and zero fixed-gauge mean
(BB Def. 8.21 and Remark 8.23, p. 354). -/
structure TypeZero (ν f : (Fin N → ℝ) → ℝ) : Prop where
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) f {0}ᶜ
  homogeneous : ∀ (t : ℝ), 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
    f (G.dilate t x) = t ^ (-(G.homogeneousDimension : ℝ)) * f x
  mean_zero : kernelMean ν f = 0
end RothschildStein.H3
