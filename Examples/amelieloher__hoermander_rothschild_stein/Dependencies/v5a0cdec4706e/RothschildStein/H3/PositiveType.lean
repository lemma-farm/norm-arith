-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H3.HomogeneousBounds
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.H3.HomogeneousOperators
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v5a0cdec4706e.RothschildStein.G2.LocalPower
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H3
open G2
variable {N : ℕ} {G : HomogeneousGroup N}
/-- A positive-type kernel has precisely the punctured smoothness
and degree α−Q of BB Definition 8.13, p. 346. -/
structure PositiveType (G : HomogeneousGroup N) (α : ℝ)
    (T : (Fin N → ℝ) → ℝ) : Prop where
  positive : 0 < α
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ
  homogeneous : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
    T (G.dilate t x) = t ^ (α - (G.homogeneousDimension : ℝ)) * T x
end RothschildStein.H3
