/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.WhiteNoise
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
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
open scoped ContDiff in
/-- The class `𝓜` of mollifiers: smooth, compactly supported, with integral one. -/
structure IsMollifier (ρ : ℝ × (Fin 3 → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ρ
  hasCompactSupport : HasCompactSupport ρ
  integral_eq_one : ∫ z, ρ z = 1
/-- The parabolic rescaling `ρ_ε(t, x) = ε⁻⁵ ρ(ε⁻² t, ε⁻¹ x)`. -/
def rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ε ^ (-5 : ℤ) * ρ (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • z.2)
def periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))
/-- The test function `ρ_{ε,z}(w) = ρ_ε^♯(z - w)`. -/
def mollifierAt (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) (w : SpaceTime) : ℝ :=
  periodise ρ ε (z - w)
/-- `ξ` is a regularised noise at scale `ε`: smooth in space-time for every `ω`, and for every `z`
measurable and almost surely equal to `W(ρ_{ε,z})`. -/
def IsRegularisedNoise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W : (SpaceTime → ℝ) → Ω → ℝ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (ξ : Ω → SpaceTime → ℝ) : Prop :=
  (∀ ω, IsSmoothOnSpaceTime (ξ ω)) ∧
    ∀ z, Measurable (fun ω => ξ ω z) ∧ (fun ω => ξ ω z) =ᵐ[P] W (mollifierAt ρ ε z)
end RegularityStructures.Phi43
end
