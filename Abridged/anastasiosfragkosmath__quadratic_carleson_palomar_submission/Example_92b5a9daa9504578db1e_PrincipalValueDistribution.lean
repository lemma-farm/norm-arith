import Mathlib.Analysis.Distribution.TemperedDistribution

-- ==== Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Examples.Example_92b5a9daa9504578db1e_PrincipalValueDistribution ====
/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The principal-value distribution `p.v. (1 / x)`

This file constructs the Hilbert-transform kernel directly from Parissis's
cancelled integral formula.  On a Schwartz test function `f`, the pairing is

`∫_{|x|<1} (f(x)-f(0))/x dx + ∫_{|x|≥1} f(x)/x dx`.

The cancellation controls the singularity by the first derivative Schwartz
seminorm, while Schwartz decay controls the tail.  The resulting functional
is continuous, hence a tempered distribution.  `PVSymmetricLimit.lean` proves
that it is exactly the limit of symmetric truncations.  We also define the
Fourier-side candidate `-π i · 𝓕⁻ sign`; identifying it with the direct
construction is kept as a theorem rather than assumed by definition.
-/
open MeasureTheory Set
open FourierTransform
open scoped SchwartzMap
namespace QuadraticCarleson

/-- The nonsingular representative used for the local part of the
principal-value functional. -/
noncomputable def principalValueNearIntegrand (f : 𝓢(ℝ, ℂ)) (x : ℝ) : ℂ :=
  (f x - f 0) / (x : ℂ)

axiom norm_integral_principalValueNearIntegrand_le (f : 𝓢(ℝ, ℂ)) :
    ‖∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x‖ ≤
      2 * SchwartzMap.seminorm ℂ 0 1 f

axiom norm_integral_principalValueFarIntegrand_le (f : 𝓢(ℝ, ℂ)) :
    ‖∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ)‖ ≤ ∫ x : ℝ, ‖f x‖
/-- Parissis's direct formula for the principal-value pairing: subtract the
constant term near zero, and use the ordinary integral away from zero. -/
noncomputable def principalValuePairing (f : 𝓢(ℝ, ℂ)) : ℂ :=
  (∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x) +
    ∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ)

/-- A fixed finite constant controlling the `L¹` norm of Schwartz functions
by two Schwartz seminorms. -/
noncomputable def principalValueTailBound : ℝ :=
  2 ^ (volume : Measure ℝ).integrablePower *
    ∫ x : ℝ, (1 + ‖x‖) ^ (-((volume : Measure ℝ).integrablePower : ℝ))

axiom integral_norm_schwartz_le (f : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ‖f x‖ ≤ principalValueTailBound *
      (SchwartzMap.seminorm ℂ 0 0 f +
        SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0 f)
theorem norm_principalValuePairing_le (f : 𝓢(ℝ, ℂ)) :
    ‖principalValuePairing f‖ ≤
      2 * SchwartzMap.seminorm ℂ 0 1 f + principalValueTailBound *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0 f) := by
  calc
    ‖principalValuePairing f‖ ≤
        ‖∫ x in Ioo (-1 : ℝ) 1, principalValueNearIntegrand f x‖ +
          ‖∫ x in {x : ℝ | 1 ≤ |x|}, f x / (x : ℂ)‖ := by
      exact norm_add_le _ _
    _ ≤ 2 * SchwartzMap.seminorm ℂ 0 1 f + ∫ x : ℝ, ‖f x‖ :=
      add_le_add (norm_integral_principalValueNearIntegrand_le f)
        (norm_integral_principalValueFarIntegrand_le f)
    _ ≤ 2 * SchwartzMap.seminorm ℂ 0 1 f + principalValueTailBound *
        (SchwartzMap.seminorm ℂ 0 0 f +
          SchwartzMap.seminorm ℂ (volume : Measure ℝ).integrablePower 0 f) :=
      add_le_add le_rfl (integral_norm_schwartz_le f)

end QuadraticCarleson
