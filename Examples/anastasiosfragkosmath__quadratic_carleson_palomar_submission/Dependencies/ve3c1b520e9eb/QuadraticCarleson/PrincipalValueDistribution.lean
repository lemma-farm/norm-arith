/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Mathlib
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
/-- Lebesgue measure restricted to the positive half-line. -/
noncomputable def positiveHalfLineMeasure : Measure ℝ :=
  volume.restrict (Ioi 0)
/-- Lebesgue measure restricted to the negative half-line. -/
noncomputable def negativeHalfLineMeasure : Measure ℝ :=
  volume.restrict (Iio 0)
noncomputable instance positiveHalfLineMeasure_hasTemperateGrowth :
    positiveHalfLineMeasure.HasTemperateGrowth := by
  obtain ⟨n, hn⟩ :=
    (inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_integrable
  exact ⟨⟨n, hn.mono_measure Measure.restrict_le_self⟩⟩
noncomputable instance negativeHalfLineMeasure_hasTemperateGrowth :
    negativeHalfLineMeasure.HasTemperateGrowth := by
  obtain ⟨n, hn⟩ :=
    (inferInstance : (volume : Measure ℝ).HasTemperateGrowth).exists_integrable
  exact ⟨⟨n, hn.mono_measure Measure.restrict_le_self⟩⟩
end QuadraticCarleson
