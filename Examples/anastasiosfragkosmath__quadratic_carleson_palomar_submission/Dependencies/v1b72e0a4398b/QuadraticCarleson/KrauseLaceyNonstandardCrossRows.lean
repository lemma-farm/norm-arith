import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyNonstandardGenerations
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Summable cross rows for the actual nonstandard bad pieces

The small intervals in a cross row need not be disjoint: their actual
restricted bad-scale inputs have no multiplicity. This removes a potential
generation-count loss from the two-scale correlation estimate.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable def intervalBadMass
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) : ℝ :=
  ∫ x in I.centralThird, ‖badScaleInput S f I₀ k₀ (scale I + 2 - s) x‖
theorem intervalBadMass_nonneg
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (I : RealInterval) :
    0 ≤ intervalBadMass S f I₀ k₀ s scale I :=
  integral_nonneg fun _ ↦ norm_nonneg _
end KrauseLaceyBadScale
end QuadraticCarleson
