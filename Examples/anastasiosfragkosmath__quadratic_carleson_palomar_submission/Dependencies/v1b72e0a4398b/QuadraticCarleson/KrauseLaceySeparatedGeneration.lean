import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyCrossScalePairing
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Separated-generation pairings of the actual localized pieces

The geometric input here consists of disjoint small intervals inside one
large interval, their actual local mass bounds, and the source scale gap.
These hypotheses are exactly the facts used after KL18 (4.20); no cross
pairing or signed-sum estimate is an input to the theorem.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
noncomputable def krauseLaceyCollectionAction
    (S : Finset RealInterval) (scale : RealInterval → ℤ)
    (b : RealInterval → ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑ I ∈ S, krauseLaceyLocalizedPiece 1 (scale I) I (b I) x
end QuadraticCarleson
