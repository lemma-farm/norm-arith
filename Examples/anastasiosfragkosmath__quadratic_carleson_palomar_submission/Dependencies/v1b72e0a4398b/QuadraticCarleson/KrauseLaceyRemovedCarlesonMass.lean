import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyOverlapJohnNirenberg
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Exponential control of the actual removed interval mass

Local Carleson packing converts the exceptional-set measure to the sum
of lengths of all removed intervals. This is stronger than just a weak
bound for the overlap counting function and is the quantity used for the
discarded contribution in KL18.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyGenerationLayers
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
