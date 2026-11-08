import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyActiveExponentialPruning
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The second moment of a finite Carleson counting function

Laminarity orders every intersecting pair. After integrating, each row
of the ordered-pair sum is exactly a descendant length sum. This proves
the second-moment bound required for the removed operator contribution.
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
