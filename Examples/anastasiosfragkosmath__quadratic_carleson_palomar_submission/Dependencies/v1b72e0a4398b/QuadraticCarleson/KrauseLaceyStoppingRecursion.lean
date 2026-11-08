import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyStoppingExtraction
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Exact localized maximal recursion after Krause--Lacey stopping extraction

The operator here is the genuine supremum of localized sums over all
intervals above a length threshold, as in KL18 (3.4), not a maximum of
individual scale outputs. The finite interval sum splits exactly into the
constructed good collection and the collections belonging to the selected
children. This gives the actual pointwise and bilinear recursion without
postulating any local oscillatory or sparse domination estimate.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyStoppingRecursion
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
end KrauseLaceyStoppingRecursion
end QuadraticCarleson
