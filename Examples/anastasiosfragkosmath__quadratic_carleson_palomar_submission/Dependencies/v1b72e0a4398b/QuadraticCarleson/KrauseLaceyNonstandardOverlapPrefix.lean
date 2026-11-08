import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyNonstandardSubcollectionPrefix
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyGenerationOverlap
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual overlap bounds replace cardinality in the nonstandard prefix estimate

The geometric hypothesis below is the literal a.e. interval overlap count.
The transition from that count to a complete maximal-prefix bound is proved,
including exact truncation of all higher generations. This is a composable
consequence, not an assertion that the source's analytic pruning is finished.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyGenerationLayers
set_option autoImplicit false
end KrauseLaceyBadScale
end QuadraticCarleson
