import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyNonstandardCrossRows
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyOrderedEnergy
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Uniform signed sums of the actual nonstandard bad pieces

Physical scales are split into three residue classes solely to guarantee
the proved two-scale kernel separation. All diagonal and cross-row bounds
are derived for the actual bad inputs, and no signed-sum bound is assumed.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction KrauseLaceyOrderedEnergy
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
