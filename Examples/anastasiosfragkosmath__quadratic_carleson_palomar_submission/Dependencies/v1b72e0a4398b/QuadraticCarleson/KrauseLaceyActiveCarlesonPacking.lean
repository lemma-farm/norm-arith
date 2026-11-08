import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyActiveBadIntervals
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Carleson length packing for the genuine active nonstandard family

Every interval above the grouped base scale is charged to a contained
selected bad cell, with exact length ratio `2^s`. No cell can be charged
twice. The grouped base scale is handled separately by disjointness.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
