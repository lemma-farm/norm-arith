import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyStandardSourceSummation
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Regrouping the scalar-standard source gaps at a fixed physical scale

The finite identity below is the exact bookkeeping step used before the
fixed-scale endpoint: the source-gap sum is regrouped by its parent interval.
It does not use any cancellation or analytic estimate.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
