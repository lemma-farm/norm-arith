import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyStoppingExtraction
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The actual finite minimal-generation decomposition

These are the successive inclusion-minimal layers used in KL18. Their
disjointness and finite exhaustion are proved from laminarity and finiteness.
No relative scale gap is inferred merely from a gap between layer labels.
-/
open Function Set
namespace QuadraticCarleson
namespace KrauseLaceyGenerationLayers
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
end KrauseLaceyGenerationLayers
end QuadraticCarleson
