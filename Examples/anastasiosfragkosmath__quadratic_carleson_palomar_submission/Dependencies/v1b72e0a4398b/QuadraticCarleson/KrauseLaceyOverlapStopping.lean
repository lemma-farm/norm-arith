import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyPhysicalTailPrefix
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite overlap stopping geometry

The maximal intervals removed by literal overlap pruning cover exactly
the high-overlap set. Inside each such interval at most `M` covering
intervals are strict ancestors. These statements are deterministic and
use only the actual finite laminar family.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
