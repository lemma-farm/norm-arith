import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.KrauseLaceyActiveOverlapPruning
import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The source-size active overlap cutoff and its prefix estimate

The concrete cutoff `(s+1)(1+2^s)` has size `O((s+1)2^s)` and logarithm
at most `2s+1`. The pruned actual prefix estimate is unconditional. The
exceptional-set result retained from the previous module is first-moment
decay, not the stronger exponential tail needed to finish the source proof.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
set_option autoImplicit false
end KrauseLaceyBadScale
end QuadraticCarleson
