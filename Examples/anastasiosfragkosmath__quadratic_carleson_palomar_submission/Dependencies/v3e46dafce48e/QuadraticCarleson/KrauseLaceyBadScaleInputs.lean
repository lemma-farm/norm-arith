import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyStoppingExtraction
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceySeparatedGeneration
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual bad-scale inputs in the local Krause--Lacey argument

The bad intervals are the actual maximal threshold-ten children for `f`
(the second stopping input is zero). The grouping uses the source's exact
condition `max (2^k₀) |J| = 2^ℓ`, including every smaller child at the base
scale. No cancellation is subtracted from these bad inputs.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
open scoped Classical
end KrauseLaceyBadScale
end QuadraticCarleson
