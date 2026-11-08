import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyPositiveCorrelation
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Separated-scale quadratic correlation

This proves the degree-two kernel estimate in Krause--Lacey (2.6).
The phase becomes linear. With small radius at least one, the existing
first-derivative integration-by-parts estimate already gives the required
large-radius squared decay; no unproved second-derivative bound is needed.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate Interval
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
