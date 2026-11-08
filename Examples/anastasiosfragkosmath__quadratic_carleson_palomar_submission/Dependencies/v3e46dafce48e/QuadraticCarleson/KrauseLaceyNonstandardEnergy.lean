import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyBadScaleInputs
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual nonstandard intervals and their diagonal energy

The nonstandard test is the source's adjoint-composition test, rather than
the desired `L²` estimate. Its right side is the actual unit-window
convolution of the restricted bad input. The diagonal estimate below is
derived from this test and the proved stopping-cell local-mass bound.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate Classical
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
end KrauseLaceyBadScale
end QuadraticCarleson
