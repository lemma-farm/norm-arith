import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyNonstandardGenerations
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Summable cross rows for the actual nonstandard bad pieces

The small intervals in a cross row need not be disjoint: their actual
restricted bad-scale inputs have no multiplicity. This removes a potential
generation-count loss from the two-scale correlation estimate.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
