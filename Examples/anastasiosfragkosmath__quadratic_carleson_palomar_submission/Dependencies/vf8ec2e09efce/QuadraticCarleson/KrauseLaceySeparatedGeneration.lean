import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyCrossScalePairing
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Separated-generation pairings of the actual localized pieces

The geometric input here consists of disjoint small intervals inside one
large interval, their actual local mass bounds, and the source scale gap.
These hypotheses are exactly the facts used after KL18 (4.20); no cross
pairing or signed-sum estimate is an input to the theorem.
-/
open Function MeasureTheory Set
open scoped ComplexConjugate
namespace QuadraticCarleson
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end QuadraticCarleson
