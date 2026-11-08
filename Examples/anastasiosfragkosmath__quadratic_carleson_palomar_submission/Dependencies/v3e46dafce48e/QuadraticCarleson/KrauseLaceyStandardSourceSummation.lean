import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyEnergyClassification
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyNonstandardCrossRows
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v3e46dafce48e.QuadraticCarleson.KrauseLaceyScaleMaximal
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Fixed-physical-scale source summation for the scalar-standard branch

This follows the organization of the standard part of the Krause--Lacey
local lemma: fix a physical scale `j`, retain the source gaps in a finite
set, and only afterwards apply finite Cauchy--Schwarz in that gap variable.
The crucial preliminary statement is that the diagonal energy over *all*
source gaps still has no multiplicity: distinct bad-scale inputs have
disjoint spatial supports.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyBadScale
open KrauseLaceyStoppingExtraction
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
end KrauseLaceyBadScale
end QuadraticCarleson
