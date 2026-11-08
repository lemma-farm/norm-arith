import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyScaleMaximal
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Actual finite stopping extraction for the Krause--Lacey recursion

This is the finite version of the extraction following KL18 Lemma 3.5:
select the maximal intervals where either input average exceeds ten times
the parent average. The selected children, their packing, and the bounded
averages on the remaining collection are conclusions, not supplied stopping
or sparse hypotheses. The only structural input is laminarity of the finite
interval collection, as holds in each source dyadic grid.
-/
open Function MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace KrauseLaceyStoppingExtraction
set_option autoImplicit false
end KrauseLaceyStoppingExtraction
end QuadraticCarleson
