import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.CanonicalScaleAtoms
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.OscillatoryReductionL1
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Exact integration and oscillatory recombination of canonical scale slices

Disjoint spatial scales give equality of the total absolute integral, not
just a bound. The resulting genuine Bochner interchange is specialized to
each dyadic height, each finite low-height kernel, and the all-height action.
-/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
namespace CanonicalScaleAtoms
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveLowFullEstimate OscillatoryReduction LowKernelLevelSummation
end CanonicalScaleAtoms
end QuadraticCarleson
