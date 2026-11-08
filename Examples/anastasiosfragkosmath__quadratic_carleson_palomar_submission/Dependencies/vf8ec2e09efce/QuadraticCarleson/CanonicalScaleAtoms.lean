import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveStoppingBadRecombination
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Canonical stopping atoms sliced by their exact dyadic lengths

The scale class is exactly `2^j ≤ length < 2^(j+1)`. The construction is
generic in the magnitude amplitudes and therefore covers both the full and
lacunary partitions. No interval family is supplied as an assumption.
-/
open MeasureTheory Set
open scoped ENNReal NNReal Function
namespace QuadraticCarleson
namespace CanonicalScaleAtoms
open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms CalderonZygmundLevelRecombination
open PositiveEndpointOptimization PositiveLevelIntegration PositiveHighHeightEstimate
open PositiveStoppingBadEstimate
end CanonicalScaleAtoms
end QuadraticCarleson
