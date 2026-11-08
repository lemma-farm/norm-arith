import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryOscillatoryScaling
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OscillatoryReductionLimit
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The lacunary principal-value operator and its ordinary Hilbert remainder

The pointwise reduction is unconditional on all of `L0Infinity`. The
Hardy--Littlewood term is estimated by its proved weak `(1,1)` bound. The
remaining ordinary Hilbert maximal level set is kept literally in the
endpoint estimate, rather than being replaced by an unproved weak bound.
-/
open Filter MeasureTheory Set
open scoped ENNReal Topology
namespace QuadraticCarleson
namespace LacunaryPositiveOperatorReduction
open OscillatoryReduction PositiveGoodOscillatory PositiveFullOscillatoryEndpoint
open PositiveEndpointOptimization PositiveLevelIntegration
open LacunaryOscillatoryScaling
set_option autoImplicit false
end LacunaryPositiveOperatorReduction
end QuadraticCarleson
