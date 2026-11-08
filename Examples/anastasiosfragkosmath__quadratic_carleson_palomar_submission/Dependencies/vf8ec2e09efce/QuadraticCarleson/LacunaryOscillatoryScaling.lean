import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryOscillatoryAssembly
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositiveFullOscillatoryScaling
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Genuine lacunary homogeneity and arbitrary endpoint thresholds

The normalized estimate is applied to the actual input `(3 / α) f`.
Its individual frozen-block hypothesis is stated for that input, not
transported through the nonlinear stopping decomposition. A uniform
individual-block formulation is also supplied for the eventual KL theorem.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
namespace LacunaryOscillatoryScaling
open OscillatoryReduction PositiveGoodOscillatory PositiveFullOscillatoryEndpoint
open PositiveEndpointOptimization PositiveHighHeightEstimate
open LacunaryMiddleKalton LacunaryOscillatoryAssembly
set_option autoImplicit false
end LacunaryOscillatoryScaling
end QuadraticCarleson
