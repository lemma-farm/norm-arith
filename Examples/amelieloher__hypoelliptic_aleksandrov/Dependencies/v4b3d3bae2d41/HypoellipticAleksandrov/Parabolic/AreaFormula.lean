module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Measure.TimeVelocity
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.HypoellipticAleksandrov.Parabolic.Jacobian
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v4b3d3bae2d41.PDEFoundation.Measure.BallVolume
public import Mathlib.MeasureTheory.Function.Jacobian
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# One-sided area formula for the parabolic normal map

This module records the exact product-volume normalization of the
slope--intercept wedge and specializes the one-sided area formula to the
parabolic normal map.  The `TimeVelocity` volume is the product
Lebesgue measure; no competing Haar instance is introduced.  The area bound
does not assume injectivity.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory Set
open scoped ENNReal
end HypoellipticAleksandrov.Parabolic
