module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.SmoothProbabilityApproximation
public import Mathlib
set_option autoImplicit false
/-!
# Small smooth sources retain the prepared separation

Convolution enlarges a centered source ball by exactly the outer radius of
the bump. Both the measure carrier and the pointwise nonzero smooth density
obey this bound. A fixed small shrinking sequence therefore permits the
closed-carrier joint convergence argument and the bounded-ray estimate.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal Topology Convolution
namespace FalconerThetaGauge
end FalconerThetaGauge
