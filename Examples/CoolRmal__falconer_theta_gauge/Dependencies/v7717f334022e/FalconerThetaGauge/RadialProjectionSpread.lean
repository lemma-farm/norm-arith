module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionSpreadRestriction
public import Mathlib
set_option autoImplicit false
/-!
# Uniform radial Orlicz spread on compact retained carriers

This is the radial spread part of the gauge preparation. Starting with only
positive gauge Hausdorff measure, Borel bounded good-pin sets yield actual
compact quarter-mass carriers. Normalizing both restrictions preserves the
geometry and gauge and gives a common finite eighth-order radial bound at
every retained carrier point in both directions.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
