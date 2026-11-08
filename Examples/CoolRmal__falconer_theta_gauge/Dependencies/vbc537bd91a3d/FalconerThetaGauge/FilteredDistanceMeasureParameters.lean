module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.FilteredDistanceMeasureTests
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.ParameterBudgets
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.FilterSummability
public import Mathlib
set_option autoImplicit false
/-!
# The exact scale-dependent filter loss and its summability

The logarithmic cutoff budget follows from the actual parameter facts of
Lemma 2.2. The full error `a_N` retains the rounded block and tolerance
parameters and all constants in Lemma 6.13.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped ENNReal
namespace FalconerThetaGauge
end FalconerThetaGauge
