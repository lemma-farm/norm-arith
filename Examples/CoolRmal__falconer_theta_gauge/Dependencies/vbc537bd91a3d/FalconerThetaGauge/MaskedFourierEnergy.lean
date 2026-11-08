module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.DirectionalTestsFilter
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.ScalarEnergyBinningFourier
public import Mathlib
set_option autoImplicit false
/-!
# The actual masked Fourier amplitude and circular spectrum

These are the literal angular-frequency quantities `U_X` and `σ_X` in
Definition 7.1, for an actual carrier and a jointly Borel bounded symbol.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal RealInnerProductSpace
namespace FalconerThetaGauge
end FalconerThetaGauge
