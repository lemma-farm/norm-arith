module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7717f334022e.FalconerThetaGauge.RadialProjectionUniformIntegrability
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Regular
set_option autoImplicit false
/-!
# Absolute continuity of a weak radial measure limit

This file proves the measure-theoretic passage to a weak limit. A uniform
logarithmic Orlicz bound yields a quantitative bound on open sets by
Portmanteau. Outer regularity of the reference measure extends that bound
to arbitrary sets, and its vanishing tail proves absolute continuity.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace FalconerThetaGauge
end FalconerThetaGauge
