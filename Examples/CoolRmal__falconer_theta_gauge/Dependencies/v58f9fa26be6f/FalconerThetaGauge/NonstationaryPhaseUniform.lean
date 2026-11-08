module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularizedReciprocal
public import Mathlib
set_option autoImplicit false
/-!
# Explicit nonstationary decay for smooth compact amplitudes

The smooth reciprocal is used only to make a globally defined transport
operator. Its derivative constants on the support follow from the actual
reciprocal identity, so its arbitrary cutoff region contributes no cost.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace FalconerThetaGauge
end FalconerThetaGauge
