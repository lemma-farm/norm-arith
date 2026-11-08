-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vb5f483631523.SlowEquilibration.RadialLaplaceBounds
set_option autoImplicit false
/-! Exact completion of the radial Gaussian square under the physical
energy tilt. Normalization bounds are obtained by integrating the actual
tilted density; no tilted probability or count limit is assumed. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory RadialGaussianBounds RadialLaplaceBounds
set_option maxHeartbeats 300000
def tiltedDensity (w : ℝ → ℝ) (N A B c₀ m σ k : ℝ) : ℝ :=
  w k*Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))
end SlowEquilibration.GaussianRadialEnergyTilt
