module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.SpaceSplittingSpatialKernelBounds
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.SpaceSplittingCircleRemainder
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.ScheduledSymbolEnergy
public import Mathlib
set_option autoImplicit false
/-! # The true averaged product of the circular stationary remainders is negligible -/
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace FalconerThetaGauge
theorem norm_circle_product_sub_stationary_product_le {Ix Iy Mx My : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hx : ‖Ix‖ ≤ 2 * Real.pi) (hy : ‖Iy‖ ≤ 2 * Real.pi)
    (hex : ‖Ix - Mx‖ ≤ δ) (hey : ‖Iy - My‖ ≤ δ) :
    ‖Ix * Iy - Mx * My‖ ≤ (4 * Real.pi + δ) * δ := by
  have hMx : ‖Mx‖ ≤ 2 * Real.pi + δ := by
    have h' := norm_add_le (Mx - Ix) Ix
    rw [sub_add_cancel, norm_sub_rev] at h'
    linarith
  have heq : Ix * Iy - Mx * My = (Ix - Mx) * Iy + Mx * (Iy - My) := by ring
  rw [heq]
  calc
    _ ≤ ‖Ix - Mx‖ * ‖Iy‖ + ‖Mx‖ * ‖Iy - My‖ := by
      simpa only [norm_mul] using norm_add_le ((Ix - Mx) * Iy) (Mx * (Iy - My))
    _ ≤ δ * (2 * Real.pi) + (2 * Real.pi + δ) * δ :=
      add_le_add (mul_le_mul hex hy (norm_nonneg _) hδ)
        (mul_le_mul hMx hey (norm_nonneg _) (by positivity))
    _ = _ := by ring
end FalconerThetaGauge
