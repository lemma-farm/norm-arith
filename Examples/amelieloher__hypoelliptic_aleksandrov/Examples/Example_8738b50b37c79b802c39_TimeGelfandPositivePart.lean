module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeGelfandPositivePartSteklov
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimePositivePartPairingConvergence
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimePositivePartContinuity
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeHilbertTraces
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive-part reverse-time energy increments

This module constructs the scalar no-defect energy representative attached to
a reverse-time Gelfand weak derivative.  It deliberately does not construct a
Hilbert-valued trace or assert a PDE solvability result.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Filter Function MeasureTheory Set Topology
open scoped ENNReal RealInnerProductSpace
private theorem abs_sq_sub_le_of_bounds
    {a b N delta y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hdelta : 0 ≤ delta) (hy : 0 ≤ y)
    (hdiff : |a - b| ≤ N * delta)
    (hsum : a + b ≤ N * delta + 2 * N * y) :
    |a ^ 2 - b ^ 2| ≤ N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by
  rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg ha hb)]
  calc
    (a + b) * |a - b| ≤ (N * delta + 2 * N * y) * (N * delta) := by
      exact mul_le_mul hsum hdiff (abs_nonneg _) (by positivity)
    _ = N ^ 2 * delta ^ 2 + 2 * N ^ 2 * y * delta := by ring
private theorem abs_sqNorm_valueCLM_sub_le
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω)
    (x y : H10HilbertGraph hΩ) :
    |‖valueCLM hΩ x‖ ^ 2 - ‖valueCLM hΩ y‖ ^ 2| ≤
      ‖valueCLM hΩ‖ ^ 2 * ‖x - y‖ ^ 2 +
        2 * ‖valueCLM hΩ‖ ^ 2 * ‖y‖ * ‖x - y‖ := by
  let L := valueCLM hΩ
  have hLx : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
  have hLy : ‖L y‖ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
  have hLsub : ‖L (x - y)‖ ≤ ‖L‖ * ‖x - y‖ := L.le_opNorm (x - y)
  have hx : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by
        congr 1
        abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hLx' : ‖L x‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) :=
    hLx.trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have hdiff : |‖L x‖ - ‖L y‖| ≤ ‖L‖ * ‖x - y‖ := by
    calc
      |‖L x‖ - ‖L y‖| ≤ ‖L x - L y‖ := abs_norm_sub_norm_le _ _
      _ = ‖L (x - y)‖ := by rw [L.map_sub]
      _ ≤ ‖L‖ * ‖x - y‖ := hLsub
  have hfactor : ‖L x‖ + ‖L y‖ ≤ ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by
    calc
      ‖L x‖ + ‖L y‖ ≤ ‖L‖ * (‖x - y‖ + ‖y‖) + ‖L‖ * ‖y‖ :=
        add_le_add hLx' hLy
      _ = ‖L‖ * ‖x - y‖ + 2 * ‖L‖ * ‖y‖ := by ring
  exact abs_sq_sub_le_of_bounds (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) (norm_nonneg _) hdiff hfactor
end HypoellipticAleksandrov.Parabolic.Dirichlet
