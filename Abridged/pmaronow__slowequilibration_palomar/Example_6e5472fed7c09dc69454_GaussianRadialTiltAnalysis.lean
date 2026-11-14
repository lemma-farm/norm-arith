module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- ==== Examples.pmaronow__slowequilibration_palomar.Dependencies.vb5f483631523.SlowEquilibration.GaussianRadialEnergyTilt ====
public section
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! Exact completion of the radial Gaussian square under the physical
energy tilt. Normalization bounds are obtained by integrating the actual
tilted density; no tilted probability or count limit is assumed. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory  
set_option maxHeartbeats 300000
def tiltedDensity (w : ℝ → ℝ) (N A B c₀ m σ k : ℝ) : ℝ :=
  w k*Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))
end SlowEquilibration.GaussianRadialEnergyTilt

end
end
end

-- ==== Examples.pmaronow__slowequilibration_palomar.Examples.Example_6e5472fed7c09dc69454_GaussianRadialTiltAnalysis ====
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! Genuine integral regularity of the exact radial energy reweighting.
Only the original nonnegative radial density and a bounded radial interval
are used, rather than an assumed normalized tail or count limit. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000
def energyDensity (w : ℝ → ℝ) (U : Set ℝ) (N A B c₀ m σ : ℝ) : ℝ :=
  ∫ k in U,tiltedDensity w N A B c₀ m σ k


set_option linter.unusedVariables false in
/-- Continuous dependence on unnormalized physical energy follows by
actual dominated convergence against the original radial density. -/
theorem energyDensity_continuous {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 ≤ A) (hN : 0<N) (hM : 0 ≤ M)
    (hRadius : ∀ k∈U,|k-m| ≤ M) 
    (h_SlowEquilibration_GaussianRadialEnergyTilt_tiltedDensity_integrableOn : ∀ {w : ℝ → ℝ} {U : Set ℝ},
      MeasurableSet U →
        MeasureTheory.IntegrableOn w U MeasureTheory.MeasureSpace.volume →
          (∀ k ∈ U, 0 ≤ w k) →
            ∀ {N A B c₀ m M : ℝ},
              0 ≤ A →
                0 < N →
                  (∀ k ∈ U, |k - m| ≤ M) →
                    ∀ (σ : ℝ),
                      MeasureTheory.IntegrableOn
                        (SlowEquilibration.GaussianRadialEnergyTilt.tiltedDensity w N A B c₀ m σ) U
                        MeasureTheory.MeasureSpace.volume)
    (h_SlowEquilibration_GaussianRadialEnergyTilt_scalar_tilt_upper : ∀ {A N M : ℝ},
      0 ≤ A →
        0 < N →
          ∀ {B c₀ m σ k : ℝ},
            |k - m| ≤ M → -c₀ * σ - B * (k - m) * σ - A * σ ^ 2 / (2 * N) ≤ (|c₀| + |B| * M) * |σ|)
    : Continuous (energyDensity w U N A B c₀ m) := by
  apply continuous_iff_continuousAt.mpr
  intro σ₀
  let C := Real.exp ((|c₀|+|B| * M)*(|σ₀|+1))
  have hCoef : 0 ≤ |c₀|+|B| * M := by positivity
  have hNear : ∀ᶠ σ : ℝ in 𝓝 σ₀,|σ| < |σ₀|+1 :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by linarith : |σ₀| < |σ₀|+1))
  have hBound : ∀ᶠ σ : ℝ in 𝓝 σ₀,∀ᵐ k ∂volume.restrict U,
      ‖tiltedDensity w N A B c₀ m σ k‖ ≤ C*w k := by
    filter_upwards [hNear] with σ hσ
    filter_upwards [ae_restrict_mem hU] with k hk
    rw [Real.norm_of_nonneg (show 0 ≤ tiltedDensity w N A B c₀ m σ k from
      mul_nonneg (h0 k hk) (Real.exp_pos _).le)]
    have he := (Real.exp_le_exp.mpr (h_SlowEquilibration_GaussianRadialEnergyTilt_scalar_tilt_upper (B := B) (c₀ := c₀) (σ := σ) hA hN (hRadius k hk))).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.le hCoef))
    exact (mul_le_mul_of_nonneg_left he (h0 k hk)).trans_eq (by dsimp [C];ring)
  exact tendsto_integral_filter_of_dominated_convergence (fun k => C*w k)
    (Eventually.of_forall fun σ => (h_SlowEquilibration_GaussianRadialEnergyTilt_tiltedDensity_integrableOn hU hw h0 hA hN hRadius σ).aestronglyMeasurable)
    hBound (hw.const_mul C) (ae_of_all _ (fun k => by
      exact (by unfold tiltedDensity;fun_prop : Continuous (fun σ : ℝ =>
        tiltedDensity w N A B c₀ m σ k)).continuousAt.tendsto))
end SlowEquilibration.GaussianRadialEnergyTilt
