module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v60add80bebc8.DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ComplexChartsAndSphericalSections
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation
open KPCplxPrincipalSeriesCharts
open scoped ContDiff
open Filter Topology Asymptotics
noncomputable def infinityCutoff (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℂ) :=
  ⟨r / 2, r, by positivity, by linarith⟩
private theorem infinityCutoff_scale (r : ℝ) (hr : 0 < r) :
    (infinityCutoff r hr : ℂ → ℝ) =
      (fun u => infinityCutoff 1 (by norm_num) (r⁻¹ • u)) := by
  funext u
  simp only [ContDiffBump.apply, infinityCutoff, sub_zero, smul_smul]
  have hratio : r / (r / 2) = 1 / (1 / 2 : ℝ) := by field_simp
  have hscale : (r / 2)⁻¹ = (1 / (1 / 2 : ℝ)) * r⁻¹ := by field_simp
  rw [hratio, hscale]
  norm_num
theorem infinityCutoff_derivative_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (hr : 0 < r) (u : ℂ),
      ‖iteratedFDeriv ℝ j (infinityCutoff r hr) u‖ ≤ C * (r⁻¹)^j := by
  let b := infinityCutoff 1 (by norm_num)
  have hc : Continuous (iteratedFDeriv ℝ j (b : ℂ → ℝ)) :=
    b.contDiff.continuous_iteratedFDeriv (by simp : (j : ℕ∞ω) ≤ (⊤ : ℕ∞))
  have hs := b.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) j
  have hb := (hs.isCompact_range hc).isBounded
  obtain ⟨C, hC⟩ := hb.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r hr u
  rw [infinityCutoff_scale r hr, iteratedFDeriv_comp_const_smul r⁻¹
    (b.contDiff (n := (j : ℕ∞)))]
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (r⁻¹)^j * max C 0 := mul_le_mul_of_nonneg_left
      ((hC _ (Set.mem_range_self (r⁻¹ • u))).trans (le_max_left _ _)) (by positivity)
    _ = _ := mul_comm _ _
end DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation
