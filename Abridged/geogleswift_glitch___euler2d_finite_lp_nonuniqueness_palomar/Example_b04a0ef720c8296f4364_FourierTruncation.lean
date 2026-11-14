module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircleMulti

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_b04a0ef720c8296f4364_FourierTruncation ====
/-!
# Finite Fourier projections and quantitative tails on the two-dimensional torus

The measure on the unit quotient torus in this file is normalized Haar measure.
The operators below are actual finite sums of Fourier modes, rather than an
assumed family of compact approximations.  The weighted estimate is the
spectral estimate needed after the distributional div--curl identities have
been transferred from the fundamental square to the quotient torus.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace Euler2D
namespace FourierProjection
variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] (b : HilbertBasis ι 𝕜 E)
end FourierProjection
attribute [local instance] instMeasureSpaceUnitAddCircle
/-- Scalar complex `L²` on the normalized two-dimensional quotient torus. -/
abbrev FourierL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))

def frequencySq (k : Fin 2 → ℤ) : ℝ := (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2

set_option linter.unusedVariables false in
/-- The finite weighted velocity sum is bounded by the vorticity `L²` norm
once the Fourier div--curl identities have been established.  The factor
`2π` from a unit-period spatial derivative is included explicitly. -/
theorem fourier_velocity_weighted_bound (u₀ u₁ ω : FourierL2)
    (hdiv : ∀ k, (k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k = 0)
    (hcurl : ∀ k, (2 * Real.pi : ℂ) * Complex.I *
      ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k) = UnitAddTorus.mFourierCoeff ω k)
    (s : Finset (Fin 2 → ℤ)) 
    (h_Euler2D_fourier_div_curl_identity : ∀ (k : Fin 2 → ℤ) (a b : ℂ),
      Euler2D.frequencySq k * (‖a‖ ^ 2 + ‖b‖ ^ 2) =
        ‖(↑(k 0) : ℂ) * a + (↑(k 1) : ℂ) * b‖ ^ 2 + ‖(↑(k 0) : ℂ) * b - (↑(k 1) : ℂ) * a‖ ^ 2)
    :
    ∑ k ∈ s, frequencySq k *
      (‖UnitAddTorus.mFourierCoeff u₀ k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff u₁ k‖ ^ 2) ≤ (‖ω‖ / (2 * Real.pi)) ^ 2 := by
  have hpoint : ∀ k, (2 * Real.pi) ^ 2 * (frequencySq k *
      (‖UnitAddTorus.mFourierCoeff u₀ k‖ ^ 2 +
       ‖UnitAddTorus.mFourierCoeff u₁ k‖ ^ 2)) =
      ‖UnitAddTorus.mFourierCoeff ω k‖ ^ 2 := by
    intro k
    rw [h_Euler2D_fourier_div_curl_identity, hdiv k, norm_zero, zero_pow (by decide : 2 ≠ 0),
      zero_add, ← hcurl k, norm_mul, norm_mul, mul_pow, mul_pow]
    simp [Complex.norm_I, abs_of_pos Real.pi_pos, mul_pow]
  rw [div_pow]
  apply (le_div_iff₀ (sq_pos_of_pos (by positivity : 0 < 2 * Real.pi))).mpr
  calc
    _ = ∑ k ∈ s, ‖UnitAddTorus.mFourierCoeff ω k‖ ^ 2 := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; exact hpoint k
    _ ≤ ‖ω‖ ^ 2 := by
      simpa only [← UnitAddTorus.mFourierBasis_repr, HilbertBasis.repr_apply_apply] using
        UnitAddTorus.mFourierBasis.orthonormal.sum_inner_products_le ω (s := s)
end Euler2D
end
