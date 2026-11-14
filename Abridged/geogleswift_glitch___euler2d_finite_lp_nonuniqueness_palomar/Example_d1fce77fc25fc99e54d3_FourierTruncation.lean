module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircleMulti

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_d1fce77fc25fc99e54d3_FourierTruncation ====
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
/-- The orthogonal projection retaining precisely a finite set of basis modes. -/
def trunc (s : Finset ι) : E →L[𝕜] E :=
  ∑ i ∈ s, (innerSL 𝕜 (b i)).smulRight (b i)

end FourierProjection
attribute [local instance] instMeasureSpaceUnitAddCircle
/-- Scalar complex `L²` on the normalized two-dimensional quotient torus. -/
abbrev FourierL2 := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 2)))
/-- Fourier frequencies retained in the square `[-N,N]²`. -/
def fourierModes (N : ℕ) : Finset (Fin 2 → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- The continuous linear square Fourier truncation. -/
def fourierTrunc (N : ℕ) : FourierL2 →L[ℂ] FourierL2 :=
  FourierProjection.trunc UnitAddTorus.mFourierBasis (fourierModes N)
def frequencySq (k : Fin 2 → ℤ) : ℝ := (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2


set_option linter.unusedVariables false in
/-- Each velocity component has the Fourier tail controlled by the
vorticity, with the correct normalization on the unit torus. -/
theorem fourier_velocity_tail_le (N : ℕ) (hN : 0 < N) (u₀ u₁ ω : FourierL2)
    (hdiv : ∀ k, (k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k +
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k = 0)
    (hcurl : ∀ k, (2 * Real.pi : ℂ) * Complex.I *
      ((k 0 : ℂ) * UnitAddTorus.mFourierCoeff u₁ k -
      (k 1 : ℂ) * UnitAddTorus.mFourierCoeff u₀ k) = UnitAddTorus.mFourierCoeff ω k) 
    (h_Euler2D_norm_sub_fourierTrunc_le : ∀ (N : ℕ),
      0 < N →
        ∀ (f : ↥Euler2D.FourierL2) {M : ℝ},
          0 ≤ M →
            (∀ (s : Finset (Fin 2 → ℤ)),
                ∑ k ∈ s,
                    Euler2D.frequencySq k *
                      ‖UnitAddTorus.mFourierCoeff
                            (↑(↑f : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                              UnitAddTorus (Fin 2) → ℂ)
                            k‖ ^
                        2 ≤
                  M ^ 2) →
              ‖f - (Euler2D.fourierTrunc N : ↥Euler2D.FourierL2 → ↥Euler2D.FourierL2) f‖ ≤ M / (↑N : ℝ))
    (h_Euler2D_frequencySq_nonneg : ∀ (k : Fin 2 → ℤ), 0 ≤ Euler2D.frequencySq k)
    (h_Euler2D_fourier_velocity_weighted_bound : ∀ (u₀ u₁ ω : ↥Euler2D.FourierL2),
      (∀ (k : Fin 2 → ℤ),
          (↑(k 0) : ℂ) *
                UnitAddTorus.mFourierCoeff
                  (↑(↑u₀ : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                    UnitAddTorus (Fin 2) → ℂ)
                  k +
              (↑(k 1) : ℂ) *
                UnitAddTorus.mFourierCoeff
                  (↑(↑u₁ : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                    UnitAddTorus (Fin 2) → ℂ)
                  k =
            0) →
        (∀ (k : Fin 2 → ℤ),
            2 * (↑Real.pi : ℂ) * Complex.I *
                ((↑(k 0) : ℂ) *
                    UnitAddTorus.mFourierCoeff
                      (↑(↑u₁ : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                        UnitAddTorus (Fin 2) → ℂ)
                      k -
                  (↑(k 1) : ℂ) *
                    UnitAddTorus.mFourierCoeff
                      (↑(↑u₀ : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                        UnitAddTorus (Fin 2) → ℂ)
                      k) =
              UnitAddTorus.mFourierCoeff
                (↑(↑ω : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                  UnitAddTorus (Fin 2) → ℂ)
                k) →
          ∀ (s : Finset (Fin 2 → ℤ)),
            ∑ k ∈ s,
                Euler2D.frequencySq k *
                  (‖UnitAddTorus.mFourierCoeff
                          (↑(↑u₀ : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                            UnitAddTorus (Fin 2) → ℂ)
                          k‖ ^
                      2 +
                    ‖UnitAddTorus.mFourierCoeff
                          (↑(↑u₁ : UnitAddTorus (Fin 2) →ₘ[MeasureTheory.MeasureSpace.volume] ℂ) :
                            UnitAddTorus (Fin 2) → ℂ)
                          k‖ ^
                      2) ≤
              (‖ω‖ / (2 * Real.pi)) ^ 2)
    :
    ‖u₀ - fourierTrunc N u₀‖ ≤ (‖ω‖ / (2 * Real.pi)) / N ∧
    ‖u₁ - fourierTrunc N u₁‖ ≤ (‖ω‖ / (2 * Real.pi)) / N := by
  have hbound := h_Euler2D_fourier_velocity_weighted_bound u₀ u₁ ω hdiv hcurl
  constructor
  · apply h_Euler2D_norm_sub_fourierTrunc_le N hN u₀ (by positivity)
    intro s
    apply le_trans _ (hbound s)
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (sq_nonneg _)) (h_Euler2D_frequencySq_nonneg k)
  · apply h_Euler2D_norm_sub_fourierTrunc_le N hN u₁ (by positivity)
    intro s
    apply le_trans _ (hbound s)
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (sq_nonneg _)) (h_Euler2D_frequencySq_nonneg k)
/-! ## Fourier test functions in the original fundamental-square model -/
end Euler2D
end
