import Mathlib
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.Convolution

-- ==== Examples.jconorgrogan__prime_minor_arcs_2_15.Examples.Example_17ff64af605f78365121_GuthMaynardAffineSmoothingSubpower ====
open scoped BigOperators Real FourierTransform
open MeasureTheory
noncomputable section
namespace GuthMaynardJIteration
/-!
# Smoothing with a subpower-mass kernel

The bump in Guth--Maynard Lemma 9.2 is one-bounded but may have support and
mass `T^δ`.  It is therefore not a unit-mass kernel.  The Proposition 9.1
iteration needs the exact resulting loss, rather than the unit-mass closure
proved in `GuthMaynardAffineSmoothingNorms`.
-/

/-- The Fourier transform of a nonnegative kernel of mass at most `K` has
norm at most `K`. -/
theorem norm_fourier_ofReal_le_mass
    (psi : ℝ → ℝ) (hpsi0 : ∀ z, 0 ≤ psi z)
    {K : ℝ} (hmass : ∫ z : ℝ, psi z ≤ K) (xi : ℝ) :
    ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤ K := by
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (fun z : ℝ => (psi z : ℂ)) xi
  change ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤
    ∫ z : ℝ, ‖(psi z : ℂ)‖ at hraw
  have hnorm : (∫ z : ℝ, ‖(psi z : ℂ)‖) = ∫ z : ℝ, psi z := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpsi0 z)]
  rw [hnorm] at hraw
  exact hraw.trans hmass
end GuthMaynardJIteration
