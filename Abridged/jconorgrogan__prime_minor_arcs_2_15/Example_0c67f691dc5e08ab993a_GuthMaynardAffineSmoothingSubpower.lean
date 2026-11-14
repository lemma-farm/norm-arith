import Mathlib
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Fourier.Convolution

-- ==== Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.vcbe7a62ade52.GuthMaynardJIterationPoisson ====
section
/-!
# Changes of variables and second Poisson step in Guth--Maynard Lemma 9.2

This module formalizes the analytic identities in TeX lines 1534--1542 and
1591--1645 of `LargevaluesDirichlet17.tex`:

* Fourier dilation, with the absolute Jacobian required when `m₁ < 0`;
* the affine frequency substitution `xi = ell*m₁ + (m₁/M₃)*tau`;
* the scaled and modulated Poisson formula with its exact `T/M₂` factor;
* constant-one domination of a `C/T`-localized integral by the affine
  smoothing used in Lemma 9.2.

The source changes the affine denominator from `M₃` in TeX 1598 to `M₁`
in TeX 1606.  `source_frequency_affine_argument` proves that the stated
substitution gives `M₃`; no silent correction is made here.
-/
open scoped BigOperators Real FourierTransform SchwartzMap ContDiff
open MeasureTheory
noncomputable section
namespace GuthMaynardJIteration

/-- The smoothing used in Lemma 9.2, with the source normalization `T` kept
outside the kernel. -/
def affineSmoothing (T : ℝ) (psi f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u : ℝ, T * psi (T * (x - u)) * f u

end GuthMaynardJIteration

end
end

-- ==== Examples.jconorgrogan__prime_minor_arcs_2_15.Examples.Example_0c67f691dc5e08ab993a_GuthMaynardAffineSmoothingSubpower ====
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
set_option linter.unusedVariables false in
/-- A positive kernel whose mass is at most `K` enlarges a pointwise source
bound by at most the same factor. -/
theorem affineSmoothing_le_mass_mul
    {T S K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hS : 0 ≤ S)
    (hf0 : ∀ u, 0 ≤ f u) (hf_le : ∀ u, f u ≤ S)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hfCont : Continuous f) (x : ℝ) 
    (h_GuthMaynardJIteration_integrable_affineSmoothing_kernel : ∀ {T : ℝ},
      0 < T →
        ∀ {psi : ℝ → ℝ},
          MeasureTheory.Integrable psi MeasureTheory.MeasureSpace.volume →
            MeasureTheory.Integrable (fun (y : ℝ) ↦ T * psi (T * y)) MeasureTheory.MeasureSpace.volume)
    (h_GuthMaynardJIteration_integral_affineSmoothing_kernel : ∀ {T : ℝ}, 0 < T → ∀ (psi : ℝ → ℝ) (x : ℝ), ∫ (u : ℝ), T * psi (T * (x - u)) = ∫ (z : ℝ), psi z)
    :
    affineSmoothing T psi f x ≤ K * S := by
  let k : ℝ → ℝ := fun u => T * psi (T * (x - u))
  have hk : Integrable k := by
    simpa only [k] using
      (h_GuthMaynardJIteration_integrable_affineSmoothing_kernel hT hpsi).comp_sub_left x
  have hk0 : ∀ u, 0 ≤ k u := fun u => mul_nonneg hT.le (hpsi0 _)
  have hleft : Integrable (fun u => k u * f u) := by
    have hbound : ∀ᵐ u : ℝ ∂volume, ‖f u‖ ≤ S := by
      filter_upwards with u
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(neg_nonpos.mpr hS).trans (hf0 u), hf_le u⟩
    exact (hk.bdd_mul hfCont.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hright : Integrable (fun u => k u * S) := hk.mul_const S
  have hmono : (∫ u : ℝ, k u * f u) ≤ ∫ u : ℝ, k u * S := by
    apply integral_mono_ae hleft hright
    filter_upwards with u
    exact mul_le_mul_of_nonneg_left (hf_le u) (hk0 u)
  calc
    affineSmoothing T psi f x = ∫ u : ℝ, k u * f u := by rfl
    _ ≤ ∫ u : ℝ, k u * S := hmono
    _ = (∫ z : ℝ, psi z) * S := by
      rw [integral_mul_const, h_GuthMaynardJIteration_integral_affineSmoothing_kernel hT psi x]
    _ ≤ K * S := mul_le_mul_of_nonneg_right hmass hS

end GuthMaynardJIteration
