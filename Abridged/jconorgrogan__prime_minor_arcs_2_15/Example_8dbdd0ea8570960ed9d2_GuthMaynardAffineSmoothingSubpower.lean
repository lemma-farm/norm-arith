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

-- ==== Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.vcbe7a62ade52.GuthMaynardJIterationSourceFourierDecay ====
section
/-!
# Source Fourier-decay quantifiers in Guth--Maynard Lemma 9.2

The hypothesis following the statement of Lemma 9.2 is kept literally: for
every positive loss exponent and every nonnegative integer decay order there
is a constant, uniform in the frequency.  `S` represents `sup_u f(u)`.
-/
open scoped BigOperators Real FourierTransform
noncomputable section
namespace GuthMaynardJIteration
def SourceFourierRapidDecay
    (fhat : ℝ → ℂ) (T S : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : ℝ, z ≠ 0 →
      ‖fhat z‖ ≤ C * T ^ eta * (T / |z|) ^ j * S

end GuthMaynardJIteration

end
end

-- ==== Examples.jconorgrogan__prime_minor_arcs_2_15.Examples.Example_8dbdd0ea8570960ed9d2_GuthMaynardAffineSmoothingSubpower ====
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
/-- Rapid Fourier decay survives smoothing with the exact multiplicative
mass loss exposed in the new sup-norm parameter `K*S`. -/
theorem sourceFourierRapidDecay_affineSmoothing_mass
    {T S K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hS : 0 ≤ S)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hpsiCont : Continuous psi) (hfCont : Continuous f)
    (hdecay : SourceFourierRapidDecay
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) T S) 
    (h_GuthMaynardJIteration_fourier_ofReal_affineSmoothing : ∀ {T : ℝ},
      0 < T →
        ∀ (psi f : ℝ → ℝ),
          MeasureTheory.Integrable psi MeasureTheory.MeasureSpace.volume →
            MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
              Continuous psi →
                Continuous f →
                  ∀ (xi : ℝ),
                    FourierTransform.fourier
                        (fun (x : ℝ) ↦ (↑(GuthMaynardJIteration.affineSmoothing T psi f x) : ℂ)) xi =
                      FourierTransform.fourier (fun (u : ℝ) ↦ (↑(f u) : ℂ)) xi *
                        FourierTransform.fourier (fun (z : ℝ) ↦ (↑(psi z) : ℂ)) (xi / T))
    (h_GuthMaynardJIteration_norm_fourier_ofReal_le_mass : ∀ (psi : ℝ → ℝ),
      (∀ (z : ℝ), 0 ≤ psi z) →
        ∀ {K : ℝ},
          ∫ (z : ℝ), psi z ≤ K →
            ∀ (xi : ℝ), ‖FourierTransform.fourier (fun (z : ℝ) ↦ (↑(psi z) : ℂ)) xi‖ ≤ K)
    :
    SourceFourierRapidDecay
      (FourierTransform.fourier
        (fun x : ℝ => (affineSmoothing T psi f x : ℂ))) T (K * S) := by
  intro eta heta j
  obtain ⟨C, hC, hbound⟩ := hdecay eta heta j
  refine ⟨C, hC, ?_⟩
  intro z hz
  rw [h_GuthMaynardJIteration_fourier_ofReal_affineSmoothing hT psi f hpsi hf hpsiCont hfCont z,
    norm_mul]
  have hk := h_GuthMaynardJIteration_norm_fourier_ofReal_le_mass psi hpsi0 hmass (z / T)
  have hfz := hbound z hz
  have hrhs0 : 0 ≤ C * T ^ eta * (T / |z|) ^ j * S := by
    positivity
  calc
    ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ *
        ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (z / T)‖ ≤
      (C * T ^ eta * (T / |z|) ^ j * S) * K := by
        exact mul_le_mul hfz hk (norm_nonneg _) hrhs0
    _ = C * T ^ eta * (T / |z|) ^ j * (K * S) := by ring

end GuthMaynardJIteration
