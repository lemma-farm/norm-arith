module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Concrete.Weights
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Concrete.GaussianProbability
public import Mathlib
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.ENNReal.Real
@[expose] public section
/-!
# Concrete Gaussian density and Ginibre measure

The Gaussian reference measure `complexGaussianMeasure n` is constructed in
`GaussianProbability.lean` as a genuine finite product probability measure.
This file also defines the explicit density measure

`(n / π)^n exp (-n |z|²) dz`.

Equality of these two descriptions is stated explicitly as
`ComplexGaussianDensityIdentificationStatement`; it is not hidden in a
definition.  The unnormalised Ginibre measure is then `|V_n|² γ_n`, and its
actual total mass is used for normalization.
-/
open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section
/-- Canonical Lebesgue/Haar volume on the finite-dimensional real space `ℂⁿ`. -/
def configurationVolume (n : ℕ) : Measure (Configuration n) :=
  volume
/-- Explicit density of the normalized complex Gaussian reference measure. -/
def complexGaussianDensity (n : ℕ) (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((((n : ℝ) / Real.pi) ^ n) * gaussianWeight n z)
/-- Measure defined directly by the explicit Gaussian density. -/
def complexGaussianDensityMeasure (n : ℕ) : Measure (Configuration n) :=
  (configurationVolume n).withDensity (complexGaussianDensity n)
/-- Identification of the product Gaussian law with its explicit Lebesgue
 density.  This is the remaining Gaussian density theorem. -/
def ComplexGaussianDensityIdentificationStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    complexGaussianMeasure n = complexGaussianDensityMeasure n
def vandermondeDensity {n : ℕ} (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z)
end
end GinibrePoincare
