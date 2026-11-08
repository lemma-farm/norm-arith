module
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Data.PNat.Basic
set_option autoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal
namespace DiscriminativeKalmanFilter
/-- The state space ℝᵈ with its standard Borel structure and Lebesgue measure. -/
abbrev State (d : ℕ) := Fin d → ℝ
/-- Real d × d matrices; positive definiteness is required explicitly. -/
abbrev Covariance (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
/-- Real-valued functions on the state space. -/
abbrev Density (d : ℕ) := State d → ℝ
variable {d : ℕ}
/-- η_d(z; m, C), the normalized multivariate Gaussian formula. Used with C positive definite. -/
def gaussianPDF (m : State d) (C : Covariance d) (z : State d) : ℝ :=
  (Real.sqrt ((2 * Real.pi) ^ d * C.det))⁻¹ *
    Real.exp (-((z - m) ⬝ᵥ (C⁻¹ *ᵥ (z - m))) / 2)
/-- A Lebesgue probability density: nonnegative almost everywhere, integrable, and of integral one. -/
def IsPDF (f : Density d) : Prop :=
  (∀ᵐ z ∂volume, 0 ≤ f z) ∧ Integrable f volume ∧ (∫ z, f z ∂volume) = 1
/-- A pdf equal almost everywhere to a nondegenerate Gaussian density. -/
def IsGaussianPDF (f : Density d) : Prop :=
  IsPDF f ∧ ∃ (m : State d) (C : Covariance d), C.PosDef ∧
    f =ᵐ[volume] gaussianPDF m C
/-- The measure with density f relative to Lebesgue measure. -/
def densityMeasure (f : Density d) : Measure (State d) :=
  volume.withDensity (fun z => ENNReal.ofReal (f z))
/-- Lebesgue L¹ norm, extended-valued so invalid weights are not mistaken for integrable ones. -/
def l1Norm (f : Density d) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal |f z| ∂volume
/-- L¹ distance between two densities. Finite when both are pdfs. -/
def l1Distance (f g : Density d) : ℝ≥0∞ := l1Norm (f - g)
/-- Weak convergence tested against every bounded continuous real function, as in Appendix B. -/
def Weakly (f : ℕ+ → Density d) (P : Measure (State d)) : Prop :=
  ∀ g : BoundedContinuousFunction (State d) ℝ,
    Tendsto (fun n => ∫ z, g z ∂densityMeasure (f n)) atTop (𝓝 (∫ z, g z ∂P))
end DiscriminativeKalmanFilter
