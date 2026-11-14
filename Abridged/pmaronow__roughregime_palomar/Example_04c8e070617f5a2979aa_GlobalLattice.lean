module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Convolution
public import Mathlib
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.Fourier.Convolution
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v7c479b05cf58.RoughRegime.Model ====
public section
@[expose] public section
/-!
# The statistical model and main theorem statement

This module provides a model encoding on actual probability measures, with
Lebesgue random design, conditional expectations, coordinate derivatives,
and measurable randomized estimators. `PerModelUpperClaim`, `UniformUpperClaim`,
and `MainLowerClaim` record statements. `ModelUpper.lean` proves the uniform
upper bound with actual estimators. `ModelLower.lean` proves both lower
regimes from the original nondegeneracy condition, including the probability bound.

Coordinate derivatives are encoded by ordered lists of coordinate directions.
`MultiIndexHolder.lean` proves its exact equivalence to the paper's maximum
over classical multi-indices on the closed cube, using derivative symmetry
and boundary uniqueness. `KernelSeedBridge.lean` proves the representation of every real-output
randomized estimator by a uniform random seed, with equality of minimax risks.
`RiskBridge.lean` proves
the exact RMSE/squared-integral equivalence for the encoded experiment.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace RoughRegime.Model
abbrev Covariate (d : ℕ) := EuclideanSpace ℝ (Fin d)

end RoughRegime.Model

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v7c479b05cf58.RoughRegime.PairedGrid ====
public section
@[expose] public section
/-! The actual even Cartesian block grid and its affine local coordinates. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set
open scoped ContDiff
 abbrev GridPair (D N : ℕ) := Fin N × (Fin D → Fin (2 * N))
 abbrev GridBlock (D N : ℕ) := GridPair D N × Bool
 def gridCell {D N : ℕ} (b : GridBlock D N) : Fin (D + 1) → ℕ :=
  Fin.cons (2 * b.1.1.val + b.2.toNat) (fun q => (b.1.2 q).val)
 
 
 def gridOrigin {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) : Model.Covariate (D + 1) :=
  WithLp.toLp 2 (fun q => offset + ell * (gridCell b q : ℝ))
 def gridCoords {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N)
    (x : Model.Covariate (D + 1)) : Model.Covariate (D + 1) :=
  ell⁻¹ • (x - gridOrigin offset ell b)
 
 
 
 
 
 def gridBlockOpen {D N : ℕ} (offset ell : ℝ) (b : GridBlock D N) : Set (Model.Covariate (D + 1)) :=
  {x | ∀ q, 0 < gridCoords offset ell b x q ∧ gridCoords offset ell b x q < 1}
 
 
 
 
 
 
 
 
end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_04c8e070617f5a2979aa_GlobalLattice ====
@[expose] public section
/-! Actual globally glued lattice densities and profiles on the even grid. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped BigOperators ContDiff
 variable {D N : ℕ}
 def unitCubeOpen (d : ℕ) : Set (Model.Covariate d) := {x | ∀ q, 0 < x q ∧ x q < 1}
 def pulledCutoff (offset ell : ℝ) (b : GridBlock D N) (cutoff : Model.Covariate (D + 1) → ℝ) :
    Model.Covariate (D + 1) → ℝ := cutoff ∘ gridCoords offset ell b
 
 
 
 def globalNumerator (offset ell A : ℝ) (inner : Model.Covariate (D + 1) → ℝ)
    (σ S : GridPair D N → ℝ) (x : Model.Covariate (D + 1)) : ℝ :=
  ∑ b : GridBlock D N, A * σ b.1 * S b.1 * pulledCutoff offset ell b inner x
 
 
 
 
 
 
 
 
 
 
 set_option linter.unusedVariables false in
theorem globalNumerator_abs_bound (offset ell A : ℝ) (hell : 0 < ell)
    (inner : Model.Covariate (D + 1) → ℝ)
    (hin : ∀ y, y ∉ unitCubeOpen (D + 1) → inner y = 0)
    (hi : ∀ y, |inner y| ≤ 1) (σ S : GridPair D N → ℝ)
    (hσ : ∀ k, |σ k| ≤ 1) (hS : ∀ k, |S k| ≤ 1) (x : Model.Covariate (D + 1)) 
    (h_RoughRegime_LatticePriors_globalNumerator_outside : ∀ {D N : ℕ} (offset ell A : ℝ) (inner : RoughRegime.Model.Covariate (D + 1) → ℝ),
      (∀ y ∉ RoughRegime.LatticePriors.unitCubeOpen (D + 1), inner y = 0) →
        ∀ (σ S : RoughRegime.LatticePriors.GridPair D N → ℝ) (x : RoughRegime.Model.Covariate (D + 1)),
          (∀ (b : RoughRegime.LatticePriors.GridBlock D N),
              x ∉ RoughRegime.LatticePriors.gridBlockOpen offset ell b) →
            RoughRegime.LatticePriors.globalNumerator offset ell A inner σ S x = 0)
    (h_RoughRegime_LatticePriors_globalNumerator_eq_local : ∀ {D N : ℕ} (offset ell A : ℝ),
      0 < ell →
        ∀ (inner : RoughRegime.Model.Covariate (D + 1) → ℝ),
          (∀ y ∉ RoughRegime.LatticePriors.unitCubeOpen (D + 1), inner y = 0) →
            ∀ (σ S : RoughRegime.LatticePriors.GridPair D N → ℝ)
              (b : RoughRegime.LatticePriors.GridBlock D N),
              ∀ x ∈ RoughRegime.LatticePriors.gridBlockOpen offset ell b,
                RoughRegime.LatticePriors.globalNumerator offset ell A inner σ S x =
                  A * σ b.1 * S b.1 * inner (RoughRegime.LatticePriors.gridCoords offset ell b x))
    :
    |globalNumerator offset ell A inner σ S x| ≤ |A| := by
  by_cases hx : ∃ b : GridBlock D N, x ∈ gridBlockOpen offset ell b
  · obtain ⟨b, hb⟩ := hx
    rw [h_RoughRegime_LatticePriors_globalNumerator_eq_local offset ell A hell inner hin σ S b x hb, abs_mul, abs_mul, abs_mul]
    have hprod := mul_le_mul (mul_le_mul (hσ b.1) (hS b.1) (abs_nonneg _) zero_le_one)
      (hi (gridCoords offset ell b x)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
    have hm := mul_le_mul_of_nonneg_left hprod (abs_nonneg A)
    convert hm using 1 <;> ring
  · rw [h_RoughRegime_LatticePriors_globalNumerator_outside offset ell A inner hin σ S x (not_exists.mp hx), abs_zero]
    exact abs_nonneg A
 
 
 
 
 
 
end RoughRegime.LatticePriors
