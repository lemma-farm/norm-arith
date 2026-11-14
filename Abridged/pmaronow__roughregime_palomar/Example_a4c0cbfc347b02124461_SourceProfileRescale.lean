module

public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
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
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.Model ====
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
def cube (d : ℕ) : Set (Covariate d) := {x | ∀ j, x j ∈ Set.Icc (0 : ℝ) 1}

def holderOrder (t : ℝ) : ℕ := Nat.ceil t - 1
def holderExponent (t : ℝ) : ℝ := t - holderOrder t
def coordinateDerivative {d : ℕ} (f : Covariate d → ℝ) (q : ℕ)
    (σ : Fin q → Fin d) (x : Covariate d) : ℝ :=
  iteratedFDerivWithin ℝ q f (cube d) x (fun j ↦ EuclideanSpace.single (σ j) 1)
def derivativeSup {d : ℕ} (f : Covariate d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_ : q ≤ k) (σ : Fin q → Fin d) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |coordinateDerivative f q σ x|
def holderSeminorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (σ : Fin (holderOrder t) → Fin d) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x -
      coordinateDerivative f (holderOrder t) σ y| / ‖x - y‖ ^ holderExponent t)
def holderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) then
    derivativeSup f (holderOrder t) + holderSeminorm f t else ∞

end RoughRegime.Model

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.Upper ====
public section
@[expose] public section
/-!
Algebraic and analytic ingredients of Section 4.
The declarations explicitly document which paper claims they cover.
-/
noncomputable section
open scoped BigOperators
open Complex
namespace RoughRegime.Upper
/-- The complete cosine generating series, with its constant term corrected to one. -/
def cosineKernel (q : ℂ) (t : ℝ) : ℂ :=
  2 * (∑' k : ℕ, q ^ k * (Real.cos ((k : ℝ) * t) : ℂ)) - 1

/-- The midpoint, half-width, geometric mean, and convergence ratio of the paper. -/
def intervalCenter (lo hi : ℝ) : ℝ := (hi + lo) / 2
def intervalHalfWidth (lo hi : ℝ) : ℝ := (hi - lo) / 2

open MeasureTheory ProbabilityTheory

end RoughRegime.Upper

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.ReciprocalComposition ====
public section
@[expose] public section
/-! True uniformly amplitude-scaled outer jets for the reciprocal and smooth
scalar composition used in the lattice Hölder proof. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open  RoughRegime.Upper
/-- The full outer family; the density oscillation and cutoff are parameters. -/
def oscillatorOuter (κ : ℝ → ℝ) (center : ℝ) (S : ℝ) (v : ℝ × (ℝ × ℝ)) : ℝ :=
  κ (S * v.2.1 / (center + v.1 * Real.cos v.2.2))

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.PhaseInputs ====
public section
@[expose] public section
/-! True jets of the phase and cutoff map used in reciprocal composition. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.LatticePriors
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def phaseInput (h θ : ℝ) (cut φ : E → ℝ) (x : E) : ℝ × (ℝ × ℝ) :=
  (h,(cut x,θ+φ x))

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.ProfileJets ====
public section
@[expose] public section
/-! Genuine reciprocal profile increment jets. Uniform constants arise from
actual smooth outer families and the finite derivative composition formula. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open  RoughRegime.Upper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def oscillatorProfile (κ : ℝ → ℝ) (center S h θ : ℝ) (cut φ : E → ℝ) : E → ℝ :=
  oscillatorOuter κ center S ∘ phaseInput h θ cut φ

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.LatticeHolder ====
public section
@[expose] public section
/-! Hölder interpolation and the source's uniformly summable hierarchical scales. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace RoughRegime.Model

/-- The norm of a smooth function whose q-th derivative is bounded by A L^q
is at most3 A L^t. This retains the fractional Hölder exponent. -/
axiom holderNorm_le_of_scaled_iteratedFDeriv_bound {d : ℕ}
    (f : Covariate d → ℝ) (t : ℝ) (ht : 0 < t) (hf : ContDiff ℝ ∞ f)
    (A L : ℝ) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hb : ∀ q, q ≤ holderOrder t + 1 → ∀ x ∈ cube d,
      ‖iteratedFDeriv ℝ q f x‖ ≤ A * L ^ q) :
    holderNorm f t ≤ ENNReal.ofReal (3 * A * L ^ t)

end RoughRegime.Model

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.SourceProfileHolder ====
public section
@[expose] public section
/-! Actual Hölder control of every source increment, with its exact fractional
exponent. This uses proved true derivative bounds and geometric source scales. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open  RoughRegime.Upper
 axiom oscillatorProfile_smooth {d : ℕ} (κ : ℝ → ℝ) (lo hi : ℝ)
     (hlo : 0<lo) (hlt : lo<hi) (N : Set ℝ) (hN : IsOpen N)
     (hκ : ContDiffOn ℝ ∞ κ N) (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
     (S h θ : ℝ) (hS : S ∈ Icc (0:ℝ) 1)
     (hh : h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi))
     (cut φ : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hp : ContDiff ℝ ∞ φ)
     (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1) :
     ContDiff ℝ ∞ (oscillatorProfile κ (intervalCenter lo hi) S h θ cut φ)
 

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.AffineJets ====
public section
@[expose] public section
/-! True Frechet jets under the source affine block rescaling. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Calculus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
 def scaleCoords (origin : E) (ell : ℝ) (x : E) : E := ell⁻¹ • (x-origin)
 axiom scaleCoords_smooth (origin : E) (ell : ℝ) : ContDiff ℝ ∞ (scaleCoords origin ell)
 axiom norm_iteratedFDeriv_rescale (f : E → F) (hf : ContDiff ℝ ∞ f)
     (origin : E) (ell : ℝ) (hell : 0<ell) (q : ℕ) (x : E) :
     ‖iteratedFDeriv ℝ q (f ∘ scaleCoords origin ell) x‖ ≤
       ‖iteratedFDeriv ℝ q f (scaleCoords origin ell x)‖*ell⁻¹^q
end RoughRegime.Calculus

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_a4c0cbfc347b02124461_SourceProfileRescale ====
@[expose] public section
/-! Uniform actual Hölder control after affine block rescaling. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper
 
axiom base_profile_jet_bound_global {d : ℕ} (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0<lo) (hlt : lo<hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0=0) (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut) (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1)
    (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ S ∈ Icc (0:ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      ∀ q ≤ n, ∀ x : Model.Covariate d,
      ‖iteratedFDeriv ℝ q (oscillatorProfile κ (intervalCenter lo hi) S h θ cut 0) x‖ ≤ C
/-- A rescaled base profile has its genuine ell^(-t) Hölder cost. -/
theorem base_profile_holder_bound_rescale {d : ℕ} (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0<lo) (hlt : lo<hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0=0) (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : 0<t) :
    ∃ C : ℝ, 0<C ∧ ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d,
      ∀ S ∈ Icc (0:ℝ) 1, ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      Model.holderNorm ((oscillatorProfile κ (intervalCenter lo hi) S h θ cut 0) ∘ scaleCoords origin ell) t ≤
        ENNReal.ofReal (C*ell⁻¹^t) := by
  obtain ⟨C,hC,hjets⟩ := base_profile_jet_bound_global κ lo hi hlo hlt N hN hκ hκ0 hinterval cut hc hcompact hcut (Model.holderOrder t+1)
  refine ⟨3*C,by positivity,?_⟩
  intro ell hell hell1 origin S hS h hh θ
  let f := oscillatorProfile κ (intervalCenter lo hi) S h θ cut 0
  have hf : ContDiff ℝ ∞ f := oscillatorProfile_smooth κ lo hi hlo hlt N hN hκ hinterval S h θ hS hh cut 0 hc contDiff_const hcut
  have hL : 1≤ell⁻¹ := (one_le_inv₀ hell).mpr hell1
  have hb (q : ℕ) (hq : q≤Model.holderOrder t+1) (x : Model.Covariate d) (_hx : x∈Model.cube d) :
      ‖iteratedFDeriv ℝ q (f ∘ scaleCoords origin ell) x‖ ≤ C*ell⁻¹^q := by
    exact (norm_iteratedFDeriv_rescale f hf origin ell hell q x).trans
      (mul_le_mul_of_nonneg_right (hjets S hS h hh θ q hq _) (by positivity))
  exact Model.holderNorm_le_of_scaled_iteratedFDeriv_bound (f ∘ scaleCoords origin ell) t ht
    (hf.comp (scaleCoords_smooth origin ell)) C ell⁻¹ hC.le hL hb

end RoughRegime.LatticePriors
