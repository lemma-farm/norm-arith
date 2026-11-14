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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.Lattice ====
public section
@[expose] public section
/-!
# Checked ingredients of the lattice construction

This file formalizes the pointwise sinc gate estimates and the finite
combinatorics used in Lemmas 13 and 14 of the supplied paper. It does **not**
claim that the lattice sampling identity, compact Fourier support, smoothness
bounds, or the complete prior lemma have been formalized.
-/
namespace RoughRegime.Lattice
open scoped BigOperators
noncomputable def gate (Q : ℕ) (scale x : ℝ) : ℝ :=
  Real.sinc (x / scale) ^ (2 * Q)

end RoughRegime.Lattice

end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.GateLaw ====
public section
@[expose] public section
namespace RoughRegime.LatticeFourier
open MeasureTheory Set Real Complex Filter Asymptotics
open scoped FourierTransform

/-- The Fourier convention used in the source paper. -/
noncomputable def paperFourier (f : ℝ → ℂ) (w : ℝ) : ℂ := 𝓕 f (-w / (2 * Real.pi))

noncomputable def latticeStep (M : ℕ) : ℝ := 2 * Real.pi / M

end RoughRegime.LatticeFourier

end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.SoftDigits ====
public section
@[expose] public section
namespace RoughRegime.LatticePriors
open Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
/-- The fixed smooth transition specified in the lattice construction. -/
structure SmoothStep where
  f : ℝ → ℝ
  smooth : ContDiff ℝ ∞ f
  monotone : Monotone f
  nonneg : ∀ x, 0 ≤ f x
  le_one : ∀ x, f x ≤ 1
  zero : ∀ x, x ≤ -1 → f x = 0
  one : ∀ x, 1 ≤ x → f x = 1
  half : f 0 = 1 / 2
/-- A concrete transition, so the construction does not require existence
of an unspecified smooth function as an axiom. -/
noncomputable def canonicalStep : SmoothStep where
  f x := Real.smoothTransition ((x + 1) / 2)
  smooth := by fun_prop
  monotone := by intro x y hxy; apply Real.smoothTransition.monotone; linarith
  nonneg x := Real.smoothTransition.nonneg _
  le_one x := Real.smoothTransition.le_one _
  zero x hx := Real.smoothTransition.zero_of_nonpos (by linarith)
  one x hx := Real.smoothTransition.one_of_one_le (by linarith)
  half := by
    norm_num [Real.smoothTransition]
    have hp : expNegInvGlue (1 / 2) ≠ 0 :=
      (expNegInvGlue.pos_of_pos (by norm_num)).ne'
    field_simp
    norm_num
/-- A single smoothed odd interval. The periodized pulse is exactly the
nearest-integer digit selector, because adjacent transition collars are disjoint. -/
noncomputable def softPulse (U : SmoothStep) (γ y : ℝ) : ℝ :=
  U.f ((y - 1) / γ) * U.f ((2 - y) / γ)
noncomputable def softDigit (U : SmoothStep) (γ y : ℝ) : ℝ :=
  ∑' z : ℤ, softPulse U γ (y - 2 * z)

end RoughRegime.LatticePriors

end
end

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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.LatticeConstruction ====
public section
@[expose] public section
/-! Concrete smooth block functions in the lattice prior construction. The
finite coefficients are actual points of the sampled lattice, and the selector
is proved equal to the source's nearest-integer selector. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Set MeasureTheory
open scoped BigOperators ContDiff
open RoughRegime.LatticeFourier RoughRegime.Lattice
variable {d : ℕ} {ι : Type*} [Fintype ι]
 def coordinateSoftDigit (U : SmoothStep) (γ : ℝ) (a : ℕ) (q : Fin d)
    (x : Model.Covariate d) : ℝ := softDigit U γ ((2 : ℝ) ^ a * x q)
 
 
 
 
 
 def blockGate (Q M : ℕ) (lam η : ι → ℝ) (z : ι → ℤ) : ℝ :=
  ∏ i, gate Q (lam i * η i) (latticeStep M * z i)
 axiom blockGate_range (Q M : ℕ) (lam η : ι → ℝ) (z : ι → ℤ) :
    0 ≤ blockGate Q M lam η z ∧ blockGate Q M lam η z ≤ 1

 
 
 
 
 
 

 

 
 
 
 
 
end RoughRegime.LatticePriors

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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.PhaseDerivatives ====
public section
@[expose] public section
/-! Actual weighted Frechet derivatives of every truncated hierarchical phase. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier
def partialBlockPhase {d : ℕ} {ι : Type*} (T : Finset ι) (U : SmoothStep) (M : ℕ)
    (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) (z : ι → ℤ) (x : Model.Covariate d) : ℝ :=
  ∑ i ∈ T, latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) x

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.LatticeScales ====
public section
@[expose] public section
/-! Finite constants for the geometric level scales in the lattice prior.
Their existence is derived from convergent concrete series. -/
noncomputable section
namespace RoughRegime.LatticePriors
open Filter
open scoped BigOperators
 
 
 
 
 
 

 def sourceGamma (gammaStar : ℝ) (b : ℕ) : ℝ := gammaStar / ((b : ℝ) + 1) ^ 2
 def sourceLambda (lambdaStar : ℝ) (b : ℕ) : ℝ := lambdaStar * ((b : ℝ) + 1)
 def sourceEta (gammaStar lambdaStar alpha0 m : ℝ) (b : ℕ) : ℝ :=
  sourceGamma gammaStar b * (2 : ℝ) ^ ((b : ℝ) * alpha0) / (sourceLambda lambdaStar b * m)
 
 
 
 

 
 
end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.HierarchicalSums ====
public section
@[expose] public section
/-! Uniform geometric sums for the concrete hierarchical Hölder scales. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.LatticePriors

/-- The source coefficient scale after applying the gate. -/
def sourceWeight (gammaStar alpha0 m : ℝ) (b : ℕ) : ℝ :=
  sourceGamma gammaStar b * (2 : ℝ) ^ ((b : ℝ) * alpha0) / m
/-- The digit selector's inverse spatial width. -/
def sourceRate (J : ℕ) (gammaStar : ℝ) (b : ℕ) : ℝ :=
  (2 : ℝ) ^ ((J : ℝ) - b) / sourceGamma gammaStar b

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.HierarchicalDerivativeSums ====
public section
@[expose] public section
/-! The true earlier-level derivative costs of the source hierarchy are
bounded by the last level, with constants independent of the hierarchy depth. -/
noncomputable section
open scoped BigOperators
namespace RoughRegime.LatticePriors

/-- All source spatial rates are at least one on their actual levels. -/
axiom sourceRate_ge_one (J b : ℕ) (gammaStar : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1) (hb : b ≤ J) :
    1 ≤ sourceRate J gammaStar b

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.HierarchicalPhases ====
public section
@[expose] public section
/-! The actual source phase truncations, and their last-level uniform jet
bounds. All coefficients come from the genuine bounded-product lattice gate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier
 def sourceLevels (d J b : ℕ) : Finset (Fin d × Fin J) :=
   Finset.univ.filter (fun i => b ≤ i.2.val)
 def sourcePartialPhase (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (z : Fin d × Fin J → ℤ) (b : ℕ) : Model.Covariate d → ℝ :=
   partialBlockPhase (sourceLevels d J b) U M (fun i => J-i.2.val) Prod.fst
     (fun i => sourceGamma gammaStar i.2.val) z
 def sourceGate (d J Q M : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
     (z : Fin d × Fin J → ℤ) : ℝ :=
   blockGate Q M (fun i => sourceLambda lambdaStar i.2.val)
     (fun i => sourceEta gammaStar lambdaStar alpha0 m i.2.val) z
 
 
 axiom sourcePartialPhase_smooth (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (z : Fin d × Fin J → ℤ) (b : ℕ) :
     ContDiff ℝ ∞ (sourcePartialPhase U d J M gammaStar z b)
 
 
 

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.SourceProfileJets ====
public section
@[expose] public section
/-! The fully instantiated true local source-profile increment jet bound,
uniform over every hierarchy depth, lattice realization and phase. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open  RoughRegime.Upper

/-- The same true bound holds on the whole ambient space for a compactly
supported cutoff, enabling affine rescaling and disjoint block gluing. -/
axiom source_profile_increment_jet_bound_global (U : SmoothStep) (d Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (N : Set ℝ) (hN : IsOpen N) (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (n : ℕ) (hn : n+1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ J M b : ℕ, b < J → ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      ∀ x : Model.Covariate d,
      ‖iteratedFDeriv ℝ n
        (oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
            (sourcePartialPhase U d J M gammaStar z b) -
         oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
            (sourcePartialPhase U d J M gammaStar z (b+1))) x‖ ≤
       C * sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^n
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

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_dc335d98bd5f8a188e88_SourceProfileRescale ====
@[expose] public section
/-! Uniform actual Hölder control after affine block rescaling. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper
 theorem source_profile_increment_holder_bound_rescale (U : SmoothStep) (d Q K : ℕ)
     (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
     (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
     (N : Set ℝ) (hN : IsOpen N) (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
     (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
     (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
     (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : 0<t)
     (hbudget : Model.holderOrder t+2 ≤ K) :
     ∃ C : ℝ, 0<C ∧ ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d, ∀ J M b : ℕ, b<J → ∀ m : ℝ,
       (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
       ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
       Model.holderNorm
         ((oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
             (sourcePartialPhase U d J M gammaStar z b) -
          oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
             (sourcePartialPhase U d J M gammaStar z (b+1))) ∘ scaleCoords origin ell) t ≤
       ENNReal.ofReal (C*sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) := by
   let n := Model.holderOrder t+1
   have hn : n+1 ≤ K := by dsimp [n]; omega
   have he (i : Fin (n+1)) := source_profile_increment_jet_bound_global U d Q K gammaStar lambdaStar alpha0
     hγ hγ1 hlam ha0 ha1 hK hKQ κ lo hi hlo hlt N hN hκ hκ0 hinterval cut hcut hcompact hcut01 i.val (by omega : i.val+1 ≤ K)
   choose C hC hb using he
   let B : ℝ := ∑ i : Fin (n+1), C i
   have hB : 0<B := by
     have hzero := hC (⟨0,by omega⟩ : Fin (n+1))
     have hs := Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ (⟨0,by omega⟩ : Fin (n+1)))
     dsimp [B]
     linarith
   refine ⟨3*B,by positivity,?_⟩
   intro ell hell hell1 origin J M b hbJ m hm z h hh θ
   let SG := sourceGate d J Q M gammaStar lambdaStar alpha0 m z
   let w := sourceWeight gammaStar alpha0 m b
   let L := sourceRate J gammaStar b
   let f₁ := oscillatorProfile κ (intervalCenter lo hi) SG h θ cut (sourcePartialPhase U d J M gammaStar z b)
   let f₂ := oscillatorProfile κ (intervalCenter lo hi) SG h θ cut (sourcePartialPhase U d J M gammaStar z (b+1))
   have hSG : SG ∈ Icc (0:ℝ) 1 := blockGate_range Q M _ _ z
   have hf₁ : ContDiff ℝ ∞ f₁ := oscillatorProfile_smooth κ lo hi hlo hlt N hN hκ hinterval SG h θ hSG hh cut _ hcut
     (sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z b) hcut01
   have hf₂ : ContDiff ℝ ∞ f₂ := oscillatorProfile_smooth κ lo hi hlo hlt N hN hκ hinterval SG h θ hSG hh cut _ hcut
     (sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z (b+1)) hcut01
   have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
   have hw : 0≤w := by dsimp [w,sourceWeight,sourceGamma]; positivity
   have hL : 1≤L := sourceRate_ge_one J b gammaStar hγ (by linarith) (Nat.le_of_lt hbJ)
   have hLscale : 1≤L/ell := (le_div_iff₀ hell).mpr (by simpa only [one_mul] using hell1.trans hL)
   have hjets (k : ℕ) (hk : k≤Model.holderOrder t+1) (x : Model.Covariate d) (_hx : x∈Model.cube d) :
       ‖iteratedFDeriv ℝ k ((f₁-f₂) ∘ scaleCoords origin ell) x‖ ≤ (B*w)*(L/ell)^k := by
     let i : Fin (n+1) := ⟨k,by dsimp [n]; omega⟩
     have hCi : C i≤B := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
     have hi := hb i J M b hbJ m hm z h hh θ (scaleCoords origin ell x)
     have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hw)
       (pow_nonneg (zero_lt_one.trans_le hL).le k)
     have hpull := norm_iteratedFDeriv_rescale (f₁-f₂) (hf₁.sub hf₂) origin ell hell k x
     calc
       _ ≤ ‖iteratedFDeriv ℝ k (f₁-f₂) (scaleCoords origin ell x)‖*ell⁻¹^k := hpull
       _ ≤ (B*w)*L^k*ell⁻¹^k := mul_le_mul_of_nonneg_right (hi.trans hmul) (by positivity)
       _ = _ := by rw [div_eq_mul_inv,mul_pow]; ring
   have hnorm := Model.holderNorm_le_of_scaled_iteratedFDeriv_bound ((f₁-f₂) ∘ scaleCoords origin ell) t ht
     ((hf₁.sub hf₂).comp (scaleCoords_smooth origin ell)) (B*w) (L/ell) (mul_nonneg hB.le hw) hLscale hjets
   convert hnorm using 1 <;> dsimp [f₁,f₂,w,L,SG] <;> congr 1 <;> ring

end RoughRegime.LatticePriors
