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

/-- The complete source sum of Hölder costs has a constant independent of J and m. -/
axiom source_holder_cost_sum_bound (gammaStar alpha0 t : ℝ)
    (hγ : 0 < gammaStar) (ht : alpha0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (J : ℕ) (m : ℝ), 0 < m →
      (∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b ^ t) ≤
        C * (2 : ℝ) ^ ((J : ℝ) * t) / m
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
 axiom sourcePartialPhase_at_depth (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (z : Fin d × Fin J → ℤ) : sourcePartialPhase U d J M gammaStar z J = 0
 
 

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

/-- Finite sums of actual smooth Hölder functions have a bound independent of
 the number of summands, apart from the sum of their norms. -/
axiom holderNorm_sum_le {d : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Covariate d → ℝ) (C : ι → ℝ) (t : ℝ) (ht : 0 < t)
    (hC : ∀ i ∈ S, 0 ≤ C i) (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hbound : ∀ i ∈ S, holderNorm (f i) t ≤ ENNReal.ofReal (C i)) :
    holderNorm (fun x => ∑ i ∈ S, f i x) t ≤ ENNReal.ofReal (2 * ∑ i ∈ S, C i)
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
 
end RoughRegime.Calculus

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_0fd12a6b82089993325e_SourceProfileRescale ====
@[expose] public section
/-! Uniform actual Hölder control after affine block rescaling. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper
 axiom source_profile_increment_holder_bound_rescale (U : SmoothStep) (d Q K : ℕ)
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
       ENNReal.ofReal (C*sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t)

/-- A rescaled base profile has its genuine ell^(-t) Hölder cost. -/
axiom base_profile_holder_bound_rescale {d : ℕ} (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0<lo) (hlt : lo<hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0=0) (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : 0<t) :
    ∃ C : ℝ, 0<C ∧ ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d,
      ∀ S ∈ Icc (0:ℝ) 1, ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      Model.holderNorm ((oscillatorProfile κ (intervalCenter lo hi) S h θ cut 0) ∘ scaleCoords origin ell) t ≤
        ENNReal.ofReal (C*ell⁻¹^t)
theorem source_profile_holder_bound_rescale (U : SmoothStep) (d Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (N : Set ℝ) (hN : IsOpen N) (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : alpha0<t)
    (hbudget : Model.holderOrder t+2 ≤ K) :
    ∃ C : ℝ, 0<C ∧ ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d, ∀ J M : ℕ, ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      Model.holderNorm
        ((oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
          (sourcePartialPhase U d J M gammaStar z 0)) ∘ scaleCoords origin ell) t ≤
      ENNReal.ofReal (C*ell⁻¹^t*(1+(2:ℝ)^((J:ℝ)*t)/m)) := by
  have ht0 : 0<t := ha0.trans_lt ht
  obtain ⟨Cb,hCb,hbase⟩ := base_profile_holder_bound_rescale κ lo hi hlo hlt N hN hκ hκ0 hinterval cut hcut hcompact hcut01 t ht0
  obtain ⟨Ci,hCi,hinc⟩ := source_profile_increment_holder_bound_rescale U d Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1
    hK hKQ κ lo hi hlo hlt N hN hκ hκ0 hinterval cut hcut hcompact hcut01 t ht0 hbudget
  obtain ⟨D,hD,hcost⟩ := source_holder_cost_sum_bound gammaStar alpha0 t hγ ht
  let C := 2*(Cb+Ci*D+1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro ell hell hell1 origin J M m hm z h hh θ
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  let S := sourceGate d J Q M gammaStar lambdaStar alpha0 m z
  let F (b : ℕ) := (oscillatorProfile κ (intervalCenter lo hi) S h θ cut (sourcePartialPhase U d J M gammaStar z b)) ∘ scaleCoords origin ell
  have hS : S ∈ Icc (0:ℝ) 1 := blockGate_range Q M _ _ z
  have hF (b : ℕ) : ContDiff ℝ ∞ (F b) := (oscillatorProfile_smooth κ lo hi hlo hlt N hN hκ hinterval S h θ hS hh cut _ hcut
    (sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z b) hcut01).comp (scaleCoords_smooth origin ell)
  let f : Option (Fin J) → Model.Covariate d → ℝ
    | none => F J
    | some b => F b.val-F (b.val+1)
  let cost : Option (Fin J) → ℝ
    | none => Cb*ell⁻¹^t
    | some b => Ci*sourceWeight gammaStar alpha0 m b.val*(sourceRate J gammaStar b.val/ell)^t
  have hnonneg (i : Option (Fin J)) : 0≤cost i := by
    cases i with
    | none => exact mul_nonneg hCb.le (Real.rpow_nonneg (inv_nonneg.mpr hell.le) _)
    | some b => dsimp [cost,sourceWeight,sourceRate,sourceGamma]; positivity
  have hbound (i : Option (Fin J)) : Model.holderNorm (f i) t ≤ ENNReal.ofReal (cost i) := by
    cases i with
    | none =>
      dsimp [f,F]
      rw [sourcePartialPhase_at_depth]
      exact hbase ell hell hell1 origin S hS h hh θ
    | some b => exact hinc ell hell hell1 origin J M b.val b.isLt m hm z h hh θ
  have hf (i : Option (Fin J)) : ContDiff ℝ ∞ (f i) := by
    cases i with
    | none => exact hF J
    | some b => exact (hF b.val).sub (hF (b.val+1))
  have hsum := Model.holderNorm_sum_le Finset.univ f cost t ht0 (fun i _ => hnonneg i) (fun i _ => hf i) (fun i _ => hbound i)
  have he : (fun x => ∑ i, f i x) = F 0 := by
    funext x
    rw [Fintype.sum_option]
    change F J x+(∑ i : Fin J, (F i.val x-F (i.val+1) x)) = F 0 x
    rw [Fin.sum_univ_eq_sum_range (fun b => F b x-F (b+1) x) J,Finset.sum_range_sub']
    ring
  have hc : (∑ i, cost i) = Cb*ell⁻¹^t+Ci*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) := by
    rw [Fintype.sum_option]
    change Cb*ell⁻¹^t+(∑ b : Fin J, Ci*sourceWeight gammaStar alpha0 m b.val*(sourceRate J gammaStar b.val/ell)^t) = _
    rw [Fin.sum_univ_eq_sum_range (fun b => Ci*sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) J]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he,hc] at hsum
  have hscale : 0≤(2:ℝ)^((J:ℝ)*t)/m := by positivity
  have hr : (∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) =
      ell⁻¹^t*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hL : 0 ≤ sourceRate J gammaStar b := by unfold sourceRate sourceGamma; positivity
    rw [Real.div_rpow hL hell.le,Real.inv_rpow hell.le]
    ring
  rw [hr] at hsum
  have hmul := mul_le_mul_of_nonneg_left (hcost J m hm0) hCi.le
  have hmul' : Ci*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^t) ≤ Ci*D*((2:ℝ)^((J:ℝ)*t)/m) := by
    convert hmul using 1 <;> ring
  have hcfinal : 2*(Cb+Ci*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^t)) ≤
      C*(1+(2:ℝ)^((J:ℝ)*t)/m) := by
    dsimp [C]
    nlinarith [mul_nonneg hCb.le hscale,mul_nonneg hCi.le hD]
  have hcfinal' := mul_le_mul_of_nonneg_left hcfinal (Real.rpow_nonneg (inv_nonneg.mpr hell.le) t)
  exact hsum.trans (ENNReal.ofReal_le_ofReal (by convert hcfinal' using 1 <;> ring))
end RoughRegime.LatticePriors
