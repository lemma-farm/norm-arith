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
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.Lattice ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.GateLaw ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.SoftDigits ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.Model ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.LatticeConstruction ====
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
 

 
 
 
 
 
 

 

 
 
 
 
 
end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.GateRoot ====
public section
@[expose] public section
/-! A deterministic root of the gate controls every actual phase coefficient.
This retains the gate factor in higher-order composition bounds. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.Lattice
variable {ι : Type*} [Fintype ι]
def gateRoot (S : ℝ) (K : ℕ) : ℝ := S ^ (1 / (K : ℝ))

end RoughRegime.LatticePriors

end
end
end

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.PhaseDerivatives ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.LatticeScales ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v969f4c5902b0.RoughRegime.HierarchicalSums ====
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

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_97b8e6b02efc1edba81c_HierarchicalPhases ====
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
 
 
 
 
 
 set_option linter.unusedVariables false in
/-- Every positive-order true partial-phase derivative is controlled by the
last source level, with a constant independent of J,M,m and the realization. -/
 theorem sourcePartialPhase_derivative_bound (U : SmoothStep) (d Q K : ℕ)
     (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (hlam : 0 < lambdaStar) (ha : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (k : ℕ) (hk : 0 < k) 
    (h_RoughRegime_LatticePriors_source_scale_product : ∀ (gammaStar lambdaStar alpha0 m : ℝ) (b : ℕ),
      0 < lambdaStar →
        RoughRegime.LatticePriors.sourceLambda lambdaStar b *
            RoughRegime.LatticePriors.sourceEta gammaStar lambdaStar alpha0 m b =
          RoughRegime.LatticePriors.sourceWeight gammaStar alpha0 m b)
    (h_RoughRegime_LatticePriors_gateRoot_phase_derivative_bound : ∀ (U : RoughRegime.LatticePriors.SmoothStep) (N : ℕ),
      ∃ (C : ℝ),
        0 < C ∧
          ∀ {d : ℕ} {ι : Type} [inst : Fintype ι] (T : Finset ι) (Q M K : ℕ) (a : ι → ℕ) (q : ι → Fin d)
            (γ lam η : ι → ℝ) (z : ι → ℤ),
            0 < K →
              K ≤ 2 * Q →
                (∀ (i : ι), 0 < γ i) →
                  (∀ (i : ι), γ i ≤ 1 / 4) →
                    (∀ (i : ι), 0 < lam i * η i) →
                      ∀ (x : RoughRegime.Model.Covariate d),
                        RoughRegime.LatticePriors.gateRoot
                              (RoughRegime.LatticePriors.blockGate Q M lam η z) K *
                            ‖iteratedFDeriv ℝ N
                                (RoughRegime.LatticePriors.partialBlockPhase T U M a q γ z) x‖ ≤
                          C * ∑ i ∈ T, lam i * η i * (2 ^ a i / γ i) ^ N)
    (h_RoughRegime_LatticePriors_source_rate_eq : ∀ (J b : ℕ) (gammaStar : ℝ),
      b ≤ J →
        2 ^ (J - b) / RoughRegime.LatticePriors.sourceGamma gammaStar b =
          RoughRegime.LatticePriors.sourceRate J gammaStar b)
    (h_RoughRegime_LatticePriors_source_derivative_tail_bound : ∀ (gammaStar alpha0 : ℝ),
      0 < gammaStar →
        alpha0 < 1 →
          ∀ (k : ℕ),
            0 < k →
              ∃ (C : ℝ),
                0 ≤ C ∧
                  ∀ (J b T : ℕ) (m : ℝ),
                    0 < m →
                      ∑ i ∈ Finset.range T,
                          RoughRegime.LatticePriors.sourceWeight gammaStar alpha0 m (b + i) *
                            RoughRegime.LatticePriors.sourceRate J gammaStar (b + i) ^ k ≤
                        C *
                          (RoughRegime.LatticePriors.sourceWeight gammaStar alpha0 m b *
                            RoughRegime.LatticePriors.sourceRate J gammaStar b ^ k))
    (h_RoughRegime_LatticePriors_sourceLevels_cost_sum : ∀ (d J b : ℕ) (f : ℕ → ℝ),
      ∑ i ∈ RoughRegime.LatticePriors.sourceLevels d J b, f (↑i.2 : ℕ) =
        (↑d : ℝ) * ∑ k ∈ Finset.Ico b J, f k)
    (h_RoughRegime_LatticePriors_sourceGamma_le_quarter : ∀ (gammaStar : ℝ) (b : ℕ),
      0 < gammaStar → gammaStar ≤ 1 / 4 → RoughRegime.LatticePriors.sourceGamma gammaStar b ≤ 1 / 4)
    :
     ∃ C : ℝ, 0 ≤ C ∧ ∀ J M b c : ℕ, b ≤ c → ∀ m : ℝ, 0 < m →
       ∀ z : Fin d × Fin J → ℤ, ∀ x : Model.Covariate d,
       gateRoot (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) K *
         ‖iteratedFDeriv ℝ k (sourcePartialPhase U d J M gammaStar z c) x‖ ≤
       C * (sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^k) := by
   obtain ⟨C,hC,hphase⟩ := h_RoughRegime_LatticePriors_gateRoot_phase_derivative_bound U k
   obtain ⟨D,hD,htail⟩ := h_RoughRegime_LatticePriors_source_derivative_tail_bound gammaStar alpha0 hγ ha k hk
   refine ⟨C*(d:ℝ)*D,mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg d)) hD,?_⟩
   intro J M b c hbc m hm z x
   have hg (i : Fin d × Fin J) : 0 < sourceGamma gammaStar i.2.val := by unfold sourceGamma; positivity
   have hs (i : Fin d × Fin J) : 0 < sourceLambda lambdaStar i.2.val * sourceEta gammaStar lambdaStar alpha0 m i.2.val := by
     rw [h_RoughRegime_LatticePriors_source_scale_product gammaStar lambdaStar alpha0 m _ hlam]
     unfold sourceWeight sourceGamma
     positivity
   have hb := hphase (sourceLevels d J c) Q M K (fun i => J-i.2.val) Prod.fst
     (fun i => sourceGamma gammaStar i.2.val) (fun i => sourceLambda lambdaStar i.2.val)
     (fun i => sourceEta gammaStar lambdaStar alpha0 m i.2.val) z hK hKQ hg
     (fun i => h_RoughRegime_LatticePriors_sourceGamma_le_quarter gammaStar _ hγ hγ1) hs x
   have he : (∑ i ∈ sourceLevels d J c,
       (sourceLambda lambdaStar i.2.val * sourceEta gammaStar lambdaStar alpha0 m i.2.val) *
       ((2:ℝ)^(J-i.2.val)/sourceGamma gammaStar i.2.val)^k) =
       (d:ℝ)*∑ v ∈ Finset.Ico c J,
         sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k := by
     simp_rw [h_RoughRegime_LatticePriors_source_scale_product gammaStar lambdaStar alpha0 m _ hlam]
     rw [← h_RoughRegime_LatticePriors_sourceLevels_cost_sum d J c (fun v => sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k)]
     apply Finset.sum_congr rfl
     intro i hi
     rw [h_RoughRegime_LatticePriors_source_rate_eq J i.2.val gammaStar (Nat.le_of_lt i.2.isLt)]
   rw [he] at hb
   have hsum : (∑ v ∈ Finset.Ico c J, sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k) ≤
       ∑ v ∈ Finset.Ico b J, sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k := by
     apply Finset.sum_le_sum_of_subset_of_nonneg
     · intro v hv
       simp only [Finset.mem_Ico] at hv ⊢
       exact ⟨hbc.trans hv.1,hv.2⟩
     · intro v _ _
       unfold sourceWeight sourceRate sourceGamma
       positivity
   have hb' := hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)) hC.le)
   rw [Finset.sum_Ico_eq_sum_range] at hb'
   have hh := mul_le_mul_of_nonneg_left (htail J b (J-b) m hm) (mul_nonneg hC.le (Nat.cast_nonneg d))
   exact hb'.trans (by convert hh using 1 <;> ring)

end RoughRegime.LatticePriors
