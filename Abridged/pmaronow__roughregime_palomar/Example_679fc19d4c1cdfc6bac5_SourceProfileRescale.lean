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

-- ==== Examples.pmaronow__roughregime_palomar.Dependencies.v9fb6ebe41f22.RoughRegime.JetComposition ====
public section
@[expose] public section
/-! Uniform quantitative continuity of higher derivative composition, obtained
from the actual finite Faà di Bruno formula. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators ContDiff
namespace RoughRegime.Calculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The local Faà di Bruno bound at a genuine spatial scale L. -/
axiom local_composition_jet_norm_bound_scaled (g : F → G) (f : E → F) (x : E) (n : ℕ)
    (hg : ContDiffAt ℝ ∞ g (f x)) (hf : ContDiffAt ℝ ∞ f x)
    (C L : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (houter : ∀ k, k ≤ n → ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C)
    (hinner : ∀ k, 1 ≤ k → k ≤ n → ‖iteratedFDeriv ℝ k f x‖ ≤ L^k) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤ (Fintype.card (OrderedFinpartition n) : ℝ)*C*L^n
end RoughRegime.Calculus

end
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
open RoughRegime.Calculus RoughRegime.Upper
/-- The full outer family; the density oscillation and cutoff are parameters. -/
def oscillatorOuter (κ : ℝ → ℝ) (center : ℝ) (S : ℝ) (v : ℝ × (ℝ × ℝ)) : ℝ :=
  κ (S * v.2.1 / (center + v.1 * Real.cos v.2.2))

/-- Actual local smoothness holds at every admissible realized phase. -/
axiom oscillatorOuter_contDiffAt (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N)
    (S : ℝ) (hS : S ∈ Icc (0 : ℝ) 1) (h a φ : ℝ)
    (hh : h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi))
    (ha : a ∈ Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ))

/-- One constant simultaneously controls the finite jet family and its true
angular differences. -/
axiom oscillatorOuter_finite_jet_bound (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0 < lo) (hlt : lo < hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0 : ℝ) (1 / lo) ⊆ N) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k ≤ n, ∀ S ∈ Icc (0 : ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ a ∈ Icc (0 : ℝ) 1, ∀ φ ψ : ℝ,
      ‖iteratedFDeriv ℝ k (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ))‖ ≤ C*S ∧
      ‖iteratedFDeriv ℝ k (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,φ)) -
        iteratedFDeriv ℝ k (oscillatorOuter κ (intervalCenter lo hi) S) (h,(a,ψ))‖ ≤ C*S*|φ-ψ|
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
axiom phaseInput_contDiffAt (h θ : ℝ) (cut φ : E → ℝ) (x : E)
    (hc : ContDiffAt ℝ ∞ cut x) (hp : ContDiffAt ℝ ∞ φ x) :
    ContDiffAt ℝ ∞ (phaseInput h θ cut φ) x
/-- True positive-order jets are exactly the cutoff and phase jets. -/
axiom norm_phaseInput_jet (h θ : ℝ) (cut φ : E → ℝ) (x : E) (k : ℕ)
    (hk : 0 < k) (hc : ContDiffAt ℝ ∞ cut x) (hp : ContDiffAt ℝ ∞ φ x) :
    ‖iteratedFDeriv ℝ k (phaseInput h θ cut φ) x‖ =
      max ‖iteratedFDeriv ℝ k cut x‖ ‖iteratedFDeriv ℝ k φ x‖

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
open RoughRegime.Calculus RoughRegime.Upper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def oscillatorProfile (κ : ℝ → ℝ) (center S h θ : ℝ) (cut φ : E → ℝ) : E → ℝ :=
  oscillatorOuter κ center S ∘ phaseInput h θ cut φ

end RoughRegime.LatticePriors

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
open RoughRegime.Calculus RoughRegime.Upper
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

-- ==== Examples.pmaronow__roughregime_palomar.Examples.Example_679fc19d4c1cdfc6bac5_SourceProfileRescale ====
@[expose] public section
/-! Uniform actual Hölder control after affine block rescaling. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper
 
theorem base_profile_jet_bound_global {d : ℕ} (κ : ℝ → ℝ) (lo hi : ℝ)
    (hlo : 0<lo) (hlt : lo<hi) (N : Set ℝ) (hN : IsOpen N)
    (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0=0) (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut) (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1)
    (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ S ∈ Icc (0:ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      ∀ q ≤ n, ∀ x : Model.Covariate d,
      ‖iteratedFDeriv ℝ q (oscillatorProfile κ (intervalCenter lo hi) S h θ cut 0) x‖ ≤ C := by
  obtain ⟨B,hB,hcutjet⟩ := hcompact.exists_bound_iteratedFDeriv hc n
  let L : ℝ := max B 1
  have hL : 1≤L := le_max_right _ _
  obtain ⟨C,hC,houter⟩ := oscillatorOuter_finite_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval n
  let cost (q : ℕ) : ℝ := (Fintype.card (OrderedFinpartition q):ℝ)*C*L^q
  let H : ℝ := 1+∑ q ∈ Finset.range (n+1), cost q
  have hcost (q : ℕ) : 0≤cost q := by dsimp [cost]; positivity
  have hH : 0<H := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun q _ => hcost q)
    dsimp [H]
    linarith
  refine ⟨H,hH,?_⟩
  intro S hS h hh θ
  let g := oscillatorOuter κ (intervalCenter lo hi) S
  let f := phaseInput h θ cut (0 : Model.Covariate d → ℝ)
  have hgf : ContDiff ℝ ∞ (g ∘ f) := oscillatorProfile_smooth κ lo hi hlo hlt N hN hκ hinterval S h θ hS hh cut 0 hc contDiff_const hcut
  have hjets (q : ℕ) (hq : q≤n) (x : Model.Covariate d)  :
      ‖iteratedFDeriv ℝ q (g ∘ f) x‖ ≤ H := by
    have hg : ContDiffAt ℝ ∞ g (f x) := by
      simpa [g,f,phaseInput] using oscillatorOuter_contDiffAt κ lo hi hlo hlt N hN hκ hinterval S hS h (cut x) θ hh (hcut x)
    have hf : ContDiffAt ℝ ∞ f x := phaseInput_contDiffAt h θ cut 0 x hc.contDiffAt contDiffAt_const
    have ho (k : ℕ) (hk : k≤q) : ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C := by
      have he := (houter k (hk.trans hq) S hS h hh (cut x) (hcut x) θ θ).1
      have hCS : C*S ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS.2 hC.le
      simpa [g,f,phaseInput] using he.trans hCS
    have hi (k : ℕ) (hk0 : 1≤k) (hk : k≤q) : ‖iteratedFDeriv ℝ k f x‖ ≤ L^k := by
      have hkpos : 0<k := by omega
      rw [norm_phaseInput_jet h θ cut 0 x k hkpos hc.contDiffAt contDiffAt_const,
        iteratedFDeriv_zero]
      simp only [Pi.zero_apply,norm_zero,max_eq_left (norm_nonneg _)]
      exact (hcutjet k (hk.trans hq) x).trans ((le_max_left B 1).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hL hk0))
    have hb := local_composition_jet_norm_bound_scaled g f x q hg hf C L hC.le (zero_lt_one.trans_le hL).le ho hi
    have hs : cost q ≤ H := by
      have hh := Finset.single_le_sum (fun i _ => hcost i) (Finset.mem_range.mpr (show q<n+1 by omega))
      dsimp [H]
      linarith
    exact hb.trans hs
  exact hjets

end RoughRegime.LatticePriors
