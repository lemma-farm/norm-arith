module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.ReflectionDefinitions ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
namespace MathCollab.Density
/-- The explicit Dirichlet phase, using the real logarithm. -/
def dirichletPhase (x v : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((v * Real.log x : ℝ) : ℂ))
/-- Reflection only needs the real smooth cutoff and its support condition. -/
structure ReflectionCutoff where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  support : tsupport toFun ⊆ Icc (1 / 2 : ℝ) 5
instance : CoeFun ReflectionCutoff (fun _ => ℝ → ℝ) := ⟨ReflectionCutoff.toFun⟩

def cutoffIntegral (w : ReflectionCutoff) (v : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (w x : ℂ) * dirichletPhase x v
/-- The n=0 summand vanishes by the support condition; all nonzero terms are finite. -/
def hKernel (w : ReflectionCutoff) (L v : ℝ) : ℂ :=
  (∑' n : ℕ, (w ((n : ℝ) / L) : ℂ) * dirichletPhase ((n : ℝ) / L) v) -
    (L : ℂ) * cutoffIntegral w v

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.LargeValueDefinitions ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set
open scoped BigOperators ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density
/-- The source polynomial has support (N,2N], distinct from the auxiliary [M,2M). -/
def detectingPolynomial (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * dirichletPhase ((n : ℝ)/N) t
def kernelEnergy (w : ReflectionCutoff) (L : ℝ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, ‖hKernel w L (t-u)‖ ^ 2
def oneSeparated (U : Finset ℝ) : Prop :=
  ∀ t ∈ U, ∀ u ∈ U, t ≠ u → 1 ≤ |t-u|
def intervalSpan (U : Finset ℝ) : ℝ :=
  if h : U.Nonempty then U.max' h - U.min' h else 0
def localDiameter (U : Finset ℝ) : ℝ := 1 + intervalSpan U
def divisorMaximum (T : ℝ) : ℕ :=
  (Finset.Icc 1 ⌈32*(T+1)⌉₊).sup (fun m => m.divisors.card)
def bootstrapScalar (T : ℝ) (N : ℕ) (V : ℝ) : ℝ :=
  (N : ℝ) * divisorMaximum T / V^2
/-- Only the packet's original large-value hypotheses; no analytic conclusion is a field. -/
structure LargeValueData (κ : ℝ) where
  T : ℝ
  N : ℕ
  V : ℝ
  a : ℕ → ℂ
  W : Finset ℝ
  t₀ : ℝ
  T_ge_two : 2 ≤ T
  N_pos : 0 < N
  V_pos : 0 < V
  scale_lower : T ^ (1/3 : ℝ) ≤ (N : ℝ)
  scale_upper : (N : ℝ) ≤ T
  height : (N : ℝ) ^ (3/4+κ) ≤ V
  coefficients : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1
  location : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T
  separated : oneSeparated W
  large : ∀ t ∈ W, V ≤ ‖detectingPolynomial N a t‖

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.Packing ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Set MeasureTheory
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

axiom localDiameter_ge_one (U : Finset ℝ) : 1 ≤ localDiameter U

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.ComparisonCutoff ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density
/-- The stronger fixed cutoff required only for the comparison step. -/
structure ComparisonCutoff extends ReflectionCutoff where
  nonneg : ∀ x, 0 ≤ toFun x
  one_on : ∀ x ∈ Icc (1 : ℝ) 4, toFun x = 1
instance : CoeFun ComparisonCutoff (fun _ => ℝ → ℝ) := ⟨fun w => w.toFun⟩

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.BootstrapDomain ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- All nonempty subsets form a finite localization family closed under the reflection windows. -/
def bootstrapFamily (W : Finset ℝ) : Finset (Finset ℝ) := W.powerset.filter Finset.Nonempty
axiom mem_bootstrapFamily {W U : Finset ℝ} :
    U ∈ bootstrapFamily W ↔ U ⊆ W ∧ U.Nonempty

/-- The normalization has a uniform positive lower bound on the actual recursion domain. -/
axiom LargeValueData.normalization_lower {κ : ℝ} (d : LargeValueData κ)
    {U : Finset ℝ} (hU : U ∈ bootstrapFamily d.W) {L : ℝ} (hNL : (d.N : ℝ) ≤ L) :
    (d.N : ℝ) ≤ bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U)
end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.BootstrapSupremum ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def bootstrapValues (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ) : Set ℝ :=
  {x | ∃ U ∈ bootstrapFamily d.W, ∃ L ∈ Icc (d.N : ℝ) (8*(d.T+1)),
    x = kernelEnergy w L U /
      (bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U))}
def bootstrapBound (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ) : ℝ :=
  sSup (bootstrapValues w d)
axiom bootstrapValues_nonempty (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) : (bootstrapValues w d).Nonempty

axiom bootstrapBound_nonneg (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) : 0 ≤ bootstrapBound w d

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v2cd4246135b6.MathCollab.Density.Comparison ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set
open scoped BigOperators ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

axiom bootstrapScalar_nonneg (T V : ℝ) (N : ℕ) : 0 ≤ bootstrapScalar T N V

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_83bd6ffa2e9fcc4940a9_BootstrapAbsorption ====
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density
/-- Uniform shell summation, retaining the local diameter and the logarithmic shell count. -/
axiom bootstrap_preabsorption (w : ComparisonCutoff) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      ∀ (U : Finset ℝ) (L : ℝ), U ⊆ d.W → (d.N : ℝ) ≤ L →
      kernelEnergy w.toReflectionCutoff L U ≤
        2*C*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*localDiameter U*U.card +
        C*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
          (2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*(Real.log (2*d.T)/Real.log 2)) +
        E*d.T^(-90 : ℝ)
/-- Scalar absorption with the precise Nb² log(2T) coefficient and constants before all data. -/
theorem bootstrap_absorption_inequality (w : ComparisonCutoff) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      bootstrapBound w.toReflectionCutoff d ≤ C₀ +
        C₁*(d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.log (2*d.T)*bootstrapBound w.toReflectionCutoff d := by
  obtain ⟨C, E, hC, hE, hpre⟩ := bootstrap_preabsorption w
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2*C+E, 2*C/Real.log 2, by positivity, by positivity, ?_⟩
  intro κ d hW
  apply csSup_le (bootstrapValues_nonempty w.toReflectionCutoff d hW)
  rintro x ⟨U, hU, L, hL, rfl⟩
  let b := bootstrapScalar d.T d.N d.V
  let B := bootstrapBound w.toReflectionCutoff d
  let D := b*U.card*(L^2+(d.N : ℝ)*localDiameter U)
  let ℓ := Real.log (2*d.T)/Real.log 2
  have hb : 0 ≤ b := bootstrapScalar_nonneg d.T d.V d.N
  have hB : 0 ≤ B := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hD : 1 ≤ D := (by exact_mod_cast d.N_pos : (1 : ℝ) ≤ d.N).trans (d.normalization_lower hU hL.1)
  have hDp : 0 < D := by linarith
  have hℓ : 1 ≤ ℓ := (le_div_iff₀ hlog2).2 (by
    simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith [d.T_ge_two] : 2 ≤ 2*d.T))
  have hp := hpre d hW U L (mem_bootstrapFamily.mp hU).1 hL.1
  have hlead : 2*C*b*(d.N : ℝ)*localDiameter U*U.card ≤ 2*C*D := by
    have hh := mul_nonneg (show 0 ≤ 2*C*b*U.card by positivity) (sq_nonneg L)
    dsimp [D]
    nlinarith
  have hinner : 2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*ℓ ≤
      2*ℓ*(d.N : ℝ)*(L^2+(d.N : ℝ)*localDiameter U) := by
    have hd := localDiameter_ge_one U
    have hh := mul_nonneg (show 0 ≤ ℓ-1 by linarith)
      (show 0 ≤ (d.N : ℝ)^2*localDiameter U by positivity)
    have hi := mul_nonneg (show 0 ≤ ℓ by linarith) (show 0 ≤ (d.N : ℝ)*L^2 by positivity)
    nlinarith
  have hrec := mul_le_mul_of_nonneg_left hinner (show 0 ≤ C*B*b^3*U.card by positivity)
  have hpow : d.T^(-90 : ℝ) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith [d.T_ge_two] : 1 ≤ d.T)
      (by norm_num : (-90 : ℝ) ≤ 0)
    simpa only [Real.rpow_zero] using hh
  have he₀ : E*1 ≤ E*D := mul_le_mul_of_nonneg_left hD hE
  have he : E*d.T^(-90 : ℝ) ≤ E*D := (mul_le_mul_of_nonneg_left hpow hE).trans he₀
  change kernelEnergy w.toReflectionCutoff L U / D ≤ _
  apply (div_le_iff₀ hDp).2
  have hrewrite : (2*C/Real.log 2)*(d.N : ℝ)*b^2*Real.log (2*d.T)*B*D =
      C*B*b^3*U.card*(2*ℓ*(d.N : ℝ)*(L^2+(d.N : ℝ)*localDiameter U)) := by
    dsimp [D, ℓ]
    ring
  dsimp [b, B, ℓ] at hrewrite hlead hrec he
  rw [add_mul]
  rw [hrewrite]
  dsimp [D, b] at he hlead ⊢
  nlinarith
end MathCollab.Density
