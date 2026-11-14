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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.ReflectionDefinitions ====
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
/-- The nonzero Poisson-mode integral in the exact source convention. -/
def modeIntegral (w : ℝ → ℂ) (v k : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), w x *
    Complex.exp (((v * Real.log x - 2 * Real.pi * k * x : ℝ) : ℂ) * Complex.I)
def cutoffIntegral (w : ReflectionCutoff) (v : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (w x : ℂ) * dirichletPhase x v
/-- The n=0 summand vanishes by the support condition; all nonzero terms are finite. -/
def hKernel (w : ReflectionCutoff) (L v : ℝ) : ℂ :=
  (∑' n : ℕ, (w ((n : ℝ) / L) : ℂ) * dirichletPhase ((n : ℝ) / L) v) -
    (L : ℂ) * cutoffIntegral w v
def dyadicPolynomial (M : ℕ) (v : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ico M (2 * M), dirichletPhase ((q : ℝ) / M) v
def completePairEnergy (M : ℕ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, ‖dyadicPolynomial M (t - u)‖ ^ 2
def shellEnergy (w : ReflectionCutoff) (L H : ℝ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, if H ≤ |t-u| ∧ |t-u| < 2*H then ‖hKernel w L (t-u)‖ ^ 2 else 0
/-- The exact fixed band, without a scale-dependent enlargement. -/
def inReflectionBand (L H : ℝ) (m : ℤ) : Prop :=
  0 < m ∧ H / (20 * Real.pi * L) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * H / (Real.pi * L)
instance (L H : ℝ) (m : ℤ) : Decidable (inReflectionBand L H m) := Classical.propDecidable _
def localSet (U : Finset ℝ) (H : ℝ) (j : ℤ) : Finset ℝ :=
  U.filter (fun t => (j : ℝ) * H ≤ t ∧ t < ((j : ℝ) + 3) * H)

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.MellinKernel ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate
noncomputable section
namespace MathCollab.Density
def mellinLine (w : ℝ → ℂ) (r : ℝ) : ℂ := mellin w ((1 : ℂ) + r * I)

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.BandEnergy ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
namespace MathCollab.Density
def mellinMass (w : ReflectionCutoff) : ℝ := ∫ r, ‖mellinLine (fun x => (w x : ℂ)) r‖

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.DyadicBlocks ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set
open scoped BigOperators
noncomputable section
namespace MathCollab.Density
def reflectionNatBand (L H : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌈4*H/(Real.pi*L)⌉₊).filter (fun m => inReflectionBand L H (m : ℤ))

def dyadicExponents (L H : ℝ) : Finset ℕ := (reflectionNatBand L H).image Nat.log2
def reflectionBlocks (L H : ℝ) : Finset ℕ := (dyadicExponents L H).image (fun j => 2^j)

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.ReflectionAssembly ====
public section
-- Reversible module-visibility port of the audited development.
-- BEGIN MODULE VISIBILITY
@[expose] public section
-- END MODULE VISIBILITY
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate
noncomputable section
namespace MathCollab.Density

def localReflectionEnergy (L H : ℝ) (U : Finset ℝ) : ℝ :=
  ∑ M ∈ reflectionBlocks L H, ∑' j : ℤ, completePairEnergy M (localSet U H j)

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.LargeValueDefinitions ====
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

axiom oneSeparated_subset {U W : Finset ℝ} (hW : oneSeparated W) (hU : U ⊆ W) : oneSeparated U
end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.Packing ====
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

axiom LargeValueData.local_card_le {κ : ℝ} (d : LargeValueData κ) {U : Finset ℝ}
    (hU : U ⊆ d.W) : (U.card : ℝ) ≤ localDiameter U ∧ localDiameter U ≤ d.T+1
end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.ReflectionApplication ====
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

/-- The uniform T-error bound is a consequence of the proved reflection theorem. -/
axiom uniform_reflection_application (w : ReflectionCutoff) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (T L H : ℝ) (U : Finset ℝ),
      2 ≤ T → T^(1/3 : ℝ) ≤ L → 0 < H → oneSeparated U → intervalSpan U ≤ T →
      shellEnergy w L H U ≤
        (20000/Real.pi^2)*(mellinMass w)^2*(L^2/H)*localReflectionEnergy L H U +
          E*T^(-100 : ℝ) ∧
      (∑ _t ∈ U, ‖hKernel w L 0‖^2) ≤ E*T^(-100 : ℝ)
end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.ComparisonCutoff ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.BootstrapDomain ====
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

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.BootstrapSupremum ====
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

axiom bootstrapBound_nonneg (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) : 0 ≤ bootstrapBound w d

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.Comparison ====
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

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.BootstrapShell ====
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

/-- Actual reflection and comparison feed the actual finite supremum; neither is a premise. -/
axiom bootstrap_one_shell (w : ComparisonCutoff) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      ∀ (U : Finset ℝ) (L H : ℝ), U ⊆ d.W → (d.N : ℝ) ≤ L → 1 ≤ H → H ≤ d.T →
      shellEnergy w.toReflectionCutoff L H U ≤
        C*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*H*U.card +
        C*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
          ((d.N : ℝ)^2*H+(d.N : ℝ)*L^2) + E*d.T^(-100 : ℝ)
end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Dependencies.v9379bd6576a4.MathCollab.Density.BootstrapShells ====
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
def shellIndices (U : Finset ℝ) : Finset ℕ :=
  (Finset.range (⌊intervalSpan U⌋₊.log2+1)).filter (fun k => (2 : ℝ)^k ≤ intervalSpan U)
axiom shellIndex_bounds {U : Finset ℝ} {k : ℕ} (hk : k ∈ shellIndices U) :
    1 ≤ (2 : ℝ)^k ∧ (2 : ℝ)^k ≤ intervalSpan U

axiom shellIndices_sum_le (U : Finset ℝ) :
    (∑ k ∈ shellIndices U, (2 : ℝ)^k) ≤ 2*localDiameter U
axiom shellIndices_card_le_log {U : Finset ℝ} {T : ℝ} (hT : 2 ≤ T)
    (hD : intervalSpan U ≤ T) :
    ((shellIndices U).card : ℝ) ≤ Real.log (2*T)/Real.log 2
axiom shellIndices_card_le_diameter (U : Finset ℝ) :
    ((shellIndices U).card : ℝ) ≤ localDiameter U

/-- Each off-diagonal pair lies in an actual dyadic shell with H at most its diameter. -/
axiom kernelEnergy_le_dyadic_shells (w : ReflectionCutoff) (L : ℝ)
    {U : Finset ℝ} (hsep : oneSeparated U) :
    kernelEnergy w L U ≤ (∑ _t ∈ U, ‖hKernel w L 0‖^2) +
      ∑ k ∈ shellIndices U, shellEnergy w L ((2 : ℝ)^k) U
end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_three_over_two_sigma_lean.Examples.Example_b1701f6e6cb92cb511b2_BootstrapAbsorption ====
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
theorem bootstrap_preabsorption (w : ComparisonCutoff) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      ∀ (U : Finset ℝ) (L : ℝ), U ⊆ d.W → (d.N : ℝ) ≤ L →
      kernelEnergy w.toReflectionCutoff L U ≤
        2*C*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*localDiameter U*U.card +
        C*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
          (2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*(Real.log (2*d.T)/Real.log 2)) +
        E*d.T^(-90 : ℝ) := by
  obtain ⟨C, E, hC, hE, hshell⟩ := bootstrap_one_shell w
  obtain ⟨F, hF, hdiag⟩ := uniform_reflection_application w.toReflectionCutoff
  refine ⟨C, 2*E+F, hC, by positivity, ?_⟩
  intro κ d hW U L hU hL
  let b := bootstrapScalar d.T d.N d.V
  let B := bootstrapBound w.toReflectionCutoff d
  have hb : 0 ≤ b := bootstrapScalar_nonneg d.T d.V d.N
  have hB : 0 ≤ B := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hT : 0 < d.T := by linarith [d.T_ge_two]
  have hT1 : 1 ≤ d.T := by linarith [d.T_ge_two]
  have hsep := oneSeparated_subset d.separated hU
  have hd : localDiameter U ≤ d.T+1 := (d.local_card_le hU).2
  have hdiam : intervalSpan U ≤ d.T := by dsimp [localDiameter] at hd; linarith
  have hQ := kernelEnergy_le_dyadic_shells w.toReflectionCutoff L hsep
  have hdi := (hdiag d.T L 1 U d.T_ge_two (d.scale_lower.trans hL) (by norm_num) hsep hdiam).2
  have hs : (∑ k ∈ shellIndices U, shellEnergy w.toReflectionCutoff L ((2 : ℝ)^k) U) ≤
      2*C*b*(d.N : ℝ)*localDiameter U*U.card +
      C*B*b^3*U.card*(2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*(Real.log (2*d.T)/Real.log 2)) +
      E*((shellIndices U).card : ℝ)*d.T^(-100 : ℝ) := by
    have hp := Finset.sum_le_sum (s := shellIndices U) (fun k hk =>
      hshell d hW U L ((2 : ℝ)^k) hU hL (shellIndex_bounds hk).1
        ((shellIndex_bounds hk).2.trans hdiam))
    have heq : (∑ k ∈ shellIndices U,
        (C*b*(d.N : ℝ)*(2 : ℝ)^k*U.card +
          C*B*b^3*U.card*((d.N : ℝ)^2*(2 : ℝ)^k+(d.N : ℝ)*L^2) + E*d.T^(-100 : ℝ))) =
        C*b*(d.N : ℝ)*U.card*(∑ k ∈ shellIndices U, (2 : ℝ)^k) +
          C*B*b^3*U.card*((d.N : ℝ)^2*(∑ k ∈ shellIndices U, (2 : ℝ)^k)+
            (d.N : ℝ)*L^2*(shellIndices U).card) + E*(shellIndices U).card*d.T^(-100 : ℝ) := by
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    change (∑ k ∈ shellIndices U, shellEnergy w.toReflectionCutoff L ((2 : ℝ)^k) U) ≤ _ at hp
    rw [heq] at hp
    have hsum := shellIndices_sum_le U
    have hcard := shellIndices_card_le_log d.T_ge_two hdiam
    have hlead := mul_le_mul_of_nonneg_left hsum (show 0 ≤ C*b*(d.N : ℝ)*U.card by positivity)
    have hrec := mul_le_mul_of_nonneg_left hsum (show 0 ≤ C*B*b^3*U.card*(d.N : ℝ)^2 by positivity)
    have hlog := mul_le_mul_of_nonneg_left hcard (show 0 ≤ C*B*b^3*U.card*(d.N : ℝ)*L^2 by positivity)
    nlinarith
  have hcardT : ((shellIndices U).card : ℝ) ≤ 2*d.T := (shellIndices_card_le_diameter U).trans (by linarith)
  have he : d.T*d.T^(-100 : ℝ) = d.T^(-99 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one d.T]
    rw [← Real.rpow_add hT]
    norm_num
  have hpow : d.T^(-99 : ℝ) ≤ d.T^(-90 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hpow' : d.T^(-100 : ℝ) ≤ d.T^(-90 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have herr₁ : E*((shellIndices U).card : ℝ)*d.T^(-100 : ℝ) ≤ 2*E*d.T^(-90 : ℝ) := by
    calc
      _ ≤ E*(2*d.T)*d.T^(-100 : ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardT hE) (Real.rpow_nonneg hT.le _)
      _ = 2*E*(d.T*d.T^(-100 : ℝ)) := by ring
      _ ≤ _ := by rw [he]; exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have herr₂ := mul_le_mul_of_nonneg_left hpow' hF
  dsimp [b, B] at hs
  linarith
end MathCollab.Density
