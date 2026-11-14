module

public import Mathlib
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds
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
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v3175e2f543d7.MathCollab.Density.ReflectionDefinitions ====
public section
set_option autoImplicit false
@[expose] public section
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
namespace MathCollab.Density
/-- The manuscript's explicit Dirichlet phase, using the real logarithm. -/
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v3175e2f543d7.MathCollab.Density.MellinKernel ====
public section
set_option autoImplicit false
@[expose] public section
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate
noncomputable section
namespace MathCollab.Density
def mellinLine (w : ℝ → ℂ) (r : ℝ) : ℂ := mellin w ((1 : ℂ) + r * I)

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v3175e2f543d7.MathCollab.Density.BandEnergy ====
public section
set_option autoImplicit false
@[expose] public section
open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff
noncomputable section
namespace MathCollab.Density
def mellinMass (w : ReflectionCutoff) : ℝ := ∫ r, ‖mellinLine (fun x => (w x : ℂ)) r‖

end MathCollab.Density

end
end
end

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v3175e2f543d7.MathCollab.Density.DyadicBlocks ====
public section
set_option autoImplicit false
@[expose] public section
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.v3175e2f543d7.MathCollab.Density.ReflectionAssembly ====
public section
set_option autoImplicit false
@[expose] public section
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_56a0fa4083e8daac6537_CenteredDilatedReflection ====
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment


set_option linter.unusedVariables false in
theorem centered_shell_dilated_short_range (w : MathCollab.Density.ReflectionCutoff)
    {K A : ℕ} (hK : 1 ≤ K) (hA : 1 < A) {η D : ℝ} (hη : 0 < η) (hD : 1 ≤ D) 
    (h_Montgomery_RationalMoment_reflection_local_energy_dilated_short_range : ∀ {K : ℕ},
      1 ≤ K →
        ∀ {η B : ℝ},
          0 < η →
            1 ≤ B →
              ∃ (C : ℝ),
                0 < C ∧
                  ∀ (T t₀ L H : ℝ),
                    1 < T →
                      0 < L →
                        0 < H →
                          ∀ (W : Finset ℝ),
                            T ^ (((↑K : ℝ) + 1) / (2 * (↑K : ℝ) + 1)) ≤ (↑W.card : ℝ) →
                              (H / (B * L)) ^ K ≤ (↑W.card : ℝ) →
                                (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
                                  (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
                                    MathCollab.Density.localReflectionEnergy L H W ≤
                                      C * T ^ η * (H / L) * (↑W.card : ℝ) ^ 2)
    (h_MathCollab_Density_uniform_reflection : ∀ (w : MathCollab.Density.ReflectionCutoff) {A : ℕ},
      1 < A →
        ∃ (K : ℝ),
          0 ≤ K ∧
            ∀ (L H : ℝ) (U : Finset ℝ),
              0 < L →
                0 < H →
                  MathCollab.Density.shellEnergy w L H U ≤
                      20000 / Real.pi ^ 2 * MathCollab.Density.mellinMass w ^ 2 * (L ^ 2 / H) *
                          MathCollab.Density.localReflectionEnergy L H U +
                        4 * K ^ 2 * (↑U.card : ℝ) ^ 2 * L ^ (2 - 2 * (↑A : ℝ)) ∧
                    ∑ _t ∈ U, ‖MathCollab.Density.hKernel w L 0‖ ^ 2 ≤
                      K ^ 2 * (↑U.card : ℝ) * L ^ (2 - 2 * (↑A : ℝ)))
    :
    ∃ C B : ℝ, 0 < C ∧ 0 ≤ B ∧ ∀ T t₀ L H : ℝ,
      1 < T → 0 < L → 0 < H → ∀ W : Finset ℝ,
      T^(((K : ℝ)+1)/(2*K+1)) ≤ W.card →
      (H/(D*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.shellEnergy w L H W ≤
        C*T^η*L*(W.card : ℝ)^2 + B*(W.card : ℝ)^2*L^(2-2*(A:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := h_Montgomery_RationalMoment_reflection_local_energy_dilated_short_range hK hη hD
  obtain ⟨B,hB,href⟩ := h_MathCollab_Density_uniform_reflection w hA
  let F : ℝ := (20000/Real.pi^2)*(MathCollab.Density.mellinMass w)^2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨1+F*C,4*B^2,by positivity,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  have he := (href L H W hL hH).1
  have hb := hbound T t₀ L H hT hL hH W hR hlen hW hsep
  have hm : F*(L^2/H)*MathCollab.Density.localReflectionEnergy L H W ≤
      (F*C)*T^η*L*(W.card : ℝ)^2 := by
    calc
      _ ≤ F*(L^2/H)*(C*T^η*(H/L)*(W.card : ℝ)^2) := by gcongr
      _ = _ := by field_simp
  exact he.trans (add_le_add (hm.trans (by gcongr; linarith)) le_rfl)
end Montgomery.RationalMoment
