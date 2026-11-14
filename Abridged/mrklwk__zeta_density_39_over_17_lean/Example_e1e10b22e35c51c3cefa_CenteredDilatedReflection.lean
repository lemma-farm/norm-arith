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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.ve7a08bec4446.MathCollab.Density.ReflectionDefinitions ====
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

def dyadicPolynomial (M : ℕ) (v : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ico M (2 * M), dirichletPhase ((q : ℝ) / M) v
def completePairEnergy (M : ℕ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, ‖dyadicPolynomial M (t - u)‖ ^ 2

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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.ve7a08bec4446.MathCollab.Density.DyadicBlocks ====
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Dependencies.ve7a08bec4446.MathCollab.Density.ReflectionAssembly ====
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

-- ==== Examples.mrklwk__zeta_density_39_over_17_lean.Examples.Example_e1e10b22e35c51c3cefa_CenteredDilatedReflection ====
set_option autoImplicit false
@[expose] public section
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
namespace Montgomery.RationalMoment

set_option linter.unusedVariables false in
/-- Fixed dilations in the reflected band are absorbed in the constant,
not imposed on the cardinality threshold. -/
theorem reflection_local_energy_dilated_short_range {K : ℕ} (hK : 1 ≤ K)
    {η B : ℝ} (hη : 0 < η) (hB : 1 ≤ B) 
    (h_Montgomery_RationalMoment_reflection_complete_pair_dilated_short_range : ∀ {K : ℕ},
      1 ≤ K →
        ∀ {η B : ℝ},
          0 < η →
            1 ≤ B →
              ∃ (C : ℝ),
                0 < C ∧
                  ∀ (T t₀ : ℝ),
                    1 < T →
                      ∀ (M : ℕ),
                        0 < M →
                          ∀ (U : ℝ),
                            0 ≤ U →
                              (↑M : ℝ) ≤ B * U →
                                ∀ (W : Finset ℝ),
                                  T ^ (((↑K : ℝ) + 1) / (2 * (↑K : ℝ) + 1)) ≤ (↑W.card : ℝ) →
                                    U ^ K ≤ (↑W.card : ℝ) →
                                      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀ + T)) →
                                        (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t - u|) →
                                          MathCollab.Density.completePairEnergy M W ≤
                                            C * T ^ η * U * (↑W.card : ℝ) ^ 2)
    (h_MathCollab_Density_reflectionBlocks_card_le : ∀ {L H : ℝ}, 0 < L → 0 < H → (MathCollab.Density.reflectionBlocks L H).card ≤ 10)
    (h_MathCollab_Density_reflectionBlock_scale_bounds : ∀ {L H : ℝ},
      0 < L →
        0 < H →
          ∀ {M : ℕ},
            M ∈ MathCollab.Density.reflectionBlocks L H →
              0 < M ∧ H / (40 * Real.pi * L) ≤ (↑M : ℝ) ∧ (↑M : ℝ) ≤ 4 * H / (Real.pi * L))
    (h_Montgomery_RationalMoment_reflection_local_pair_le_three : ∀ {H : ℝ},
      0 < H →
        ∀ (M : ℕ) (W : Finset ℝ),
          ∑' (j : ℤ), MathCollab.Density.completePairEnergy M (MathCollab.Density.localSet W H j) ≤
            3 * MathCollab.Density.completePairEnergy M W)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ T t₀ L H : ℝ, 1 < T → 0 < L → 0 < H →
      ∀ W : Finset ℝ,
      T^(((K:ℝ)+1)/(2*K+1)) ≤ W.card → (H/(B*L))^K ≤ W.card →
      (∀ t ∈ W, t ∈ Set.Icc t₀ (t₀+T)) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      MathCollab.Density.localReflectionEnergy L H W ≤
        C*T^η*(H/L)*(W.card:ℝ)^2 := by
  obtain ⟨C,hC,hbound⟩ := h_Montgomery_RationalMoment_reflection_complete_pair_dilated_short_range hK hη
    (B := 2*B) (by linarith)
  have hBp : 0 < B := by linarith
  refine ⟨30*C,by positivity,?_⟩
  intro T t₀ L H hT hL hH W hR hlen hW hsep
  let U : ℝ := H/(B*L)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hUL : U ≤ H/L := by
    dsimp [U]
    exact div_le_div_of_nonneg_left hH.le hL (by nlinarith)
  open MathCollab.Density in
  have hb (M : ℕ) (hM : M ∈ reflectionBlocks L H) :
      (∑' j : ℤ, completePairEnergy M (localSet W H j)) ≤
        3*(C*T^η*(H/L)*(W.card:ℝ)^2) := by
    obtain ⟨hM0,_,hMhi⟩ := h_MathCollab_Density_reflectionBlock_scale_bounds hL hH hM
    have hMU : (M:ℝ) ≤ (2*B)*U := by
      have hpi : 4*H/(Real.pi*L) ≤ 2*H/L := by
        apply (div_le_div_iff₀ (by positivity : 0 < Real.pi*L) hL).mpr
        nlinarith [Real.pi_gt_three,mul_pos hH hL]
      have he : (2*B)*U=2*H/L := by dsimp [U]; field_simp
      rw [he]
      exact hMhi.trans hpi
    refine (h_Montgomery_RationalMoment_reflection_local_pair_le_three hH M W).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3)
    exact (hbound T t₀ hT M hM0 U hU hMU W hR hlen hW hsep).trans (by gcongr)
  open MathCollab.Density in
  calc
    localReflectionEnergy L H W ≤ ∑ _M ∈ reflectionBlocks L H,
        3*(C*T^η*(H/L)*(W.card:ℝ)^2) := sum_le_sum hb
    _ = ((reflectionBlocks L H).card:ℝ)*(3*(C*T^η*(H/L)*(W.card:ℝ)^2)) := by simp
    _ ≤ 10*(3*(C*T^η*(H/L)*(W.card:ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast h_MathCollab_Density_reflectionBlocks_card_le hL hH
    _ = _ := by ring

end Montgomery.RationalMoment
