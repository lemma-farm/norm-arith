module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.vc4a3ed914428.FalconerThetaGauge.StationaryPhaseInverseOperatorsAction ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # Actual differential action and the inverse-operator cancellation identities -/
@[expose] public section
noncomputable section
open Finset Polynomial
open scoped ContDiff
namespace FalconerThetaGauge
/-- A polynomial acts as its literal finite constant-coefficient differential operator. -/
def polynomialDifferentialAction (p : Polynomial ℂ) (G : ℝ → ℂ) : ℝ → ℂ :=
  fun x => p.sum (fun n c => c * iteratedDeriv n G x)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.vc4a3ed914428.FalconerThetaGauge.RegularFunctions ====
public section
set_option autoImplicit false
/-!
# Explicit derivative bounds for smooth amplitudes

The global real-line version of Definition 3.1 applies to compactly supported
smooth amplitudes and to periodic lifts of circular amplitudes. The product
bound retains the sum of the two derivative scales exactly.
-/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge
/-- Uniform bounds on each actual iterated derivative up to the chosen order. -/
structure IsDerivativeRegular (A M : ℝ) (k : ℕ) (f : ℝ → ℂ) : Prop where
  amplitude_nonneg : 0 ≤ A
  one_le_scale : 1 ≤ M
  smooth : ContDiff ℝ k f
  bound : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j f x‖ ≤ A * M ^ j

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.vc4a3ed914428.FalconerThetaGauge.PolynomialWeightedNorm ====
public section
set_option autoImplicit false
/-! # Weighted coefficient norms of actual complex polynomials -/
@[expose] public section
noncomputable section
open Finset Polynomial
namespace FalconerThetaGauge
def polynomialWeightedNorm (p : Polynomial ℂ) (M : ℝ) : ℝ :=
  p.sum fun k a ↦ ‖a‖ * M ^ k

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_0b5c8471e4dcfa59fcf7_StationaryPhaseInverseOperatorsRegularity ====
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-! # Actual derivative regularity of the stationary and inverse operators -/
@[expose] public section
noncomputable section
open Finset Polynomial
open scoped ContDiff
namespace FalconerThetaGauge
set_option linter.unusedVariables false in
/-- Applying a polynomial of order `d` consumes exactly `d` input derivatives and
multiplies the amplitude bound by its literal weighted coefficient norm. -/
theorem polynomialDifferentialAction_isDerivativeRegular {G : ℝ → ℂ}
    {A M : ℝ} {K d : ℕ} (hG : IsDerivativeRegular A M (K + d) G)
    (p : Polynomial ℂ) (hp : p.natDegree ≤ d) 
    (h_FalconerThetaGauge_contDiff_polynomialDifferentialAction_of_natDegree_le : ∀ {G : ℝ → ℂ} {K d : ℕ},
      ContDiff ℝ (↑(K + d) : WithTop ℕ∞) G →
        ∀ (p : Polynomial ℂ),
          p.natDegree ≤ d →
            ContDiff ℝ (↑K : WithTop ℕ∞) (FalconerThetaGauge.polynomialDifferentialAction p G))
    (h_FalconerThetaGauge_polynomialWeightedNorm_nonneg : ∀ (p : Polynomial ℂ) {M : ℝ}, 0 ≤ M → 0 ≤ FalconerThetaGauge.polynomialWeightedNorm p M)
    (h_FalconerThetaGauge_iteratedDeriv_polynomialDifferentialAction_of_natDegree_le : ∀ {G : ℝ → ℂ} {K d : ℕ},
      ContDiff ℝ (↑(K + d) : WithTop ℕ∞) G →
        ∀ (p : Polynomial ℂ),
          p.natDegree ≤ d →
            ∀ {m : ℕ},
              m ≤ K →
                ∀ (x : ℝ),
                  iteratedDeriv m (FalconerThetaGauge.polynomialDifferentialAction p G) x =
                    ∑ n ∈ p.support, (p.coeff : ℕ → ℂ) n * iteratedDeriv (m + n) G x)
    :
    IsDerivativeRegular (A * polynomialWeightedNorm p M) M K
      (polynomialDifferentialAction p G) := by
  have hM : 0 ≤ M := by linarith [hG.one_le_scale]
  refine ⟨mul_nonneg hG.amplitude_nonneg (h_FalconerThetaGauge_polynomialWeightedNorm_nonneg p hM),
    hG.one_le_scale, h_FalconerThetaGauge_contDiff_polynomialDifferentialAction_of_natDegree_le hG.smooth p hp, ?_⟩
  intro m hm x
  rw [h_FalconerThetaGauge_iteratedDeriv_polynomialDifferentialAction_of_natDegree_le hG.smooth p hp hm]
  calc
    _ ≤ ∑ n ∈ p.support, ‖p.coeff n * iteratedDeriv (m + n) G x‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ p.support, ‖p.coeff n‖ * (A * M ^ (m + n)) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply hG.bound
      have hnd := (le_natDegree_of_mem_supp n hn).trans hp
      omega
    _ = (A * polynomialWeightedNorm p M) * M ^ m := by
      rw [polynomialWeightedNorm, Polynomial.sum_def, mul_sum, sum_mul]
      apply sum_congr rfl
      intro n _
      rw [pow_add]
      ring
end FalconerThetaGauge
