module

public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- ==== Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.CriticalEndpoint ====
public section
set_option autoImplicit false
public section
/-!
# Transition-point algebra and scalar exclusion

These are the algebraic conclusions used in the revised manuscript's Section 8
and the parameter estimates in Section 16. They do not assert existence or
convergence of a CK solution. In particular, `zero_plateau_excluded` takes the
strict scalar sign property as a named analytic hypothesis; obtaining this
property from the CK equations belongs to Section 6.
-/
namespace SphericalAging.CriticalEndpoint
noncomputable section
@[expose] def relaxationParameter (p : ℕ) (q : ℝ) : ℝ :=
  ((p : ℝ) - 2) * (1 - q) / (2 * q)
@[expose] noncomputable def exponentCoefficient (a : ℝ) : ℝ :=
  Real.Gamma (1 - a) ^ 2 / Real.Gamma (1 - 2 * a)

end
end SphericalAging.CriticalEndpoint

end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.StationaryNormalization ====
public section
set_option autoImplicit false
public section
/-!
# Normalizing the stationary scalar equation

This file proves the change of time and profile in Lemma 16.3 of the manuscript.
The hypotheses below are the actual stationary-profile facts used in that lemma:
continuous differentiability, `c' = -r`, `c(0)=1`, the scalar memory equation,
and the plateau identity. They are not assertions that the normalized equation
already holds. Derivatives at zero are derivatives within the nonnegative ray.
-/
open MeasureTheory Set
open scoped Topology
namespace SphericalAging.StationaryNormalization
noncomputable section

/-- Causal convolution on the nonnegative time ray. -/
@[expose] def causalConvolution (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in 0..t, f (t - s) * g s

end
end SphericalAging.StationaryNormalization

end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.StationaryPowerProfiles ====
public section
set_option autoImplicit false
public section
/-!
# The actual shifted-power comparison profiles

The corrected powers and all derivatives below are actual real functions.
The Gamma quotient estimate is derived from the proved strict digamma theorem.
-/
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace SphericalAging.StationaryPowerProfiles
noncomputable section
@[expose] def shiftedPower (a t : ℝ) : ℝ := (1 + t) ^ (-a)

end
end SphericalAging.StationaryPowerProfiles

end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.StationaryBetaConvolution ====
public section
set_option autoImplicit false
public section
/-! Exact real beta-integral formula for the actual shifted-power convolution. -/
open Set MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryBetaConvolution
noncomputable section
open StationaryPowerProfiles StationaryNormalization
@[expose] def betaKernel (α ζ y : ℝ) : ℝ := y ^ (-α) * (1 - y) ^ (-ζ)
@[expose] def truncatedBeta (α ζ x : ℝ) : ℝ := ∫ y in x..(1 - x), betaKernel α ζ y

end
end SphericalAging.StationaryBetaConvolution

end
end

-- ==== Examples.pmaronow__aging_palomar.Dependencies.vc0770c57311b.SphericalAging.StationaryShiftedResidual ====
public section
set_option autoImplicit false
public section
/-! Positivity of the actual critical shifted-power quadratic residual. -/
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.StationaryShiftedResidual
noncomputable section
open StationaryPowerProfiles StationaryBetaConvolution StationaryNormalization
@[expose] def J (a x : ℝ) : ℝ := (1 - 2 * a) * truncatedBeta a a x + 2 * x * betaKernel a a x

@[expose] def quadraticResidual (a t : ℝ) : ℝ :=
  deriv (causalConvolution (shiftedPower a) (shiftedPower a)) t -
    CriticalEndpoint.exponentCoefficient a * shiftedPower a t ^ 2

end
end SphericalAging.StationaryShiftedResidual

end
end

-- ==== Examples.pmaronow__aging_palomar.Examples.Example_95339e7fe22936d33795_StationaryQuadraticDecay ====
set_option autoImplicit false
public section
/-! Quantitative decay of the actual positive shifted-power residual. -/
open Set MeasureTheory Filter Asymptotics
open scoped Topology
namespace SphericalAging.StationaryQuadraticDecay
noncomputable section
open StationaryPowerProfiles StationaryBetaConvolution StationaryNormalization StationaryShiftedResidual

set_option linter.unusedVariables false in
/-- Positivity allows dropping both negative terms in the exact quadratic
balance, giving a global quantitative estimate without a beta-tail asymptotic. -/
theorem quadraticResidual_global_bound (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) 
    (h_SphericalAging_CriticalEndpoint_beta_gamma_balance : ∀ a < 1 / 2,
      (1 - 2 * a) * ProbabilityTheory.beta (1 - a) (1 - a) =
        SphericalAging.CriticalEndpoint.exponentCoefficient a)
    (h_SphericalAging_CriticalEndpoint_exponentCoefficient_pos : ∀ a < 1 / 2, 0 < SphericalAging.CriticalEndpoint.exponentCoefficient a)
    (h_SphericalAging_StationaryShiftedResidual_symmetric_kernel : ∀ (a x : ℝ),
      SphericalAging.StationaryBetaConvolution.betaKernel a a (1 - x) =
        SphericalAging.StationaryBetaConvolution.betaKernel a a x)
    (h_SphericalAging_StationaryShiftedResidual_quadraticResidual_pos : ∀ (a t : ℝ),
      0 < a → a < 1 / 2 → 0 ≤ t → 0 < SphericalAging.StationaryShiftedResidual.quadraticResidual a t)
    (h_SphericalAging_StationaryBetaConvolution_shifted_convolution_hasDerivAt : ∀ (α ζ t : ℝ),
      -1 < t →
        HasDerivAt
          (SphericalAging.StationaryNormalization.causalConvolution
            (SphericalAging.StationaryPowerProfiles.shiftedPower α)
            (SphericalAging.StationaryPowerProfiles.shiftedPower ζ))
          ((t + 2) ^ (-α - ζ) *
            ((1 - α - ζ) * SphericalAging.StationaryBetaConvolution.truncatedBeta α ζ (1 / (t + 2)) +
                1 / (t + 2) * SphericalAging.StationaryBetaConvolution.betaKernel α ζ (1 / (t + 2)) +
              1 / (t + 2) * SphericalAging.StationaryBetaConvolution.betaKernel α ζ (1 - 1 / (t + 2))))
          t)
    (h_SphericalAging_StationaryQuadraticDecay_truncatedBeta_le_complete : ∀ (a x : ℝ),
      a < 1 →
        0 ≤ x →
          x ≤ 1 / 2 →
            SphericalAging.StationaryBetaConvolution.truncatedBeta a a x ≤
              ProbabilityTheory.beta (1 - a) (1 - a))
    (h_SphericalAging_StationaryShiftedResidual_boundary_kernel_power : ∀ (a x : ℝ),
      a < 1 →
        0 ≤ x →
          x < 1 →
            x * SphericalAging.StationaryBetaConvolution.betaKernel a a x = x ^ (1 - a) * (1 - x) ^ (-a))
    :
    ∀ t ≥ 0, |quadraticResidual a t| ≤
      (2 * (1 / 2 : ℝ) ^ (-a)) * (1 + t) ^ (-a - 1) := by
  intro t ht
  let T := t + 2
  let x := 1 / T
  let θ := CriticalEndpoint.exponentCoefficient a
  have hT : 0 < T := by dsimp [T]; linarith
  have hx0 : 0 < x := one_div_pos.mpr hT
  have hxhalf : x ≤ 1 / 2 := one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ) < 2) (by dsimp [T]; linarith)
  have hx1 : x < 1 := by linarith
  have hTp := Real.rpow_pos_of_pos hT (-2 * a)
  have hθ : 0 < θ := h_SphericalAging_CriticalEndpoint_exponentCoefficient_pos a ha1
  have hB := h_SphericalAging_StationaryQuadraticDecay_truncatedBeta_le_complete a x (by linarith) hx0.le hxhalf
  have hBJ := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ 1 - 2 * a)
  rw [h_SphericalAging_CriticalEndpoint_beta_gamma_balance a ha1] at hBJ
  have hJ : J a x ≤ θ + 2 * x * betaKernel a a x := by
    unfold J
    dsimp [θ]
    linarith
  have hderiv : deriv (causalConvolution (shiftedPower a) (shiftedPower a)) t =
      T ^ (-2 * a) * J a x := by
    rw [(h_SphericalAging_StationaryBetaConvolution_shifted_convolution_hasDerivAt a a t (by linarith)).deriv]
    change T ^ (-a - a) * ((1 - a - a) * truncatedBeta a a x +
      x * betaKernel a a x + x * betaKernel a a (1 - x)) = T ^ (-2 * a) * J a x
    rw [h_SphericalAging_StationaryShiftedResidual_symmetric_kernel, show -a - a = -2 * a by ring]
    unfold J
    ring
  have hgpow : shiftedPower a t ^ 2 = (1 + t) ^ (-2 * a) := by
    unfold shiftedPower
    rw [← Real.rpow_mul_natCast (show 0 ≤ 1 + t by linarith) (-a) 2]
    congr 1
    norm_num
    ring
  have hgsq : T ^ (-2 * a) ≤ shiftedPower a t ^ 2 := by
    rw [hgpow]
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by dsimp [T]; linarith) (by linarith)
  have hDbound : quadraticResidual a t ≤ 2 * T ^ (-2 * a) * (x * betaKernel a a x) := by
    have hderivb := mul_le_mul_of_nonneg_left hJ hTp.le
    have hθb := mul_le_mul_of_nonneg_left hgsq hθ.le
    unfold quadraticResidual
    rw [hderiv]
    dsimp [θ] at hderivb hθb
    nlinarith
  have hboundary := h_SphericalAging_StationaryShiftedResidual_boundary_kernel_power a x (by linarith) hx0.le hx1
  have h1power : (1 - x) ^ (-a) ≤ (1 / 2 : ℝ) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have hboundaryb : x * betaKernel a a x ≤ x ^ (1 - a) * (1 / 2 : ℝ) ^ (-a) := by
    rw [hboundary]
    exact mul_le_mul_of_nonneg_left h1power (Real.rpow_pos_of_pos hx0 _).le
  have hp : T ^ (-2 * a) * x ^ (1 - a) = T ^ (-a - 1) := by
    dsimp [x]
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow T (1 - a), ← Real.rpow_add hT]
    congr 1
    ring
  have hlag : T ^ (-a - 1) ≤ (1 + t) ^ (-a - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by dsimp [T]; linarith) (by linarith)
  rw [abs_of_pos (h_SphericalAging_StationaryShiftedResidual_quadraticResidual_pos a t ha0 ha1 ht)]
  calc
    quadraticResidual a t ≤ 2 * T ^ (-2 * a) * (x * betaKernel a a x) := hDbound
    _ ≤ 2 * T ^ (-2 * a) * (x ^ (1 - a) * (1 / 2 : ℝ) ^ (-a)) :=
      mul_le_mul_of_nonneg_left hboundaryb (by positivity)
    _ = (2 * (1 / 2 : ℝ) ^ (-a)) * T ^ (-a - 1) := by
      rw [← hp]
      ring
    _ ≤ (2 * (1 / 2 : ℝ) ^ (-a)) * (1 + t) ^ (-a - 1) :=
      mul_le_mul_of_nonneg_left hlag (by positivity)
end
end SphericalAging.StationaryQuadraticDecay
