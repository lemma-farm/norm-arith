module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Tactic
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.vd30ac82f190d.Paper.Hyperbolic ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Hyperbolic identities and pointwise inequalities

The pointwise analytic ingredients of arXiv:2604.11921v2, Sections 3 and 4.
All hyperbolic functions are the actual real functions from mathlib.
-/
namespace Paper
noncomputable def sech (x : ℝ) : ℝ := 1 / Real.cosh x

end Paper

end
end

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.vd30ac82f190d.Paper.Gaussian ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Concrete Gaussian quantities

The expectations in the paper are Bochner integrals against mathlib's standard
Gaussian probability measure. We keep `q` explicit; existence and uniqueness of
the fixed point are proved separately in `FixedPointUnique.lean`.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
noncomputable def gaussianExpectation (f : ℝ → ℝ) : ℝ :=
  ∫ z, f z ∂gaussianReal 0 1
noncomputable def gaussianField (β h q z : ℝ) : ℝ := β * Real.sqrt q * z + h
noncomputable def overlapMap (β h q : ℝ) : ℝ :=
  gaussianExpectation (fun z => Real.tanh (gaussianField β h q z) ^ 2)

 
 
 
 
 
 
 

 
 
 
 
 
 
 

 
 
end Paper

end
end

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.vd30ac82f190d.Paper.DoobKernel ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# The Gaussian cosh transform in Proposition 5.4

The analytic Gaussian operator below is a positive operator preserving the
constant one. This file does not identify it with an SDE transition law;
that identification requires the separate backward-equation and Markov
arguments in the paper.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper

/-- The Gaussian form of the paper's cosh Doob transform. -/
def doobOperator (v : ℝ≥0) (ψ : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(v : ℝ) / 2) / Real.cosh x *
    ∫ y, Real.cosh y * ψ y ∂gaussianReal x v

end Paper

end
end
end

-- ==== Examples.pmaronow__frsb_palomar.Dependencies.vd30ac82f190d.Paper.MomentBridge ====
public section
set_option autoImplicit false
@[expose] public section
/-!
# Analytic Doob moments and the conditional right-hand bound

The moments in this file are literal Gaussian integrals of the proven positive,
normalized Gaussian Doob operator. Their initial values, moment comparison,
and exponential decay are proved. Transition-law identification with the
paper's diffusion and the Itô derivative identity remain explicit hypotheses.
This file does not assert Proposition 5.1 or identify an SDE solution.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper
/-- The Gaussian average of the actual Doob transform of squared `tanh`. -/
def gaussianDoobSecondMoment (β h q : ℝ) (lam : ℝ≥0) : ℝ :=
  ∫ x, doobOperator lam (fun y => Real.tanh y ^ 2) x
    ∂gaussianReal h (β ^ 2 * q).toNNReal
/-- The Gaussian average of the actual Doob transform of fourth-power `sech`. -/
def gaussianDoobFourthMoment (β h q : ℝ) (lam : ℝ≥0) : ℝ :=
  ∫ x, doobOperator lam (fun y => sech y ^ 4) x
    ∂gaussianReal h (β ^ 2 * q).toNNReal
/-- The actual analytic second moment at time `t`, with time rescaling by `β²`.
The nonnegative-real truncation is inactive whenever `t ≥ q`. -/
def hardSecondMoment (β h q t : ℝ) : ℝ :=
  gaussianDoobSecondMoment β h q (β ^ 2 * (t - q)).toNNReal
/-- The actual analytic fourth-sech moment at time `t`. -/
def hardFourthMoment (β h q t : ℝ) : ℝ :=
  gaussianDoobFourthMoment β h q (β ^ 2 * (t - q)).toNNReal

end Paper

end
end
end

-- ==== Examples.pmaronow__frsb_palomar.Examples.Example_974d08efd04516f61e25_StrictRSMoments ====
set_option autoImplicit false
@[expose] public section
/-!
# Strict post-interface moment and variational inequalities

Positivity of the actual Doob fourth moment makes the second moment strictly
increasing. In the small-variance regime this turns the comparison derivative
bound into a strict bound. The existing exponential estimate handles the
remaining regime, so strictness holds under the original fixed-point and AT
assumptions without an additional small-field hypothesis.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Paper


set_option linter.unusedVariables false in
/-- Strict comparison in the small-variance regime, including its equality boundary. -/
theorem hardSecondMoment_lt_time_of_small_variance {β h q : ℝ}
    (hβ : 0 < β) (hq : q ∈ Icc (0 : ℝ) 1)
    (hfixed : q = overlapMap β h q) (hsmall : β ^ 2 * (1 - q) ≤ 1) 
    (h_Paper_hardSecondMoment_initial_fixed : ∀ {β h q : ℝ}, 0 ≤ q → q = Paper.overlapMap β h q → Paper.hardSecondMoment β h q q = q)
    (h_Paper_hasDerivAt_hardSecondMoment : ∀ (β h q : ℝ) {t : ℝ},
      q < t → HasDerivAt (Paper.hardSecondMoment β h q) (β ^ 2 * Paper.hardFourthMoment β h q t) t)
    (h_Paper_strictMonoOn_hardSecondMoment : ∀ {β : ℝ}, 0 < β → ∀ (h q : ℝ), StrictMonoOn (Paper.hardSecondMoment β h q) (Set.Icc q 1))
    (h_Paper_gaussianDoobFourthMoment_le_one_sub_second : ∀ (β h q : ℝ) (lam : NNReal),
      Paper.gaussianDoobFourthMoment β h q lam ≤ 1 - Paper.gaussianDoobSecondMoment β h q lam)
    (h_Paper_deriv_hardSecondMoment : ∀ (β h q : ℝ) {t : ℝ},
      q < t → deriv (Paper.hardSecondMoment β h q) t = β ^ 2 * Paper.hardFourthMoment β h q t)
    (h_Paper_continuous_hardSecondMoment : ∀ (β h q : ℝ), Continuous (Paper.hardSecondMoment β h q))
    :
    ∀ t ∈ Ioc q (1 : ℝ), hardSecondMoment β h q t < t := by
  have hfix := h_Paper_hardSecondMoment_initial_fixed hq.1 hfixed
  have hm := h_Paper_strictMonoOn_hardSecondMoment hβ h q
  have hd : DifferentiableOn ℝ (hardSecondMoment β h q) (interior (Icc q (1 : ℝ))) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (h_Paper_hasDerivAt_hardSecondMoment β h q ht.1).differentiableAt.differentiableWithinAt
  have hb : ∀ t ∈ interior (Icc q (1 : ℝ)), deriv (hardSecondMoment β h q) t < 1 := by
    intro t ht
    rw [interior_Icc] at ht
    have hqt : q < hardSecondMoment β h q t := by
      have hi := hm ⟨le_rfl, hq.2⟩ ⟨ht.1.le, ht.2.le⟩ ht.1
      simpa only [hfix] using hi
    rw [h_Paper_deriv_hardSecondMoment β h q ht.1]
    have hbound := mul_le_mul_of_nonneg_left
      (h_Paper_gaussianDoobFourthMoment_le_one_sub_second β h q
        (β ^ 2 * (t - q)).toNNReal) (sq_nonneg β)
    change β ^ 2 * hardFourthMoment β h q t ≤
      β ^ 2 * (1 - hardSecondMoment β h q t) at hbound
    exact hbound.trans_lt ((mul_lt_mul_of_pos_left (by linarith) (sq_pos_of_pos hβ)).trans_le hsmall)
  intro t ht
  have he := (convex_Icc q (1 : ℝ)).image_sub_lt_mul_sub_of_deriv_lt
    (h_Paper_continuous_hardSecondMoment β h q).continuousOn hd hb
    q ⟨le_rfl, hq.2⟩ t ⟨ht.1.le, ht.2⟩ ht.1
  rw [hfix] at he
  linarith
end Paper
