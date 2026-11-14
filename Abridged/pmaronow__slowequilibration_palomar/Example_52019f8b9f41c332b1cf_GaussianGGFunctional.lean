module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Topology.Order.ProjIcc

-- ==== Examples.pmaronow__slowequilibration_palomar.Dependencies.v5ab068cefed0.SlowEquilibration.GaussianGGPolynomialTests ====
public section
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! True finite polynomial extension of continuous GG tests. The
normalized GG discrepancy is a linear functional on continuous overlap
tests with norm at most two. Its finite power-test defects, together with
genuine uniform polynomial approximation, bound every predetermined
negative cutoff. No indicator GG identity is a premise. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGPolynomialTests
open Set MeasureTheory

open scoped Topology BigOperators
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Tests := C(Icc (-1:ℝ) 1,ℝ)

end SlowEquilibration.GaussianGGPolynomialTests

end
end
end

-- ==== Examples.pmaronow__slowequilibration_palomar.Dependencies.v5ab068cefed0.SlowEquilibration.GaussianGGIndicatorTransfer ====
public section
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! Ordinary-measure GG discrepancies and negative-indicator transfer.
The overlap marginals are genuine `HasLaw` statements. The discrepancy
is constructed from the actual replica expectations; its norm bound is
proved from probability and boundedness, not supplied as an operator
assumption. Continuous cutoffs approximate their negative steps through
actual pair-law shell mass. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGIndicatorTransfer
open MeasureTheory ProbabilityTheory Set
open  GaussianGGPolynomialTests
open scoped Topology BigOperators
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type*} [MeasurableSpace Ω]
/-- The literal normalized GG discrepancy with m old neighbors and one
fresh neighbor, hence m+1 replicas in the original bounded observable. -/
def discrepancy (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ) (ψ : ℝ → ℝ) : ℝ :=
  (∫ ω, f ω * ψ (R ω) ∂μ) -
    (∫ ω, f ω ∂μ) * (∫ r, ψ r ∂ρ) / ((m:ℝ)+1) -
    (∑ j : Fin m, ∫ ω, f ω * ψ (Q j ω) ∂μ) / ((m:ℝ)+1)

set_option linter.unusedVariables false in
axiom _root_.SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy_add.{w_u_1} : ∀ {Ω : Type w_u_1} [inst : MeasurableSpace Ω] (m : ℕ) (μ : MeasureTheory.Measure Ω)
  (ρ : MeasureTheory.Measure ℝ) (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ),
  MeasureTheory.AEStronglyMeasurable f μ →
    (∀ᵐ (ω : Ω) ∂μ, |f ω| ≤ 1) →
      ProbabilityTheory.HasLaw R ρ μ →
        (∀ (j : Fin m), ProbabilityTheory.HasLaw (Q j) ρ μ) →
          ∀ {ψ χ : ℝ → ℝ},
            MeasureTheory.Integrable ψ ρ →
              MeasureTheory.Integrable χ ρ →
                (SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy m μ ρ f R Q fun (r : ℝ) ↦
                    ψ r + χ r) =
                  SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy m μ ρ f R Q ψ +
                    SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy m μ ρ f R Q χ
set_option linter.unusedVariables false in
axiom _root_.SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy_smul.{w_u_1} : ∀ {Ω : Type w_u_1} [inst : MeasurableSpace Ω] (m : ℕ) (μ : MeasureTheory.Measure Ω)
  (ρ : MeasureTheory.Measure ℝ) (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ) (ψ : ℝ → ℝ) (c : ℝ),
  (SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy m μ ρ f R Q fun (r : ℝ) ↦ c * ψ r) =
    c * SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy m μ ρ f R Q ψ

end SlowEquilibration.GaussianGGIndicatorTransfer

end
end
end

-- ==== Examples.pmaronow__slowequilibration_palomar.Examples.Example_52019f8b9f41c332b1cf_GaussianGGFunctional ====
-- SPDX-License-Identifier: Apache-2.0
set_option autoImplicit false
/-! The GG continuous linear functional constructed from literal ordinary
probability expectations. Projection onto [-1,1] is only a total-function
extension of a continuous test; all applications to true overlaps are
proved equal to the original tests through their actual supported law. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianGGIndicatorTransfer
open MeasureTheory ProbabilityTheory Set
open  GaussianGGPolynomialTests
open scoped Topology BigOperators
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Ω : Type*} [MeasurableSpace Ω]
/-- Continuous extension of a test, agreeing with it on the actual
physical overlap interval. -/
def extendTest (ψ : Tests) (r : ℝ) : ℝ := ψ (projIcc (-1:ℝ) 1 (by norm_num) r)

set_option linter.unusedVariables false in
axiom _root_.SlowEquilibration.GaussianGGIndicatorTransfer.extendTest_integrable : ∀ (ρ : MeasureTheory.Measure ℝ) [MeasureTheory.IsProbabilityMeasure ρ]
  (ψ : SlowEquilibration.GaussianGGPolynomialTests.Tests),
  MeasureTheory.Integrable (SlowEquilibration.GaussianGGIndicatorTransfer.extendTest ψ) ρ

def discrepancyLinearMap (m : ℕ) (μ : Measure Ω) (ρ : Measure ℝ)
    [IsProbabilityMeasure ρ] (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) : Tests →ₗ[ℝ] ℝ where
  toFun ψ := discrepancy m μ ρ f R Q (extendTest ψ)
  map_add' ψ χ := by
    change discrepancy m μ ρ f R Q (fun r => extendTest ψ r+extendTest χ r)=_
    exact discrepancy_add m μ ρ f R Q hf hb hR hQ
      (extendTest_integrable ρ ψ) (extendTest_integrable ρ χ)
  map_smul' c ψ := by
    change discrepancy m μ ρ f R Q (fun r => c*extendTest ψ r)=
      c*discrepancy m μ ρ f R Q (extendTest ψ)
    exact discrepancy_smul m μ ρ f R Q (extendTest ψ) c
set_option linter.unusedVariables false in
theorem discrepancyLinearMap_bound (m : ℕ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (f R : Ω → ℝ) (Q : Fin m → Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, |f ω| ≤ 1)
    (hR : HasLaw R ρ μ) (hQ : ∀j, HasLaw (Q j) ρ μ) (ψ : Tests) 
    (h_SlowEquilibration_GaussianGGIndicatorTransfer_extendTest_norm_le : ∀ (ψ : SlowEquilibration.GaussianGGPolynomialTests.Tests) (r : ℝ),
      ‖SlowEquilibration.GaussianGGIndicatorTransfer.extendTest ψ r‖ ≤ ‖ψ‖)
    (h_SlowEquilibration_GaussianGGIndicatorTransfer_discrepancy_abs_le_l1 : ∀ {Ω : Type u_1} [inst : MeasurableSpace Ω] (m : ℕ) (μ : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure μ] (ρ : MeasureTheory.Measure ℝ) (f R : Ω → ℝ)
      (Q : Fin m → Ω → ℝ),
      MeasureTheory.AEStronglyMeasurable f μ →
        (∀ᵐ (ω : Ω) ∂μ, |f ω| ≤ 1) →
          ProbabilityTheory.HasLaw R ρ μ →
            (∀ (j : Fin m), ProbabilityTheory.HasLaw (Q j) ρ μ) →
              ∀ {ψ : ℝ → ℝ},
                MeasureTheory.Integrable ψ ρ →
                  |SlowEquilibration.GaussianGGIndicatorTransfer.discrepancy m μ ρ f R Q ψ| ≤
                    2 * ∫ (r : ℝ), |ψ r| ∂ρ)
    :
    ‖discrepancyLinearMap m μ ρ f R Q hf hb hR hQ ψ‖ ≤ 2*‖ψ‖ := by
  have hL : (∫r, |extendTest ψ r| ∂ρ) ≤ ‖ψ‖ := by
    have h := integral_mono_ae (extendTest_integrable ρ ψ).abs (integrable_const ‖ψ‖)
      (.of_forall fun r => by simpa only [Real.norm_eq_abs] using h_SlowEquilibration_GaussianGGIndicatorTransfer_extendTest_norm_le ψ r)
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h
  change |discrepancy m μ ρ f R Q (extendTest ψ)| ≤ 2*‖ψ‖
  exact (h_SlowEquilibration_GaussianGGIndicatorTransfer_discrepancy_abs_le_l1 m μ ρ f R Q hf hb hR hQ
    (extendTest_integrable ρ ψ)).trans (mul_le_mul_of_nonneg_left hL (by norm_num))

end SlowEquilibration.GaussianGGIndicatorTransfer
