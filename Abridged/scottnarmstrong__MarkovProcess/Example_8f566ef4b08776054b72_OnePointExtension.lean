import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Convex.Combination
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactness.SigmaCompact

-- ==== Examples.scottnarmstrong__MarkovProcess.Examples.Example_8f566ef4b08776054b72_OnePointExtension ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# One-point extension of a positive `C₀` resolvent

A positive contractive resolvent on a locally compact Polish space generates a sub-Markov
semigroup. This file adjoins the genuine Alexandroff point at infinity, extends continuous
functions by splitting off their value there, and lets the generated semigroup evolve only the
part which vanishes at infinity. The resulting positive contractive resolvent has a conservative
Feller kernel semigroup, and the added point is absorbing.

Main results: `PositiveC0ContractiveResolvent.onePointResolvent`,
`PositiveC0ContractiveResolvent.onePointResolvent_operator`,
`PositiveC0ContractiveResolvent.isConservative_onePointKernelSemigroup`, and
`PositiveC0ContractiveResolvent.onePointKernelSemigroup_absorbing`.

This construction does not assert a Kolmogorov moment bound or construct a continuous-path
process.
-/
open Filter Set Topology TopologicalSpace
noncomputable section
namespace OnePoint
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]

end OnePoint
namespace MarkovProcess.PositiveC0ContractiveResolvent
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal ZeroAtInfty
variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X]
/-- The part of a function on the one-point compactification which vanishes at infinity. -/
noncomputable def onePointRemainder (g : C₀(OnePoint X, ℝ)) : C₀(X, ℝ) where
  toFun x := g (x : OnePoint X) - g OnePoint.infty
  continuous_toFun :=
    (g.continuous.comp OnePoint.continuous_coe).sub continuous_const
  zero_at_infty' := by
    have hg := (OnePoint.continuous_iff (g : OnePoint X → ℝ)).mp g.continuous
    rw [← Filter.coclosedCompact_eq_cocompact]
    simpa only [Function.comp_apply, sub_self] using hg.1.sub_const (g OnePoint.infty)

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
private theorem norm_onePointRemainder_le (g : C₀(OnePoint X, ℝ)) :
    ‖onePointRemainder g‖ ≤ 2 * ‖g‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  refine (BoundedContinuousFunction.norm_le (mul_nonneg (by norm_num) (norm_nonneg g))).2 fun x ↦ ?_
  change ‖g (x : OnePoint X) - g OnePoint.infty‖ ≤ 2 * ‖g‖
  calc
    ‖g (x : OnePoint X) - g OnePoint.infty‖ ≤
        ‖g (x : OnePoint X)‖ + ‖g OnePoint.infty‖ := norm_sub_le _ _
    _ ≤ ‖g‖ + ‖g‖ := add_le_add
      (g.toBCF.norm_coe_le_norm (x : OnePoint X))
      (g.toBCF.norm_coe_le_norm OnePoint.infty)
    _ = 2 * ‖g‖ := by ring
variable [MeasurableSpace X] [BorelSpace X]


end MarkovProcess.PositiveC0ContractiveResolvent
