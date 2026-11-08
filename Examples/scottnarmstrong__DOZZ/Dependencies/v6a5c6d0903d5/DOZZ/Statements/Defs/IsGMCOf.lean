/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v6a5c6d0903d5.DOZZ.Statements.Defs.RegularizedGMC
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.IsGMCOf`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- `M` is the GMC `M_γ` of the field `X` ([KRV, (law)]): a finite random measure such that, for
some (hence, a.s., every) circle-average process `Xc` of `X`, `∫ f dM_r → ∫ f dM` in probability
as `r → ∞` for every bounded continuous `f` (convergence in probability in the weak topology).
The `∃` keeps the predicate non-vacuous. -/
def IsGMCOf {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (γ : ℝ)
    (M : Ω → Measure ℂ) : Prop :=
  (∀ ω, IsFiniteMeasure (M ω)) ∧
    ∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
      ∀ f : BoundedContinuousFunction ℂ ℝ,
        TendstoInMeasure P (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
          (fun ω => ∫ x, f x ∂M ω)
end DOZZ
