/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.scottnarmstrong__DOZZ.Dependencies.v3cf0cc9f30c6.DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The definition `DOZZ.IsCenteredJointlyGaussian`. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ
/-- A finite family is centered jointly Gaussian when each real linear combination is a centered
Gaussian and is in `L²`. See [KRV, Theorem 12.1]. -/
def IsCenteredJointlyGaussian {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) : Prop :=
  IsProbabilityMeasure P ∧
    (∀ i, AEMeasurable (fun ω => Z ω i) P) ∧
      ∀ a : ι → ℝ,
        MemLp (fun ω => ∑ i, a i * Z ω i) 2 P ∧
          ∃ v : ℝ≥0,
            P.map (fun ω => ∑ i, a i * Z ω i) = gaussianReal 0 v
end DOZZ
