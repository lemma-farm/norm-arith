/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.ve34072bd0687.MarkovProcess.Semigroup.Generator
import Mathlib.Analysis.ODE.Gronwall
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Eigenvectors of a generator, and injectivity of `μ - L`

Let `S` be a strongly continuous contraction semigroup with generator `L`.  If `f` lies in the
generator domain with `L f = μ f`, then the orbit of `f` is the scalar exponential
`S t f = exp (μ t) f`: the defect `w t = S t f - exp (μ t) f` vanishes at `t = 0` and has right
derivative `μ w t`, so Grönwall's inequality forces it to vanish
(`operator_eq_exp_smul_of_generator_eq_smul`).

Since `S` is contractive, an eigenvalue `μ > 0` therefore forces `f = 0`
(`eq_zero_of_generator_eq_smul`); equivalently, `μ - L` is injective on the generator domain
(`eq_of_smul_sub_generator_eq`).  This is the uniqueness half of the assertion that the resolvent
`(μ - L)⁻¹` is a well-defined operator.
-/
open Filter Set Topology
open scoped NNReal
namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)
end
end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
