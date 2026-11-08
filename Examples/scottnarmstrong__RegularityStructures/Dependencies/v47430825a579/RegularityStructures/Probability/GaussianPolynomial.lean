/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianLaw
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianGrowthIntegrability
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomial bounds in Gaussian `Lᵖ` spaces

The finite Gaussian moment theorem is converted here into the polynomial domination estimates
used by the analytic Poincare proof.  No integrability condition is hidden in a proposition-valued
admissibility predicate.
-/
@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
namespace RegularityStructures
end RegularityStructures
end
