-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Numeric.Exponents
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Construction.Scalars
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section3.PermittedInterval
public import Mathlib
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section3.KMat
public import Mathlib.Analysis.Matrix.Normed
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Scalar bridges for §4. Diffusivity results named `conditional` take the
applicable diffusivity-recursion conclusion explicitly. No draft theorem module is imported.
The top index never acquires an interior two-sided bound. -/
@[expose] public section
noncomputable section
namespace AVenhance.Infra.Section4
open scoped Matrix.Norms.Elementwise
open AVenhance
open AVenhance.Infra.Ingredients
end AVenhance.Infra.Section4
