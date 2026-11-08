-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Construction.StreamVel
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Construction.IsStreamSeq
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Ingredients.EpsilonConsequences
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Conditional hypotheses for the limit-field argument in §2.

`StreamRegularityBounds` is exactly the three estimates in the first part of the stream-regularity estimates:
the increment estimate at every order, the estimate on `Φ m` for `n ≥ 2`,
and the low-order estimate on `Φ m` for `n ≤ 1`.  It is data, not an import
of the draft theorem.  `StreamVelocityTimeIncrementBound` isolates the one
additional quantitative input used below for temporal Hölder continuity; it
is the mean-value consequence of the estimate obtained by differentiating
the recursion in (e.psi.recursion.partial.t).
-/
@[expose] public section
open MeasureTheory Homogenization Filter Topology
noncomputable section
namespace AVenhance
end AVenhance
