/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.ve54961c61da9.MarkovProcess.Semigroup.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Continuity of semigroup orbits from continuity at zero

For a contractive semigroup, strong convergence to the identity at time zero
propagates to continuity of every orbit at every nonnegative time.  Contractivity also upgrades
strong continuity to joint continuity in the time and the vector, in the form
`continuous_operator_apply`.
-/
open Filter Topology
namespace MarkovProcess.Semigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace StronglyContinuousContractionSemigroup
end StronglyContinuousContractionSemigroup
end MarkovProcess.Semigroup
