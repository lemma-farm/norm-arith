/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Defs.Configuration
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# One-particle density

The spatial density obtained by integrating out all other particle coordinates and summing over
particles.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring
end LiebThirring
end
