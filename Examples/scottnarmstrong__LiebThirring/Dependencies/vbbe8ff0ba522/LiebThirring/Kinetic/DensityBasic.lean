/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Defs.Density
public import Examples.scottnarmstrong__LiebThirring.Dependencies.vbbe8ff0ba522.LiebThirring.Kinetic.Insertion
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measurability, testing and mass of the one-particle density

Arbitrary representatives agreeing almost everywhere give the same density almost everywhere,
with no measurability assumption on the replacement.
-/
public section
open MeasureTheory WithLp
open scoped ENNReal NNReal
namespace LiebThirring
end LiebThirring
end
