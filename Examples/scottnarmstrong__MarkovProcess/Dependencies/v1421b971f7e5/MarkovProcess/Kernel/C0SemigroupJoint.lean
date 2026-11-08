/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Semigroup.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Joint regularity of strongly continuous semigroups on `C₀`

Strong continuity of a semigroup orbit in the `C₀` norm and continuity of
evaluation give continuity, jointly in time and state, of the evaluated orbit.
The corresponding Borel measurability statement follows without any additional
regularity premise on the semigroup.

This is a generic functional-analytic API. It makes no representation claim
about the semigroup.
-/
open scoped ZeroAtInfty
namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
variable {α : Type*} [TopologicalSpace α]
end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
