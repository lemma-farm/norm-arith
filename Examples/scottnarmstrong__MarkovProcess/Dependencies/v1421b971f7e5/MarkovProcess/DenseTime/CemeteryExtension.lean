/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Constructions.SumProd
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal
namespace MarkovProcess
variable {α : Type*}
/-- A state space with one additional isolated cemetery state. -/
abbrev Cemetery (α : Type*) := α ⊕ Unit
/-- Embed a live state into the cemetery extension. -/
abbrev Cemetery.alive (x : α) : Cemetery α := Sum.inl x
/-- The cemetery state. -/
abbrev Cemetery.delta : Cemetery α := Sum.inr ()
namespace Kernel
variable [MeasurableSpace α]
end Kernel
end MarkovProcess
