/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.vf2d1c3fc4e53.FroehlichSpencer.BKT.Surface.Multigraph
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The simple graph underlying a multigraph -/
@[expose] public section
namespace FroehlichSpencer.BKT
universe u v
/-- The simple graph underlying a multigraph: distinct vertices `j`, `ℓ` are adjacent
(`j ∼ ℓ`, KP p. 2) when some edge joins them. KP's graph distance `dist` and connectedness are
those of this graph; edge multiplicities play no role in them. -/
def Multigraph.toSimpleGraph {V : Type u} {E : Type v} (G : Multigraph V E) : SimpleGraph V :=
  SimpleGraph.fromRel fun j ℓ => ∃ e, (G.src e = j ∧ G.tgt e = ℓ) ∨ (G.src e = ℓ ∧ G.tgt e = j)
end FroehlichSpencer.BKT
end
