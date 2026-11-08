/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v4cb506007089.FroehlichSpencer.BKT.Surface.Multigraph
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v4cb506007089.FroehlichSpencer.BKT.Surface.SquarePeriodicEdge
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The periodic square domain `Λ_L^per` -/
@[expose] public section
namespace FroehlichSpencer.BKT
/-- The square domain `Λ_L^per` with periodic boundary conditions (KP p. 2): vertices
`{0, …, L - 1}²`, edges `SquarePeriodicEdge L`, each oriented from its lexicographically
smaller endpoint. KP take `L > 1` even. -/
def squarePeriodic (L : ℕ) : Multigraph (Fin L × Fin L) (SquarePeriodicEdge L) where
  src e := e.1.1
  tgt e := e.1.2
  src_ne_tgt e h := lt_irrefl (toLex e.1.2) (h ▸ e.2.1)
end FroehlichSpencer.BKT
end
