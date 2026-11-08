/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Multiscale.Basic
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Multiscale.Clusters
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Surface.HamiltonianHermitian
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The singular-set recursion

FS83 (2.3)-(2.7) : `S_{i+1} = S_i ∖ S_i^g`, where `S_i^g` is the union of all
gentle `2 r_i`-chain clusters of `S_i`.
-/
@[expose] public section
namespace FroehlichSpencer.Multiscale
variable {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν)) (S₀ : Set (Site ν))
  (v : Site ν → ℝ)
end FroehlichSpencer.Multiscale
