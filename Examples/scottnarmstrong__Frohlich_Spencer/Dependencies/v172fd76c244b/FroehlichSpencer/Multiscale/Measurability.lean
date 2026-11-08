/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Multiscale.Singular
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Multiscale.Locality
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.ProductMeasure
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.Infra.Spectral.Regularity
public import Examples.scottnarmstrong__Frohlich_Spencer.Dependencies.v172fd76c244b.FroehlichSpencer.IDS.Averaged
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Measurability of singular-set events

For the product σ-algebra on configurations `Site ν → ℝ`: membership `x ∈ S_i(v)` and the
gentle-cluster events are measurable (both the infinite-volume and the `Λ`-restricted variants).
-/
@[expose] public section
open MeasureTheory
namespace FroehlichSpencer.Multiscale
section Aux
variable {Ω α : Type*} [MeasurableSpace Ω]
end Aux
section Generic
variable {ν : ℕ} (P : Params) (blk : Finset (Site ν) → Finset (Site ν))
  (S₀ : (Site ν → ℝ) → Set (Site ν))
variable {P S₀}
end Generic
end FroehlichSpencer.Multiscale
end
