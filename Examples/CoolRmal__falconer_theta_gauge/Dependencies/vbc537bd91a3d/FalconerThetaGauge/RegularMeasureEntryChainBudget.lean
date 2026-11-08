/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureEntryChainCosts
public import Mathlib
set_option autoImplicit false
/-!
# Telescoping the actual costs through a finite chain

Every prefix with a sufficiently long final interval is paid by its budget
increase. For an arbitrarily short leaf, the last positive-cost move still
has a `40q` margin; this yields the exact leaf-point bound needed in Section 8.5.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
namespace ProfileMoveChain
variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)
end ProfileMoveChain
end FalconerThetaGauge
