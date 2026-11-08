/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.v58f9fa26be6f.FalconerThetaGauge.RegularMeasureEntryChains
public import Mathlib
set_option autoImplicit false
/-!
# Counting every actual child type along a chain

Fourier-state entries pay for far exits. The concrete longest-test alternative
pays for near moves by marked-depth crossings, following refinements, or the
last move. Together with the exact end-drop bounds, this proves Lemma 8.7.
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
