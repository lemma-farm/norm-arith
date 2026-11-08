/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Examples.CoolRmal__falconer_theta_gauge.Dependencies.vbc537bd91a3d.FalconerThetaGauge.RegularMeasureEntryChainSteps
public import Mathlib
set_option autoImplicit false
/-!
# Finite chains of the actual induction moves

The chain contains concrete states and genuine transitions. Its start depths
increase, its end depths decrease, and visits or crossings of marked depths
are counted injectively.
-/
@[expose] public section
noncomputable section
open Finset
open scoped Classical
namespace FalconerThetaGauge
/-- A finite chain of the actual six child types of Table 1. -/
structure ProfileMoveChain (A : ℕ → ℝ) (q N δ : ℕ) where
  length : ℕ
  state : ℕ → ProfileChainState
  step (i : ℕ) (hi : i < length) : ProfileChainMove A q N δ (state i) (state (i + 1))
  valid_initial : (state 0).Valid N δ
namespace ProfileMoveChain
variable {A : ℕ → ℝ} {q N δ : ℕ} (chain : ProfileMoveChain A q N δ)
end ProfileMoveChain
end FalconerThetaGauge
