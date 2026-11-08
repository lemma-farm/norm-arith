/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Params.lean.  Consumer-facing layer, part 1:
the `P : Params`, `T : ℝ` versions of everything that depends only on Taper/Basic, Taper/Norms
and Taper/Strip (φ facts [eq:phidef], [eq:abdef], C₁ and [eq:hfbound] for φ), plus the rfl
bridges to Defs.  Split out of Zeta23/Taper.lean so that Zeta23/Main.lean can import it without
pulling Taper/Decay, Taper/Fourier.  Hypotheses: `hP : P.Valid`,
`hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).  The remaining Params-layer facts (φ̂/Φ, ψ, g, A_φ,
Plancherel) are in the umbrella Zeta23/Taper.lean.
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Taper.Basic
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Taper.Norms
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Taper.Strip
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
namespace Zeta23
namespace Params
variable (P : Params) (T : ℝ)
variable {P T}
theorem w_pos (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
theorem two_w_le (hwL : 8 * P.w ≤ P.L T) (hP : P.Valid) : 2 * P.w ≤ P.L T := by
  linarith [hP.one_le_w]
/-! #### hypothesis-free facts -/
section
variable (hP : P.Valid)
include hP
theorem phi_nonneg (u : ℝ) : 0 ≤ P.phi T u := Taper.phi_nonneg hP.taper u
theorem phi_le_one (u : ℝ) : P.phi T u ≤ 1 := Taper.phi_le_one hP.taper u
theorem phi_eq_zero {u : ℝ} (hu : P.L T / 2 ≤ |u|) : P.phi T u = 0 :=
  Taper.phi_eq_zero hP.taper (w_pos hP) hu
theorem phi_eq_one {u : ℝ} (hu : |u| ≤ P.L T / 2 - P.w) : P.phi T u = 1 :=
  Taper.phi_eq_one hP.taper (w_pos hP) hu
theorem phi_hasCompactSupport : HasCompactSupport (P.phi T) :=
  Taper.phi_hasCompactSupport hP.taper (w_pos hP)
theorem phi_support_subset : Function.support (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) :=
  Taper.phi_support_subset hP.taper (w_pos hP)
end
section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL
/-! #### φ -/
theorem phi_contDiff : ContDiff ℝ 3 (P.phi T) :=
  Taper.phi_contDiff hP.taper (w_pos hP) (two_w_le hwL hP)
theorem phi_continuous : Continuous (P.phi T) :=
  Taper.phi_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
/-! #### [eq:abdef] -/
theorem b_le_a : P.b T ≤ P.a T := Taper.bConst_le_aConst hP.taper (w_pos hP) (two_w_le hwL hP)
theorem a_le_one : P.a T ≤ 1 := Taper.aConst_le_one hP.taper (w_pos hP) (two_w_le hwL hP)
end
end Params
end Zeta23
