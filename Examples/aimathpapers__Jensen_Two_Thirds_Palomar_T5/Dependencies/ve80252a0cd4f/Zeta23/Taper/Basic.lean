/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.ve80252a0cd4f.Zeta23.Defs
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.ve80252a0cd4f.Zeta23.Poisson.PaperFT
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
namespace Taper
/-! ### Constants depending only on ϱ  [eq:phinorms] -/
variable (ϱ : ℝ → ℝ) (L w : ℝ)
/-- [eq:phidef]: "`φ(u) := ϱ((L/2 − |u|)/w)`, `u ∈ ℝ`". -/
noncomputable def phi (u : ℝ) : ℝ := ϱ ((L / 2 - |u|) / w)
noncomputable def phiHat (z : ℂ) : ℂ := paperFT (fun u => (phi ϱ L w u : ℂ)) z
noncomputable def Phi (z : ℂ) : ℂ := paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) z
noncomputable def g (y : ℝ) : ℝ := Params.autocorr (fun u => (phi ϱ L w u) ^ 2) y
/-- [eq:PhigA]: "`A_φ := φ ⋆ φ`". -/
noncomputable def Aphi (y : ℝ) : ℝ := Params.autocorr (phi ϱ L w) y
section Basic
variable {ϱ L w}
end Basic
end Taper
end Zeta23
