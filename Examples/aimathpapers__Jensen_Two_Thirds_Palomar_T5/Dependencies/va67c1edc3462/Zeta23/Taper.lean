/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper.lean — the test family [subsec:family] of the paper §2.2 and its
elementary facts: text after [eq:phidef], [eq:phinorms], [eq:abdef], the facts after [eq:PhigA]
(incl. [eq:Phi2FT]), [eq:gbounds], [eq:psidef], [eq:psiints], and [eq:hfbound] specialized to φ.
([eq:hfbound] for general f is in `Zeta23.Poisson.PaperFT`.)

SUB-FILES: Zeta23/Taper/Basic.lean (defs + [eq:phidef] facts),
Norms.lean ([eq:phinorms], [eq:abdef]), Strip.lean ([eq:hfbound] for φ),
Decay.lean ([eq:gbounds], [eq:psidef], [eq:psiints]),
Fourier.lean ([eq:PhigA]-line facts, Plancherel, [eq:Phi2FT]).  This umbrella file
holds the consumer-facing `Params` layer, part 2 (φ̂/Φ/ψ/g/A_φ facts); part 1 (φ, a, b, C₁,
hfbound — depends only on Basic/Norms/Strip) is Zeta23/Taper/Params.lean, importable on its own.

ORGANIZATION.  Namespace `Zeta23.Taper`: generic parameters `(ϱ : ℝ → ℝ) (L w : ℝ)` — pure
one-variable calculus, no `T`.  Namespace `Zeta23.Params` (last section): the same facts for
`P : Params`, `T : ℝ` of Zeta23/Defs.lean (`L = P.L T`, `w = P.w`, `ϱ = P.ϱ`); the bridges
`P.phi T = Taper.phi P.ϱ (P.L T) P.w` etc. are `rfl`.  Consumers use the `Params` versions.

Side conditions: the paper fixes `1 ≤ w ≤ L/8` [eq:wrange].  Generic lemmas carry the minimal
hypothesis they need (`0 < w`, `2w ≤ L`, …); the `Params` versions uniformly assume
`hP : P.Valid` (gives `1 ≤ w`, `TaperProfile ϱ`) and `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Taper.Params
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Taper.Decay
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.va67c1edc3462.Zeta23.Taper.Fourier
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
/-! ## Instantiation for `P : Params`, `T : ℝ` (Zeta23/Defs.lean).
Consumer-facing names.  Hypotheses: `hP : P.Valid`, `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]). -/
namespace Params
variable {P : Params} {T : ℝ}
/-! #### hypothesis-free facts -/
section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL
/-! #### φ̂, Φ real/even/continuous; conj symmetry -/
theorem g_ge (y : ℝ) : max (P.L T - 2 * P.w - |y|) 0 ≤ P.g T y :=
  Taper.g_ge hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem g_le_Aphi (y : ℝ) : P.g T y ≤ P.Aphi T y :=
  Taper.g_le_Aphi hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem Aphi_le (y : ℝ) : P.Aphi T y ≤ max (P.L T - |y|) 0 :=
  Taper.Aphi_le hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem g_nonneg (y : ℝ) : 0 ≤ P.g T y := Taper.g_nonneg hP.taper (w_pos hP) (two_w_le hwL hP) y
end
end Params
end Zeta23
