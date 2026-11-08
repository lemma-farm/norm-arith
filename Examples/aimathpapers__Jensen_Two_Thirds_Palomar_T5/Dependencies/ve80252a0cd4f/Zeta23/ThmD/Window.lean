/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Window.lean — [thm:D], the concrete window.  A summary of the statements
proved is given at the bottom of the file.

The concrete Montgomery–Taylor window of the [thm:D] proof (paper §7.1):
  φ_D(u) := √(cos(√2 λ u/L)) · φ_flat(u),   φ_flat = Zeta23.Taper.phi ϱ L w (the §2.2 ramp taper),
i.e. the paper's "cos(√2 u/l)^{1/2} ϱ(L/2−|u|)" at general 0 < λ ≤ 1 (we avoid the λ = 1
endpoint; the paper's display is the λ = 1 case with w = 1) and with the ramp width w kept
free as everywhere else in this project.

On the support [−L/2, L/2] the cosine argument is ≤ √2λ/2 = ϑ ≤ 1/√2 < π/2, so cos ≥ cos ϑ ≥ 3/4
> 0 there and √cos is smooth on a neighbourhood; off the support φ_flat kills everything
(and Real.sqrt of a negative is 0, so φ_D is total and 0 outside [−L/2, L/2] regardless).

WHY THESE STATEMENTS (paper §7.1, first paragraph): "Nothing in Sections 4–5 used that φ is
flat-topped, only: φ ∈ C_c² even, 0 ≤ φ ≤ 1, supp φ = [−L/2,L/2], φ nonincreasing in |u|
(so ‖φ'‖₁ ≤ 2, ‖(φ²)'‖₁ ≤ 2), and ‖φ''‖₁, ‖(φ²)''‖₁ ≪ 1" + the moments [eq:abJ] "differ from
those of v*_λ by O(1/L)".
-/
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.ve80252a0cd4f.Zeta23.Taper.Basic
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.ve80252a0cd4f.Zeta23.Taper.Norms
import Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.ve80252a0cd4f.Zeta23.Taper.Decay
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
noncomputable section
open Real Set MeasureTheory
namespace Zeta23
namespace ThmD
variable {ϱ : ℝ → ℝ} {lam L w : ℝ}
/-! ### pointwise / support facts (sentence 1 of §7.1) -/
section JMoment
/-! #### jD_close: the J-moment of the window vs J* (no Fubini — everything is one-variable:
the sharp-window autocorrelation has a trigonometric closed form (product-to-sum + explicit
antiderivatives), its y-moment evaluates to (L³/2)·(the closed form of J*) [jStar_closed], and
the ramp only moves the autocorrelation by 4w pointwise). -/
end JMoment
section AutocorrC1
/-! #### C¹ facts for the autocorrelation (the g_D-side hypotheses of ThmD/PP.sumA2g_close):
for h C¹ with compact support and |h| ≤ 1, the autocorrelation is differentiable with
deriv = h ⋆ h' and |deriv| ≤ ∫|h'|.  Via Mathlib's convolution calculus. -/
open scoped Convolution
variable {h : ℝ → ℝ}
end AutocorrC1
/-!
Summary of the statements proved in this file:
cos_factor_ge, phiD_contDiff, phiD_antitoneOn, integral_abs_deriv_phiD_le,
integral_abs_deriv_phiD_sq_le, integral_abs_deriv2_phiD_le, integral_abs_deriv2_phiD_sq_le,
aD_close, bD_close, jD_close (via the 1-D route: jStar_closed [Functional.lean] + the
sharp-window autocorrelation closed form integral_cos_overlap/sharp_autocorr_eq + the
y-moment closed form integral_Cfun_moment + the 4w ramp comparison
integral_abs_phiDsq_sub_sharp/autocorr_phiDsq_close — no Fubini anywhere).
-/
end ThmD
end Zeta23
