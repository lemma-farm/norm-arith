import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.v8db32281b8c9.Zeta23.Defs ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Defs.lean — fixed data of the paper.

Reference text: the paper "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line". Bracketed labels [eq:foo] below are the paper's own labels.

Design (ζ-free abstract layer): nothing in this file mentions
riemannZeta. The zeros enter only through the abstract structure ZeroConfig
("every locally finite multiset of points in the strip 0<β<1 that is invariant under ρ ↦ 1−ρ̄",
paper end of §4). Only Zeta23/Statement.lean instantiates ZeroConfig from Mathlib's ζ.
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open scoped BigOperators ArithmeticFunction
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
/-! ## 0. Fourier convention dictionary  [Notation], [subsec:weil]

Paper: "Fourier transforms are f̂(τ) := ∫_ℝ f(u) e^{iτu} du, so that ∫ f ḡ = (1/2π) ∫ f̂ conj(ĝ)
and (f∗g)^ = f̂ ĝ."  and  "For f ∈ C_c²(ℝ) put h_f(z) := f̂(z) = ∫ f(u) e^{izu} du, an entire
function".  Mathlib's Real.fourierIntegral 𝓕 is ∫ f(v) e^{−2πi v ξ} dv, so for real τ:
    paperFT f τ = 𝓕 f (−τ / (2π)).
All paper-side statements use paperFT; conversion to 𝓕 happens only inside proofs. -/
/-- Paper Fourier transform / h_f :  paperFT f z = ∫ u, f u * exp (I * z * u)  for complex z
([Notation]; [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u)e^{izu} du"). -/
def paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u : ℝ, f u * Complex.exp (Complex.I * z * (u : ℂ))
/-! ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/

/-! ## 2. The densities μ, Π_X, P_X, ν_X  [eq:mudef]–[eq:nudef]

Paper, verbatim: "Define, for τ ∈ ℝ and X = e^L > 1, s := 1/2 + iτ,
  μ(τ)   := (1/2π) Re Γ'/Γ(1/4 + iτ/2) − (log π)/(2π),                      [eq:mudef]
  Π_X(τ) := 1/(2π(1/4+τ²)) + (1/π) Re (X^s − 1)/s,                           [eq:Pidef]
  P_X(τ) := −(1/π) Σ_{n≤X} Λ(n)/√n · cos(τ log n),                           [eq:Pdef]
  ν_X    := μ + Π_X + P_X."                                                   [eq:nudef]
-/

/-! ## 3. Abstract zero configurations  [Results], [subsec:weil], §4 closing paragraph -/

namespace ZeroConfig


end ZeroConfig
/-! ## 4. The test family  [subsec:family] -/
/-- "Fix once and for all a nondecreasing function ϱ ∈ C³(ℝ) with ϱ = 0 on (−∞,0] and ϱ = 1 on
[1,∞)"  [subsec:family]. -/
structure TaperProfile (ϱ : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 3 ϱ
  monotone : Monotone ϱ
  eq_zero : ∀ x ≤ 0, ϱ x = 0
  eq_one : ∀ x ≥ 1, ϱ x = 1

namespace Params
variable  (T : ℝ)

/-! ### The prime-side matrix (second expression in [eq:Gdef]) -/

end Params
/-! ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/
namespace ZeroConfig

end ZeroConfig
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.v8db32281b8c9.Zeta23.Taper.Basic ====
section
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
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23

namespace Taper
/-! ### Constants depending only on ϱ  [eq:phinorms] -/

/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/
variable (ϱ : ℝ → ℝ) (L w : ℝ)
/-- [eq:phidef]: "`φ(u) := ϱ((L/2 − |u|)/w)`, `u ∈ ℝ`". -/
noncomputable def phi (u : ℝ) : ℝ := ϱ ((L / 2 - |u|) / w)

/-- `φ̂(z) = h_φ(z) = ∫ φ(u) e^{izu} du` (paper convention, complex argument). -/
noncomputable def phiHat (z : ℂ) : ℂ := paperFT (fun u => (phi ϱ L w u : ℂ)) z

/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/
section Basic
variable {ϱ L w}

end Basic

end Taper
end Zeta23

end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_3b6c3aa7c83a9f518d8a_Strip ====
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Strip.lean.
[eq:hfbound] specialized to `f = φ`, `Λ_f = L/2` (as consumed by [prop:tail]):
"`|φ̂(r − iy)| ≤ e^{L/4} ‖φ''‖₁ |r − iy|⁻²`" for `|y| ≤ 1/2`.
All three statements are proved here from the general-`f` bounds in Zeta23/Poisson/PaperFT.lean,
and are consumed via `Zeta23.Params.norm_phiHat_*`.
Reference: the paper, §2.1 [eq:hfbound], §4 [prop:tail].
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
namespace Zeta23
namespace Taper
section HfPhi
variable {ϱ : ℝ → ℝ} {L w : ℝ}


set_option linter.unusedVariables false in
/-- [eq:hfbound] for φ, 0-th order: `‖φ̂(z)‖ ≤ e^{|Im z|·L/2} · ‖φ‖₁ ≤ e^{|Im z| L/2} · L`. -/
theorem norm_phiHat_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (z : ℂ) 
    (h_Zeta23_Taper_integral_phi_le : ∀ {ϱ : ℝ → ℝ} {L w : ℝ},
      Zeta23.TaperProfile ϱ → 0 < w → 2 * w ≤ L → ∫ (u : ℝ), Zeta23.Taper.phi ϱ L w u ≤ L)
    (h_Zeta23_Taper_phiC_support : ∀ {ϱ : ℝ → ℝ} {L w : ℝ},
      Zeta23.TaperProfile ϱ → 0 < w → ∀ (u : ℝ), (↑(Zeta23.Taper.phi ϱ L w u) : ℂ) ≠ 0 → |u| ≤ L / 2)
    (h_Zeta23_norm_paperFT_le : ∀ {f : ℝ → ℂ} {Λ : ℝ},
      MeasureTheory.Integrable f MeasureTheory.MeasureSpace.volume →
        (∀ (u : ℝ), f u ≠ 0 → |u| ≤ Λ) →
          ∀ (z : ℂ), ‖Zeta23.paperFT f z‖ ≤ Real.exp (|z.im| * Λ) * ∫ (u : ℝ), ‖f u‖)
    (h_Zeta23_Taper_phi_integrable : ∀ {ϱ : ℝ → ℝ} {L w : ℝ},
      Zeta23.TaperProfile ϱ →
        0 < w →
          2 * w ≤ L →
            MeasureTheory.Integrable (Zeta23.Taper.phi ϱ L w) MeasureTheory.MeasureSpace.volume)
    (h_Zeta23_Taper_phi_nonneg : ∀ {ϱ : ℝ → ℝ} {L w : ℝ}, Zeta23.TaperProfile ϱ → ∀ (u : ℝ), 0 ≤ Zeta23.Taper.phi ϱ L w u)
    :
    ‖phiHat ϱ L w z‖ ≤ Real.exp (|z.im| * (L / 2)) * L := by
  have hint : Integrable (fun u => (phi ϱ L w u : ℂ)) := (h_Zeta23_Taper_phi_integrable hϱ hw hwL).ofReal
  have h := h_Zeta23_norm_paperFT_le hint (h_Zeta23_Taper_phiC_support hϱ hw) z
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  refine le_trans h ?_
  gcongr
  calc ∫ u, |phi ϱ L w u| = ∫ u, phi ϱ L w u := by
        congr 1 with u; exact abs_of_nonneg (h_Zeta23_Taper_phi_nonneg hϱ u)
    _ ≤ L := h_Zeta23_Taper_integral_phi_le hϱ hw hwL

end HfPhi
end Taper
end Zeta23
