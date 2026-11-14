import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.vb4d2558def68.Zeta23.Hypotheses ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Hypotheses.lean — the hypothesis ("axiom") boundary.

Canonical text: the paper.

PRINCIPLE: the fields of PaperInputs are PUBLISHED, CLASSICAL inputs,
stated in the paper's own form with the paper's equation labels. Everything the paper itself derives
(lem:poisson, prop:block, prop:tail, [eq:PiPfacts], [eq:Bdef], prop:trace, thm:traces, §6, taper facts
[eq:phinorms]–[eq:psiints], …) is a proof obligation and must NOT be added here. There are NO Lean
axiom declarations anywhere in this project: hypotheses are fields of the Prop-valued structure
PaperInputs, which every headline theorem takes as an explicit argument, so #print axioms stays at
{propext, Classical.choice, Quot.sound} and the trust boundary is exactly this file.

Every field below: docstring = paper label + verbatim paper statement + literature source + any
deviation in shape (∃-constant form unless the constant is load-bearing).
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open scoped BigOperators ArithmeticFunction ComplexConjugate ContDiff
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
/-! ## H-EF — Weil's explicit formula in the paper's spectral form  [prop:EF], [eq:EF], [eq:Wdef] -/

/-! ## H-MV — Montgomery–Vaughan weighted Hilbert inequality  [lem:MV] -/
/-- The weighted ("generalised") Hilbert inequality with constant C [lem:MV], verbatim:
"Let λ_1,…,λ_R be distinct real numbers, δ_r := min_{s≠r} |λ_r − λ_s|, and x_r, z_r ∈ ℂ. Then
  |Σ_{r≠s} x_r conj(z_s)/(λ_r − λ_s)| ≤ (3π/2) (Σ_r |x_r|²/δ_r)^{1/2} (Σ_r |z_r|²/δ_r)^{1/2}."
Source: [MV74, Theorem 2] for z = x (the paper citation); the bilinear form is derived in the paper by a
3-line operator-norm argument. "Any absolute constant in place of 3π/2 would suffice below."
Shape notes: index set = any Fintype ι with DecidableEq; distinctness = injectivity of freq; instead
of δ_r := min_{s≠r}|λ_r−λ_s| (undefined for R = 1) we allow ANY admissible weights 0 < δ_r ≤
|λ_r − λ_s| (s ≠ r) — equivalent to the paper's statement since the right side is antitone in δ.
The bilinear (x,z) form is assumed directly (it is what prop:PP/prop:cross consume). -/
def MVHilbert (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (freq δ : ι → ℝ) (x z : ι → ℂ),
    Function.Injective freq → (∀ r, 0 < δ r) → (∀ r s, r ≠ s → δ r ≤ |freq r - freq s|) →
    ‖∑ r, ∑ s, if r = s then (0 : ℂ) else x r * conj (z s) / ((freq r - freq s : ℝ) : ℂ)‖
      ≤ C * Real.sqrt (∑ r, ‖x r‖ ^ 2 / δ r) * Real.sqrt (∑ r, ‖z r‖ ^ 2 / δ r)
/-! ## H-Γ — Stirling-type facts for μ  [eq:mufacts], [eq:muints] -/
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.vb4d2558def68.Zeta23.PrimeSideA.Defs ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side (paper §5 [sec:prime]) — ABSTRACT LAYER & SHARED DEFINITIONS
for PrimeSideA.lean / PrimeSideB.lean.

Bracketed labels and section numbers (§5.2, …) are as in the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".

SEAM between PrimeSideA.lean and PrimeSideB.lean:
  * The seam object is the symmetric bilinear form
        𝓜[u₁,u₂] := ∬_{I×I} Φ(τ−τ')² u₁(τ) u₂(τ') dτ dτ',   I = [T,2T]          (§5.4)
    spelled here LITERALLY as `Mform Φ T u₁ u₂` below, and 𝓜 := 𝓜[ν_X,ν_X] = `MtotalA`.
  * PrimeSideA.lean : [prop:trace] tr G̃ = aL·N(T,2T)+O(L√X);
      [eq:trG2int]+[eq:Kbounds]+[lem:ends] tr G̃² = 𝓜 + O(L·l·log l·(l²+X));
      [eq:Msplit] (6-term expansion of 𝓜); [prop:mumu]; [prop:cross] (four bounds).
  * PrimeSideB.lean : [prop:PP] incl. 𝒟/𝒪₁/𝒪₂ and the g-sandwich via H-cheb [eq:cheb2];
      [thm:traces] = [eq:tr1],[eq:tr2],[eq:ratio] assembling A's five results + prop:PP + H-Γ [eq:muints] + H-RvM.
  * Error-term shape everywhere: ∃ C T₀ (allowed to depend on the profile constants and on λ),
      ∀ T ≥ T₀, |lhs − main| ≤ C·(error expression).  No filters / IsBigO until the final liminf wrapper.

ABSTRACT LAYER.  §5 is a computation about the functions φ̂, Φ, μ, Π_X, P_X on the REAL line
using only a short list of facts about them ([eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
[lem:poisson], [eq:mufacts], [eq:PiPfacts], [lem:cheb]).  We therefore prove §5 for ABSTRACT data
(`Setting` = the scalars T, λ, w;  `LocalFun` = the taper data φ̂, Φ, A_φ, g, a, b) subject
to exactly those facts (hypothesis structures in PrimeSideA.lean), and a thin bridge
(Zeta23/PrimeSideA/Bridge.lean) instantiates it with the
concrete objects of Zeta23/Defs.lean: `Zeta23.Params.phiHatR`, `.PhiR`, `.a`, `.b`, `.g`, `.Aphi`,
so that `trGtA` below becomes `Zeta23.Params.trGtilde` etc.  Names in this
layer carry a trailing `A` (abstract) where they would otherwise clash with Zeta23/Defs.lean.
The closed-form, ζ-free objects `Zeta23.l`, `Zeta23.ell1`, `Zeta23.mu` [eq:mudef], `Zeta23.PiX` [eq:Pidef],
`Zeta23.PX` [eq:Pdef], `Zeta23.nuX` [eq:nudef] are used DIRECTLY from Zeta23/Defs.lean, and the analytic
inputs H-Γ / H-cheb are Zeta23/Hypotheses.lean's `GammaFacts` / `ChebyshevMertens` verbatim, so the
statements here are literally about the official objects of Zeta23/Defs.lean; only the taper enters
abstractly.

The prime side is ζ-free: N(T,2T) enters only as an abstract real together
with [eq:RvM].

FOURIER CONVENTION: paper f̂(τ) := ∫ f(u) e^{iτu} du (§1.4) = `Zeta23.paperFT`.  On
this side we only meet φ̂ and Φ := (φ²)^ on ℝ, where they are real and even; we carry them as
functions ℝ → ℝ (= `phiHatR`, `PhiR` of Defs.lean).
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
namespace Zeta23
namespace PrimeSide
/-! ## Scalars of the abstract setting  [§1 Notation, §1.4; eq:wrange; eq:fk] -/

namespace Setting


end Setting
/-! ## The prime-power sum: notation of §5 for `Zeta23.PX` [eq:Pdef, §2.1] -/
/-- `a_n := Λ(n) n^{-1/2}` [Notation, §1.4]. -/
def acoef (n : ℕ) : ℝ := (Λ n : ℝ) / Real.sqrt n
/-- The index set "prime powers `n ≤ X`": all `0 < n ≤ ⌊X⌋` weighted by Λ (zero off prime powers);
spelled `Finset.Ioc 0 ⌊X⌋₊` as in Zeta23/Defs.lean's `PX` and Mathlib's `Chebyshev.psi`. -/
def primeRange (X : ℝ) : Finset ℕ := Finset.Ioc 0 ⌊X⌋₊



end PrimeSide
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.vb4d2558def68.Zeta23.PrimeSideB.PPKernel ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/
noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
namespace Zeta23
namespace PrimeSide
/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/
section Basics

end Basics
/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/
section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}

end Shear
/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/
section CosIntegral

/-- Closed form of `J(θ,c;α,β) := ∫_α^β cos(θt + c) dt`:  `(β−α)cos c` if `θ = 0` (§5.4 "the first
inner integral is T−|x|"), else `[sin(θβ+c) − sin(θα+c)]/θ` (§5.4). -/
def Jker (θ c α β : ℝ) : ℝ :=
  if θ = 0 then (β - α) * Real.cos c else (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ

variable {T : ℝ}
end CosIntegral
/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/
section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}

/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/
/-- The four half-line trigonometric moments of Φ² (the paper's α_n^±, §5.4, split into
real and imaginary parts): C⁺(y) = ∫_0^T Φ²cos(xy), S⁺(y) = ∫_0^T Φ²sin(xy),
C⁻(y) = ∫_{−T}^0 Φ²cos(xy), S⁻(y) = ∫_{−T}^0 Φ²sin(xy). -/
def Cp (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Φ x ^ 2 * Real.cos (x * y)
def Sp (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (0:ℝ)..T, Φ x ^ 2 * Real.sin (x * y)
def Cm (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (-T)..0, Φ x ^ 2 * Real.cos (x * y)
def Sm (Φ : ℝ → ℝ) (T y : ℝ) : ℝ := ∫ x in (-T)..0, Φ x ^ 2 * Real.sin (x * y)

end PairDecomp
/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/
section MVapply
variable {C : ℝ}

end MVapply
end PrimeSide
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_9075951f1950005b4030_PPChi ====
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# [prop:PP] for L(s,chi)

[thm:E] proof (iii) (§8.2): "the coefficients a_n acquire unimodular factors chi(n)n^{i.}, which
leave the diagonal D unchanged (|chi(n)|^2 = 1) and enter Lemma lem:MV and all other bounds only
through |a_n|".  This file proves that sentence for [prop:PP]:

* prop_PP_chi:  |M[P_{X,c}, P_{X,c}] − (T/pi)·sumA2gCoprime| ≤ C·L²X, over EventuallyAtCore
  (window-generic: no flat-top plateau fact used); hypotheses H-cheb + H-MV + CoeffUnimodular
  (unimodularity used EXACTLY once: the diagonal main term a_n²·normSq(c n)).
* sumA2gCoprime_upper (over EventuallyAtCore) and sumA2gCoprime_lower (over the FULL EventuallyAt:
  the lower g-sandwich needs LocalHyps.g_lower, which LocalHypsCore deliberately lacks — the
  Montgomery–Taylor window case supplies its own analogue), from H-cheb-coprime.

Route (magnitude/phase): write c n = r_n·exp(i·phi_n),
r_n := norm (c n), phi_n := arg (c n), so P_{X,c}(tau) = −(1/pi)·Sum_n a_n·r_n·cos(tau·log n − phi_n)
— ONE family of phase-shifted cosines.  The PPKernel pair decomposition generalizes by a single
phase parameter (Jker already carries an arbitrary constant): AminusPh/AplusPh below.  On the
diagonal the phase difference vanishes and AminusPh = Aminus, giving the zeta diagonal with weight
r_n²; the off-diagonal [lem:MV] application takes x_n with norm x_n ≤ a_n ("only through |a_n|");
the O2 bound is phase-free.
-/
noncomputable section
open MeasureTheory Real Set Finset ComplexConjugate
open scoped BigOperators ArithmeticFunction
namespace Zeta23
namespace ThmE
open Zeta23.PrimeSide
variable {cϱ lam : ℝ} {q : ℕ} {c : ℕ → ℂ}

section PhaseKernel
variable {Φ : ℝ → ℝ} {T : ℝ}
/-- A⁻ with phases. -/
def AminusPh (Φ : ℝ → ℝ) (T y y' φ φ' : ℝ) : ℝ :=
  ∫ x in Icc (-T) T,
    Φ x ^ 2 * Jker (y - y') (x * y - (φ - φ')) (max (T - x) T) (min (2 * T - x) (2 * T))

end PhaseKernel
section PhasePair
variable {Φ : ℝ → ℝ} {T : ℝ}

end PhasePair
section PhaseO1
variable {Φ : ℝ → ℝ} {T : ℝ}

end PhaseO1
/-! ## The magnitude/phase form of P_{X,c} -/
section PXcForm

end PXcForm
/-! ## H-MV with phases -/
section MVPh
variable {C : ℝ}

end MVPh
/-! ## The decomposition 𝓜[P_{X,c}, P_{X,c}] = 𝒟 + 𝒪₁ + 𝒪₂, weighted and phased -/
section Decomp
variable {Φ : ℝ → ℝ} {T : ℝ}

end Decomp
/-! ## The three estimates, weighted and phased -/
section Estimates
variable {Φ : ℝ → ℝ} {T : ℝ}

end Estimates
/-! ## 𝒪₁ for P_{X,c} -/
section O1Chi
variable {Φ : ℝ → ℝ} {T : ℝ}
set_option linter.unusedVariables false in
/-- 𝒪₁ for P_{X,c} (mirror of O1_bound; weights a_k‖c k‖ ≤ a_k, phases arg(c k) ride into
MV_real_ph): |Σ_{n≠m} w_n w_m A⁻_ph| ≤ 16·C·(∫Φ²)·ΣΛ². -/
theorem O1_bound_chi {C : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) (hc1 : ∀ n, ‖c n‖ ≤ 1) (X : ℝ) 
    (h_Zeta23_ThmE_sub_mul_AminusPh_eq : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          ∀ {y y' : ℝ},
            y - y' ≠ 0 →
              ∀ (φ φ' : ℝ),
                (y - y') * Zeta23.ThmE.AminusPh Φ T y y' φ φ' =
                  Real.sin ((y - y') * (2 * T) - (φ - φ')) * Zeta23.PrimeSide.Cm Φ T y +
                        Real.cos ((y - y') * (2 * T) - (φ - φ')) * Zeta23.PrimeSide.Sm Φ T y -
                      (Real.sin ((y - y') * T - (φ - φ')) * Zeta23.PrimeSide.Cm Φ T y' +
                        Real.cos ((y - y') * T - (φ - φ')) * Zeta23.PrimeSide.Sm Φ T y') +
                    (Real.sin ((y - y') * (2 * T) - (φ - φ')) * Zeta23.PrimeSide.Cp Φ T y' +
                        Real.cos ((y - y') * (2 * T) - (φ - φ')) * Zeta23.PrimeSide.Sp Φ T y' -
                      (Real.sin ((y - y') * T - (φ - φ')) * Zeta23.PrimeSide.Cp Φ T y +
                        Real.cos ((y - y') * T - (φ - φ')) * Zeta23.PrimeSide.Sp Φ T y)))
    (h_Zeta23_PrimeSide_abs_Sm_le : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
            ∀ (y : ℝ), |Zeta23.PrimeSide.Sm Φ T y| ≤ ∫ (x : ℝ), Φ x ^ 2)
    (h_Zeta23_PrimeSide_abs_Sp_le : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
            ∀ (y : ℝ), |Zeta23.PrimeSide.Sp Φ T y| ≤ ∫ (x : ℝ), Φ x ^ 2)
    (h_Zeta23_PrimeSide_abs_Cp_le : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
            ∀ (y : ℝ), |Zeta23.PrimeSide.Cp Φ T y| ≤ ∫ (x : ℝ), Φ x ^ 2)
    (h_Zeta23_PrimeSide_abs_Cm_le : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
            ∀ (y : ℝ), |Zeta23.PrimeSide.Cm Φ T y| ≤ ∫ (x : ℝ), Φ x ^ 2)
    (h_Zeta23_PrimeSide_one_le_of_mem_primeRange : ∀ {X : ℝ} {n : ℕ}, n ∈ Zeta23.PrimeSide.primeRange X → 1 ≤ n)
    (h_Zeta23_ThmE_MV_real_ph : ∀ {C : ℝ},
      Zeta23.MVHilbert C →
        ∀ (X cc : ℝ) (u v φv : ℕ → ℝ),
          |∑ n ∈ Zeta23.PrimeSide.primeRange X,
                  ∑ m ∈ Zeta23.PrimeSide.primeRange X,
                    if n = m then 0
                    else
                      u n * v m *
                          Real.cos (cc * (Real.log (↑n : ℝ) - Real.log (↑m : ℝ)) - (φv n - φv m)) /
                        (Real.log (↑n : ℝ) - Real.log (↑m : ℝ))| ≤
              C * √(∑ n ∈ Zeta23.PrimeSide.primeRange X, u n ^ 2 * (2 * (↑n : ℝ))) *
                √(∑ n ∈ Zeta23.PrimeSide.primeRange X, v n ^ 2 * (2 * (↑n : ℝ))) ∧
            |∑ n ∈ Zeta23.PrimeSide.primeRange X,
                  ∑ m ∈ Zeta23.PrimeSide.primeRange X,
                    if n = m then 0
                    else
                      u n * v m *
                          Real.sin (cc * (Real.log (↑n : ℝ) - Real.log (↑m : ℝ)) - (φv n - φv m)) /
                        (Real.log (↑n : ℝ) - Real.log (↑m : ℝ))| ≤
              C * √(∑ n ∈ Zeta23.PrimeSide.primeRange X, u n ^ 2 * (2 * (↑n : ℝ))) *
                √(∑ n ∈ Zeta23.PrimeSide.primeRange X, v n ^ 2 * (2 * (↑n : ℝ))))
    (h_Zeta23_ThmE_MV_size_le₂ : ∀ {C : ℝ},
      0 ≤ C →
        ∀ (X : ℝ) {w₁ w₂ : ℕ → ℝ} {W : ℝ},
          0 ≤ W →
            (∀ n ∈ Zeta23.PrimeSide.primeRange X, |w₁ n| ≤ 1) →
              (∀ n ∈ Zeta23.PrimeSide.primeRange X, |w₂ n| ≤ W) →
                C *
                        √(∑ n ∈ Zeta23.PrimeSide.primeRange X,
                            (Zeta23.PrimeSide.acoef n * w₁ n) ^ 2 * (2 * (↑n : ℝ))) *
                      √(∑ n ∈ Zeta23.PrimeSide.primeRange X,
                          (Zeta23.PrimeSide.acoef n * w₂ n) ^ 2 * (2 * (↑n : ℝ))) ≤
                    2 * C * W *
                      ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                        (ArithmeticFunction.vonMangoldt : ℕ → ℝ) n ^ 2 ∧
                  C *
                        √(∑ n ∈ Zeta23.PrimeSide.primeRange X,
                            (Zeta23.PrimeSide.acoef n * w₂ n) ^ 2 * (2 * (↑n : ℝ))) *
                      √(∑ n ∈ Zeta23.PrimeSide.primeRange X,
                          (Zeta23.PrimeSide.acoef n * w₁ n) ^ 2 * (2 * (↑n : ℝ))) ≤
                    2 * C * W *
                      ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                        (ArithmeticFunction.vonMangoldt : ℕ → ℝ) n ^ 2)
    :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
          * AminusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg)|
      ≤ 16 * C * (∫ x, Φ x ^ 2) * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set W : ℝ := ∫ x, Φ x ^ 2 with hW
  have hW0 : 0 ≤ W := MeasureTheory.integral_nonneg fun x => sq_nonneg _
  set Λ2 : ℝ := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  set S1 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Cm Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.sin ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS1
  set S2 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Sm Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.cos ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS2
  set S3 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Cm Φ T (Real.log m)))
      * Real.sin (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS3
  set S4 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Sm Φ T (Real.log m)))
      * Real.cos (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS4
  set S5 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Cp Φ T (Real.log m)))
      * Real.sin ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS5
  set S6 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * ‖c n‖ * (acoef m * (‖c m‖ * Sp Φ T (Real.log m)))
      * Real.cos ((2 * T) * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS6
  set S7 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Cp Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.sin (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS7
  set S8 : ℝ := ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
    acoef n * (‖c n‖ * Sp Φ T (Real.log n)) * (acoef m * ‖c m‖)
      * Real.cos (T * (Real.log n - Real.log m) - ((c n).arg - (c m).arg)) / (Real.log n - Real.log m)) with hS8
  have hsplit : ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
      (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
        * AminusPh Φ T (Real.log n) (Real.log m) ((c n).arg) ((c m).arg))
      = S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8 := by
    rw [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    by_cases hnm : n = m
    · simp [hnm]
    · simp only [if_neg hnm]
      have hθ : Real.log n - Real.log m ≠ 0 := by
        have hn1 := h_Zeta23_PrimeSide_one_le_of_mem_primeRange hn
        have hm1 := h_Zeta23_PrimeSide_one_le_of_mem_primeRange hm
        have hinj : Real.log n ≠ Real.log m := by
          rcases lt_or_gt_of_ne hnm with hlt | hgt
          · exact ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt))
          · exact ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt))
        exact sub_ne_zero.mpr hinj
      have hA := h_Zeta23_ThmE_sub_mul_AminusPh_eq (Φ := Φ) hT hΦ hθ ((c n).arg) ((c m).arg)
      have hAm : AminusPh Φ T (Real.log n) (Real.log m) ((c n).arg) ((c m).arg)
          = ((Real.sin ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Cm Φ T (Real.log n)
              + Real.cos ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Sm Φ T (Real.log n)
              - (Real.sin ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Cm Φ T (Real.log m)
                + Real.cos ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Sm Φ T (Real.log m)))
            + (Real.sin ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Cp Φ T (Real.log m)
              + Real.cos ((Real.log n - Real.log m) * (2 * T) - ((c n).arg - (c m).arg)) * Sp Φ T (Real.log m)
              - (Real.sin ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Cp Φ T (Real.log n)
                + Real.cos ((Real.log n - Real.log m) * T - ((c n).arg - (c m).arg)) * Sp Φ T (Real.log n))))
            / (Real.log n - Real.log m) := by
        rw [eq_div_iff hθ, mul_comm]
        exact hA
      rw [hAm, mul_comm ((2 : ℝ) * T) (Real.log n - Real.log m),
        mul_comm T (Real.log n - Real.log m)]
      field_simp
      ring
  have hb : ∀ (M : ℕ → ℝ), (∀ n ∈ primeRange X, |M n| ≤ W) →
      (∀ n ∈ primeRange X, |‖c n‖ * M n| ≤ W) := by
    intro M hM n hn
    rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    calc ‖c n‖ * |M n| ≤ 1 * W := by
          apply mul_le_mul (hc1 n) (hM n hn) (abs_nonneg _) zero_le_one
      _ = W := one_mul _
  have hc1' : ∀ n ∈ primeRange X, |(‖c n‖ : ℝ)| ≤ 1 := by
    intro n _
    rw [abs_of_nonneg (norm_nonneg _)]
    exact hc1 n
  have hw_Cm : ∀ n ∈ primeRange X, |Cm Φ T (Real.log n)| ≤ W := fun n _ => h_Zeta23_PrimeSide_abs_Cm_le hT hΦ hΦ2 _
  have hw_Sm : ∀ n ∈ primeRange X, |Sm Φ T (Real.log n)| ≤ W := fun n _ => h_Zeta23_PrimeSide_abs_Sm_le hT hΦ hΦ2 _
  have hw_Cp : ∀ n ∈ primeRange X, |Cp Φ T (Real.log n)| ≤ W := fun n _ => h_Zeta23_PrimeSide_abs_Cp_le hT hΦ hΦ2 _
  have hw_Sp : ∀ n ∈ primeRange X, |Sp Φ T (Real.log n)| ≤ W := fun n _ => h_Zeta23_PrimeSide_abs_Sp_le hT hΦ hΦ2 _
  have hb1 : |S1| ≤ 2 * C * W * Λ2 := by
    rw [hS1]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (2 * T) (fun k => acoef k * (‖c k‖ * Cm Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).2
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cm)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb2 : |S2| ≤ 2 * C * W * Λ2 := by
    rw [hS2]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (2 * T) (fun k => acoef k * (‖c k‖ * Sm Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).1
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sm)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb3 : |S3| ≤ 2 * C * W * Λ2 := by
    rw [hS3]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Cm Φ T (Real.log k))) (fun k => (c k).arg)).2
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cm)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb4 : |S4| ≤ 2 * C * W * Λ2 := by
    rw [hS4]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Sm Φ T (Real.log k))) (fun k => (c k).arg)).1
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sm)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb5 : |S5| ≤ 2 * C * W * Λ2 := by
    rw [hS5]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (2 * T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Cp Φ T (Real.log k))) (fun k => (c k).arg)).2
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cp)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb6 : |S6| ≤ 2 * C * W * Λ2 := by
    rw [hS6]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (2 * T) (fun k => acoef k * ‖c k‖) (fun k => acoef k * (‖c k‖ * Sp Φ T (Real.log k))) (fun k => (c k).arg)).1
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sp)).1
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb7 : |S7| ≤ 2 * C * W * Λ2 := by
    rw [hS7]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (T) (fun k => acoef k * (‖c k‖ * Cp Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).2
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Cp)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  have hb8 : |S8| ≤ 2 * C * W * Λ2 := by
    rw [hS8]
    have h := (h_Zeta23_ThmE_MV_real_ph hMV X (T) (fun k => acoef k * (‖c k‖ * Sp Φ T (Real.log k))) (fun k => acoef k * ‖c k‖) (fun k => (c k).arg)).1
    have hsz := (h_Zeta23_ThmE_MV_size_le₂ hC X hW0 hc1' (hb _ hw_Sp)).2
    have hfin := h.trans hsz
    rw [← hΛ2] at hfin
    exact hfin
  rw [hsplit]
  have habs : |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := by
    have t1 := abs_add_le S1 S2
    have t2 := abs_sub (S1 + S2) S3
    have t3 := abs_sub (S1 + S2 - S3) S4
    have t4 := abs_add_le (S1 + S2 - S3 - S4) S5
    have t5 := abs_add_le (S1 + S2 - S3 - S4 + S5) S6
    have t6 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6) S7
    have t7 := abs_sub (S1 + S2 - S3 - S4 + S5 + S6 - S7) S8
    linarith
  calc |S1 + S2 - S3 - S4 + S5 + S6 - S7 - S8|
      ≤ |S1| + |S2| + |S3| + |S4| + |S5| + |S6| + |S7| + |S8| := habs
    _ ≤ 8 * (2 * C * W * Λ2) := by linarith
    _ = 16 * C * W * Λ2 := by ring
end O1Chi
/-! ## The coprime g-sandwich (§5.4 with [eq:cheb2] restricted to (n,q)=1) -/
section SandwichChi

end SandwichChi
/-! ## Assembly: [prop:PP] for L(s,chi) -/
section Results

end Results
end ThmE
end Zeta23
