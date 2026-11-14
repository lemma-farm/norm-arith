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

end PairDecomp
/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/
section MVapply
variable {C : ℝ}

end MVapply
end PrimeSide
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_f228491de750c833cecd_PPChi ====
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
/-- A⁺ with phases. -/
def AplusPh (Φ : ℝ → ℝ) (T y y' φ φ' : ℝ) : ℝ :=
  ∫ x in Icc (-T) T,
    Φ x ^ 2 * Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))

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

set_option linter.unusedVariables false in
/-- 𝒪₂ for P_{X,c} (mirror of O2_estimate; weights ≤ 1, phase-free bound). -/
lemma O2_estimate_chi (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hc1 : ∀ n, ‖c n‖ ≤ 1) (X T : ℝ) 
    (h_Zeta23_ThmE_abs_AplusPh_le : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      Continuous Φ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
          ∀ {y y' : ℝ},
            0 < y + y' →
              ∀ (φ φ' : ℝ), |Zeta23.ThmE.AplusPh Φ T y y' φ φ'| ≤ 2 / (y + y') * ∫ (x : ℝ), Φ x ^ 2)
    (h_Zeta23_PrimeSide_acoef_nonneg : ∀ (n : ℕ), 0 ≤ Zeta23.PrimeSide.acoef n)
    (h_Zeta23_PrimeSide_acoef_eq_zero_or_two_le : ∀ {X : ℝ} {n : ℕ}, n ∈ Zeta23.PrimeSide.primeRange X → Zeta23.PrimeSide.acoef n = 0 ∨ 2 ≤ n)
    :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
        * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
      ≤ (∫ x, Φ x ^ 2) / Real.log 2 * (∑ n ∈ primeRange X, acoef n) ^ 2 := by
  have hW : 0 ≤ ∫ x, Φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hper : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      |(acoef n * ‖c n‖) * (acoef m * ‖c m‖)
          * AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
        ≤ acoef n * acoef m * ((∫ x, Φ x ^ 2) / Real.log 2) := by
    intro n hn m hm
    rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg (h_Zeta23_PrimeSide_acoef_nonneg n) (norm_nonneg _)),
      abs_of_nonneg (mul_nonneg (h_Zeta23_PrimeSide_acoef_nonneg m) (norm_nonneg _))]
    rcases h_Zeta23_PrimeSide_acoef_eq_zero_or_two_le hn with h0 | hn2
    · simp [h0]
    rcases h_Zeta23_PrimeSide_acoef_eq_zero_or_two_le hm with h0 | hm2
    · simp [h0]
    have hwn : acoef n * ‖c n‖ ≤ acoef n := by
      calc acoef n * ‖c n‖ ≤ acoef n * 1 := mul_le_mul_of_nonneg_left (hc1 n) (h_Zeta23_PrimeSide_acoef_nonneg n)
        _ = acoef n := mul_one _
    have hwm : acoef m * ‖c m‖ ≤ acoef m := by
      calc acoef m * ‖c m‖ ≤ acoef m * 1 := mul_le_mul_of_nonneg_left (hc1 m) (h_Zeta23_PrimeSide_acoef_nonneg m)
        _ = acoef m := mul_one _
    have hyn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn2)
    have hym : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) (by exact_mod_cast hm2)
    have hpos : 0 < Real.log n + Real.log m := by linarith
    have hA : |AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
        ≤ (∫ x, Φ x ^ 2) / Real.log 2 := by
      calc |AplusPh Φ T (Real.log n) (Real.log m) (c n).arg (c m).arg|
          ≤ 2 / (Real.log n + Real.log m) * ∫ x, Φ x ^ 2 := h_Zeta23_ThmE_abs_AplusPh_le hΦ hΦ2 hpos _ _
        _ ≤ 2 / (2 * Real.log 2) * ∫ x, Φ x ^ 2 := by gcongr; linarith
        _ = (∫ x, Φ x ^ 2) / Real.log 2 := by field_simp
    exact mul_le_mul (mul_le_mul hwn hwm (mul_nonneg (h_Zeta23_PrimeSide_acoef_nonneg m) (norm_nonneg _))
      (h_Zeta23_PrimeSide_acoef_nonneg n)) hA (abs_nonneg _) (mul_nonneg (h_Zeta23_PrimeSide_acoef_nonneg n) (h_Zeta23_PrimeSide_acoef_nonneg m))
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hper n hn m hm) ?_
  refine le_of_eq ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring
end Estimates
/-! ## 𝒪₁ for P_{X,c} -/
section O1Chi
variable {Φ : ℝ → ℝ} {T : ℝ}

end O1Chi
/-! ## The coprime g-sandwich (§5.4 with [eq:cheb2] restricted to (n,q)=1) -/
section SandwichChi

end SandwichChi
/-! ## Assembly: [prop:PP] for L(s,chi) -/
section Results

end Results
end ThmE
end Zeta23
