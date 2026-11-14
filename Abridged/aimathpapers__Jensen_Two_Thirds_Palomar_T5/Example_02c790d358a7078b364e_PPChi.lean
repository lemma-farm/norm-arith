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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_02c790d358a7078b364e_PPChi ====
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

set_option linter.unusedVariables false in
/-- O₂-type bound, phase-free (mirror of abs_Aplus_le): for 0 < y + y',
|A⁺_ph(y,y',φ,φ')| ≤ (2/(y+y'))·∫Φ². -/
lemma abs_AplusPh_le (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {y y' : ℝ}
    (hyy : 0 < y + y') (φ φ' : ℝ) 
    (h_Zeta23_PrimeSide_abs_Jker_le : ∀ {θ : ℝ}, θ ≠ 0 → ∀ (c α β : ℝ), |Zeta23.PrimeSide.Jker θ c α β| ≤ 2 / |θ|)
    (h_Zeta23_ThmE_continuous_Jker_offset_ph : ∀ (θ y ψ T : ℝ),
      Continuous fun (x : ℝ) ↦
        Zeta23.PrimeSide.Jker θ (x * y - ψ) (Max.max (T - x) T) (Min.min (2 * T - x) (2 * T)))
    :
    |AplusPh Φ T y y' φ φ'| ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
  unfold AplusPh
  have hne : y + y' ≠ 0 := hyy.ne'
  have hint : IntegrableOn (fun x => Φ x ^ 2 *
      Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))) (Icc (-T) T) :=
    ((hΦ.pow 2).mul (h_Zeta23_ThmE_continuous_Jker_offset_ph _ _ _ _)).integrableOn_Icc
  calc |∫ x in Icc (-T) T, Φ x ^ 2 *
          Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))|
      ≤ ∫ x in Icc (-T) T, |Φ x ^ 2 *
          Jker (y + y') (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in Icc (-T) T, Φ x ^ 2 * (2 / (y + y')) := by
        apply setIntegral_mono_on hint.abs (hΦ2.integrableOn.mul_const _) measurableSet_Icc
        intro x _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have h := h_Zeta23_PrimeSide_abs_Jker_le hne (x * y - (φ + φ')) (max (T - x) T) (min (2 * T - x) (2 * T))
        rwa [abs_of_pos hyy] at h
    _ = 2 / (y + y') * ∫ x in Icc (-T) T, Φ x ^ 2 := by rw [integral_mul_const]; ring
    _ ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact setIntegral_le_integral hΦ2 (Filter.Eventually.of_forall fun x => sq_nonneg _)
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

end O1Chi
/-! ## The coprime g-sandwich (§5.4 with [eq:cheb2] restricted to (n,q)=1) -/
section SandwichChi

end SandwichChi
/-! ## Assembly: [prop:PP] for L(s,chi) -/
section Results

end Results
end ThmE
end Zeta23
