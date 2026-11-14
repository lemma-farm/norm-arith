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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_7aff1d62f8810e59c815_PPChi ====
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

set_option linter.unusedVariables false in
/-- Size bound with weights on BOTH slots: |w₁| ≤ 1, |w₂| ≤ W ⟹ the MV bound ≤ 2CW·ΣΛ²,
in both slot orders. -/
lemma MV_size_le₂ (hC : 0 ≤ C) (X : ℝ) {w₁ w₂ : ℕ → ℝ} {W : ℝ} (hW : 0 ≤ W)
    (hw₁ : ∀ n ∈ primeRange X, |w₁ n| ≤ 1) (hw₂ : ∀ n ∈ primeRange X, |w₂ n| ≤ W) 
    (h_Zeta23_PrimeSide_acoef_sq_mul_two_mul : ∀ {n : ℕ},
      1 ≤ n →
        Zeta23.PrimeSide.acoef n ^ 2 * (2 * (↑n : ℝ)) =
          2 * (ArithmeticFunction.vonMangoldt : ℕ → ℝ) n ^ 2)
    (h_Zeta23_PrimeSide_one_le_of_mem_primeRange : ∀ {X : ℝ} {n : ℕ}, n ∈ Zeta23.PrimeSide.primeRange X → 1 ≤ n)
    :
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ∧
    C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
        * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
      ≤ 2 * C * W * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := by
  set Λ2 := ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 with hΛ2
  have hΛ2nn : 0 ≤ Λ2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hbd : ∀ (w : ℕ → ℝ) (B : ℝ), 0 ≤ B → (∀ n ∈ primeRange X, |w n| ≤ B) →
      ∑ n ∈ primeRange X, (acoef n * w n) ^ 2 * (2 * n) ≤ B ^ 2 * (2 * Λ2) := by
    intro w B hB hw
    rw [hΛ2, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_pow, mul_comm (acoef n ^ 2), mul_assoc,
      h_Zeta23_PrimeSide_acoef_sq_mul_two_mul (h_Zeta23_PrimeSide_one_le_of_mem_primeRange hn)]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (sq_abs (w n)).symm ▸ pow_le_pow_left₀ (abs_nonneg _) (hw n hn) 2
  have h1 := hbd w₁ 1 zero_le_one hw₁
  have h2 := hbd w₂ W hW hw₂
  have hs1 : Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
      ≤ Real.sqrt (2 * Λ2) := by
    refine (Real.sqrt_le_sqrt h1).trans ?_
    rw [one_pow, one_mul]
  have hs2 : Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
      ≤ W * Real.sqrt (2 * Λ2) := by
    calc Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
        ≤ Real.sqrt (W ^ 2 * (2 * Λ2)) := Real.sqrt_le_sqrt h2
      _ = W * Real.sqrt (2 * Λ2) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hW]
  have hsq : Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2) = 2 * Λ2 :=
    Real.mul_self_sqrt (by positivity)
  constructor
  · calc C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
        ≤ C * Real.sqrt (2 * Λ2) * (W * Real.sqrt (2 * Λ2)) := by
          refine mul_le_mul ?_ hs2 (Real.sqrt_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hs1 hC
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring
  · calc C * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₂ n) ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, (acoef n * w₁ n) ^ 2 * (2 * n))
        ≤ C * (W * Real.sqrt (2 * Λ2)) * Real.sqrt (2 * Λ2) := by
          refine mul_le_mul ?_ hs1 (Real.sqrt_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hs2 hC
      _ = C * W * (Real.sqrt (2 * Λ2) * Real.sqrt (2 * Λ2)) := by ring
      _ = 2 * C * W * Λ2 := by rw [hsq]; ring
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
