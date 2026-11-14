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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.Defs ====
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

/-! ## 1. Scalars depending on T only  [Notation], [eq:RvM], [eq:Fdef] -/
/-- l := log(T/2π)  [Notation]. -/
def l (T : ℝ) : ℝ := Real.log (T / (2 * Real.pi))

def PiX (X : ℝ) (τ : ℝ) : ℝ :=
  let s : ℂ := 1 / 2 + Complex.I * τ
  1 / (2 * Real.pi * (1 / 4 + τ ^ 2)) + (1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re

namespace ZeroConfig


end ZeroConfig
/-! ## 4. The test family  [subsec:family] -/

namespace Params
variable  (T : ℝ)

end Params
/-! ### The zero-side matrices  [eq:Gdef] first expression, [eq:AE], §4 Block structure -/
namespace ZeroConfig

end ZeroConfig
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.Hypotheses ====
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
structure ChebyshevMertens : Prop where
  cheb1a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ≤ C * x
  cheb1b : ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x
  cheb1c : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤ C * Real.sqrt x / Real.log x
  cheb1d : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ C * x * Real.log x
  cheb2a : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n - Real.log x ^ 2 / 2| ≤ C * Real.log x
  cheb2b : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x →
    |∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n) - Real.log x ^ 3 / 6|
      ≤ C * Real.log x ^ 2
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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.PrimeSideA.Defs ====
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
/-- The free scalar parameters: height `T`, bandwidth ratio `λ` (`0<λ≤1`), ramp width `w`
([eq:wrange] `1 ≤ w ≤ L/8`; §6 takes `w = 1`).  (Zeta23/Defs.lean's `Params` = (ϱ, λ, w) with `T`
separate; the bridge is `fun (P : Zeta23.Params) T => ⟨T, P.lam, P.w⟩` and then `L, X, d, tau, h`
below agree with `P.L T, P.X T, P.d T, P.tau T, P.hgrid T` by `rfl`.) -/
structure Setting where
  T : ℝ
  lam : ℝ
  w : ℝ
namespace Setting
variable (p : Setting)
/-- `l := log(T/2π)` [Notation] — this IS `Zeta23.l p.T`. -/
abbrev l : ℝ := Zeta23.l p.T
def L : ℝ := p.lam * Zeta23.l p.T
/-- `X := e^L = (T/2π)^λ` [Notation] (same body as `Zeta23.Params.X`). -/
def X : ℝ := Real.exp p.L
/-- Grid spacing `h := 2π/L` [§2.2] (= `Zeta23.Params.hgrid`). -/
def h : ℝ := 2 * Real.pi / p.L

/-- Grid points `τ_k := T + k h  (k ∈ ℤ)` [eq:fk] (= `Zeta23.Params.tau`). -/
def tau (k : ℤ) : ℝ := p.T + k * p.h

end Setting
/-! ## The prime-power sum: notation of §5 for `Zeta23.PX` [eq:Pdef, §2.1] -/
/-- `a_n := Λ(n) n^{-1/2}` [Notation, §1.4]. -/
def acoef (n : ℕ) : ℝ := (Λ n : ℝ) / Real.sqrt n
def primeRange (X : ℝ) : Finset ℕ := Finset.Ioc 0 ⌊X⌋₊
structure LocalFun where
  /-- `φ̂` restricted to ℝ (real-valued: φ is real and even) [§2.2]. -/
  phiHat : ℝ → ℝ
  /-- `Φ := (φ²)^` restricted to ℝ (real, even, entire) [eq:PhigA]. -/
  Phi : ℝ → ℝ
  /-- `A_φ := φ ⋆ φ`, `(v⋆v)(y) := ∫ v(u)v(u+y)du` [eq:PhigA]. -/
  Aphi : ℝ → ℝ
  /-- `g := φ² ⋆ φ²` [eq:PhigA]. -/
  g : ℝ → ℝ
  /-- `a := L⁻¹ ∫ φ²` [eq:abdef]. -/
  a : ℝ
  /-- `b := L⁻¹ ∫ φ⁴` [eq:abdef]. -/
  b : ℝ
variable (p : Setting) (F : LocalFun)
def Mform (Φ : ℝ → ℝ) (T : ℝ) (u₁ u₂ : ℝ → ℝ) : ℝ :=
  ∫ q in (Set.Icc T (2 * T)) ×ˢ (Set.Icc T (2 * T)), (Φ (q.1 - q.2)) ^ 2 * u₁ q.1 * u₂ q.2
end PrimeSide
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.PrimeSideB.PPKernel ====
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

/-- The `τ'`-window at offset `x`:  `I ∩ (I − x) = [max(T−x, T), min(2T−x, 2T)]`
(§5.4: "= [T + x⁻, 2T − x⁺] for |x| < T", empty for `|x| > T`). -/
def Ix (T x : ℝ) : Set ℝ := Icc (max (T - x) T) (min (2 * T - x) (2 * T))

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
/-- The "−" (difference-frequency) inner integral at offset x:  J(y−y', xy; I∩(I−x)). -/
def JmK (T y y' x : ℝ) : ℝ := Jker (y - y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
def Aminus (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ := ∫ x in Icc (-T) T, Φ x ^ 2 * JmK T y y' x

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

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.PrimeSideA.Basic ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].
/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/
noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
namespace Zeta23
namespace PrimeSide
/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/
/-- ψ(r) := min(L, 2/|r|, c_ϱ/(w r²)) [eq:psidef], with the r = 0 guard
(= `Zeta23.Params.psi` / `Taper.psi'` by `rfl` under the bridge).  Majorant for both `φ̂` and `Φ`. -/
def psiA (cϱ : ℝ) (p : Setting) (r : ℝ) : ℝ :=
  if r = 0 then p.L else min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2)))

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}

end MformLemmas
/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/
section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}
end SupBound
section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

structure LocalHypsCore (cϱ : ℝ) (p : Setting) (F : LocalFun) : Prop where
  /-- [eq:phinorms] `c_ϱ ≥ 4`. -/
  four_le_cϱ : 4 ≤ cϱ
  /-- `0 < λ ≤ 1` [Notation]. -/
  lam_pos : 0 < p.lam
  lam_le_one : p.lam ≤ 1
  /-- [eq:wrange] `1 ≤ w ≤ L/8` (forces `L ≥ 8`). -/
  one_le_w : 1 ≤ p.w
  w_le : p.w ≤ p.L / 8
  /-- "T is large": `l ≥ 1`, i.e. `T ≥ 2πe`. -/
  one_le_l : 1 ≤ p.l
  /-- φ̂ real-analytic facts: continuity; evenness (φ even) [§2.2 "φ̂ and Φ are real, even, entire"]. -/
  phiHat_cont : Continuous F.phiHat
  phiHat_even : ∀ r, F.phiHat (-r) = F.phiHat r
  /-- [eq:psidef] `|φ̂(r)| ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`, split into three division-free bounds. -/
  phiHat_le_L : ∀ r, |F.phiHat r| ≤ p.L
  phiHat_le_inv : ∀ r, |F.phiHat r| * |r| ≤ 2
  phiHat_le_sq : ∀ r, |F.phiHat r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] (`φ̂² ≤ ψ² ≤ min(L², c_ϱ²/(w²r⁴))`), and
  [eq:psiints] in the packaged form `∫ φ̂(r)²|r| dr ≤ ∫ ψ²|r| = 8 + 8 log(c_ϱL/4w)` (§2.2, used at
  §5.2 "∫ φ̂(r)²|r| dr ≪ log L"). -/
  phiHat_sq_integrable : Integrable (fun r => F.phiHat r ^ 2)
  phiHat_sq_mul_abs_integrable : Integrable (fun r => F.phiHat r ^ 2 * |r|)
  integral_phiHat_sq_mul_abs_le :
    ∫ r, F.phiHat r ^ 2 * |r| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- also from [eq:psidef]: `φ̂(r)²r² ≤ min(4, (c_ϱ/w)²/r²)`, so `∫ φ̂(r)² r² dr ≤ 8 + 2(c_ϱ/w)²`
  (used for the `|r| > τ_k/2` tails at §5.2 in place of the paper's sharper r⁻⁴ bound). -/
  phiHat_sq_mul_sq_integrable : Integrable (fun r => F.phiHat r ^ 2 * r ^ 2)
  integral_phiHat_sq_mul_sq_le : ∫ r, F.phiHat r ^ 2 * r ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `∫ φ̂(r)² dr = 2π ∫ φ² = 2π a L` [prop:trace proof, §5.2; Plancherel in the paper's
  convention `∫ f ḡ = (2π)⁻¹ ∫ f̂ conj ĝ` + eq:abdef]. -/
  phiHat_sq_integral : ∫ r, F.phiHat r ^ 2 = 2 * π * F.a * p.L
  /-- `φ̂² = Â_φ` on ℝ [§2.2] + Fourier inversion, in the real form used at §5.2:
  `∫ φ̂(r)² cos(ry) dr = 2π A_φ(y)` (`φ̂²` even, `A_φ` even, continuous, supported in `[−L,L]`). -/
  phiHat_sq_fourier : ∀ y, ∫ r, F.phiHat r ^ 2 * Real.cos (r * y) = 2 * π * F.Aphi y
  /-- window-generic remnant of [eq:gbounds]: `g ≥ 0` and `g ≤ A_φ ≤ (L−|y|)₊`
  (the flat-top plateau lower bound `(L−2w−|y|)₊ ≤ g` is NOT here — see §7.1). -/
  g_nonneg : ∀ y, 0 ≤ F.g y
  g_le_Aphi : ∀ y, F.g y ≤ F.Aphi y
  Aphi_le : ∀ y, F.Aphi y ≤ max (p.L - |y|) 0
  /-- Φ facts: `Φ` is C¹ (indeed entire), even [§2.2]. -/
  Phi_contDiff : ContDiff ℝ 1 F.Phi
  Phi_even : ∀ r, F.Phi (-r) = F.Phi r
  /-- [eq:psidef] `|Φ(r)| ≤ ψ(r)`, three division-free bounds. -/
  Phi_le_L : ∀ r, |F.Phi r| ≤ p.L
  Phi_le_inv : ∀ r, |F.Phi r| * |r| ≤ 2
  Phi_le_sq : ∀ r, |F.Phi r| * r ^ 2 ≤ cϱ / p.w
  /-- Integrability consequences of [eq:psidef] for Φ, and [eq:psiints] packaged as
  `∫ Φ(x)²|x| dx ≤ 8 + 8 log(c_ϱL/4w)` (§5.4 "∫Φ(x)²|x|dx ≪ log L (by (eq:psidef), (eq:psiints))"). -/
  Phi_sq_integrable : Integrable (fun x => F.Phi x ^ 2)
  Phi_sq_mul_abs_integrable : Integrable (fun x => F.Phi x ^ 2 * |x|)
  integral_Phi_sq_mul_abs_le :
    ∫ x, F.Phi x ^ 2 * |x| ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
  /-- second moment of `Φ²` (same [eq:psidef] path as the `φ̂` version; needed against the
  `10r²/t` term of `mu_increment_bound` in [prop:mumu]). -/
  Phi_sq_mul_sq_integrable : Integrable (fun x => F.Phi x ^ 2 * x ^ 2)
  integral_Phi_sq_mul_sq_le : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * (cϱ / p.w) ^ 2
  /-- `Φ(0) = aL` [§2.2]. -/
  Phi_zero : F.Phi 0 = F.a * p.L
  /-- `∫_ℝ Φ² = 2π g(0) = 2π b L` [§2.2]. -/
  Phi_sq_integral : ∫ x, F.Phi x ^ 2 = 2 * π * F.b * p.L
  /-- [eq:Phi2FT] `∫_ℝ Φ(x)² e^{ixy} dx = 2π g(y)` (§5.4), real form (`Φ²`, `g` even). -/
  Phi_sq_fourier : ∀ y, ∫ x, F.Phi x ^ 2 * Real.cos (x * y) = 2 * π * F.g y
  /-- [lem:poisson] (★) `Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L Φ(τ−τ')` (§2.2). -/
  poisson : ∀ τ τ', HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k))
    (p.L * F.Phi (τ - τ'))
  /-- window-generic remnant of [eq:abdef]: `1/2 ≤ b ≤ a ≤ 1` (the flat-top `1 − 2w/L ≤ b`
  is NOT here; 1/2 suffices for every positivity/division use and holds for the
  Montgomery–Taylor window). -/
  b_ge_half : 1 / 2 ≤ F.b
  b_le_a : F.b ≤ F.a
  a_le_one : F.a ≤ 1
  /-- [eq:psidef] in majorant form, with the [eq:psiints] integrals (`Ψ₀ = 4 + 2log(c_ϱL/4w)`,
  `∫ψ² ≤ 8L`) — fields match `Zeta23.Params.psi'_integrable / psi'_sq_integrable /
  integral_psi'_Ioi_le / integral_psi'_sq_le` in Zeta23/Taper.lean (consumed by [lem:ends]). -/
  psi_integrable : Integrable (psiA cϱ p)
  psi_sq_integrable : Integrable (fun r => psiA cϱ p r ^ 2)
  integral_psi_Ioi_le : ∫ r in Set.Ioi 0, psiA cϱ p r ≤ 4 + 2 * Real.log (cϱ * p.L / (4 * p.w))
  integral_psi_sq_le : ∫ r, psiA cϱ p r ^ 2 ≤ 8 * p.L
  /-- `|φ̂| ≤ ψ` and `|Φ| ≤ ψ` [eq:psidef] in the majorant form used by [lem:ends]. -/
  phiHat_le_psi : ∀ r, |F.phiHat r| ≤ psiA cϱ p r
  Phi_le_psi : ∀ r, |F.Phi r| ≤ psiA cϱ p r
  /-- Π_X is continuous and [eq:PiPfacts] `|Π_X(τ)| ≤ 3√X/(1+|τ|)` (§2.1), for the concrete
  `Zeta23.PiX X` [eq:Pidef] — see `PiX_bound` (holds for all `X ≥ 1`) and `PiX_continuous`. -/
  PiX_cont : Continuous (Zeta23.PiX p.X)
  PiX_bound : ∀ τ, |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / (1 + |τ|)
set_option linter.unusedVariables false in
axiom _root_.Zeta23.PrimeSide.LocalHypsCore.eight_le_L : ∀ {cϱ : ℝ} {p : Zeta23.PrimeSide.Setting} {F : Zeta23.PrimeSide.LocalFun},
  Zeta23.PrimeSide.LocalHypsCore cϱ p F → 8 ≤ p.L

set_option linter.unusedVariables false in
axiom _root_.Zeta23.PrimeSide.LocalHypsCore.integral_Phi_sq_le : ∀ {cϱ : ℝ} {p : Zeta23.PrimeSide.Setting} {F : Zeta23.PrimeSide.LocalFun},
  Zeta23.PrimeSide.LocalHypsCore cϱ p F → ∫ (x : ℝ), F.Phi x ^ 2 ≤ 2 * Real.pi * p.L

end Regime
/-! ### Elementary lemmas for [prop:trace] -/
section TraceLemmas
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}
end TraceLemmas
/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/
section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}
end TraceAnalytic
end PrimeSide
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.PrimeSideB.PP ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Prime side, part B/PP — paper §5 [prop:PP] (§5.4): the term 𝓜[P_X,P_X]

Consumed by `Zeta23/PrimeSideB.lean` ([thm:traces]) through the three results at the bottom of
this file:

* `prop_PP`        [prop:PP] first form (§5.4):
      𝓜[P_X,P_X] = (T/π) Σ_{n≤X} Λ(n)²/n · g(log n) + O(L²X);
* `sum_a2g_lower`, `sum_a2g_upper`  (§5.4, the "Finally" step, from [eq:gbounds]+[eq:cheb2]):
      (L−2w)³/6 − C·L² ≤ Σ_{n≤X} Λ(n)²/n · g(log n) ≤ L³/6 + C·L²,
  which give the paper's second form  𝓜[P_X,P_X] = (TL³/6π)(1+O(w/L)) + O(L²X).

Everything is stated in the abstract prime-side layer (Zeta23/PrimeSideA/Defs.lean +
`LocalHyps`/`EventuallyAt` of Zeta23/PrimeSideA.lean): `p : Setting` = (T, λ, w), `F : LocalFun` =
the taper data (φ̂, Φ, A_φ, g, a, b) subject to `LocalHyps cϱ p F` (the facts [eq:psidef],
[eq:abdef], [eq:gbounds], [eq:Phi2FT], …, each a proof obligation of Zeta23/Taper.lean, not an
axiom).  `P_X` is `Zeta23.PX` [eq:Pdef] of Zeta23/Defs.lean and 𝓜[·,·] is
`Zeta23.PrimeSide.Mform` (§5.4).  Analytic inputs: H-cheb = `Zeta23.ChebyshevMertens` [lem:cheb]
and H-MV = `Zeta23.MVHilbert` [lem:MV] from Zeta23/Hypotheses.lean (fields of `PaperInputs`).

## Proof route (paper §5.4, reorganised for Lean; labels as in the paper)
1. Bilinearity:  𝓜[P_X,P_X] = π⁻² Σ_{n,m≤X} a_n a_m 𝓜[cos(·y_n), cos(·y_m)],  a_n = Λ(n)/√n, y_n = log n.
2. Shear `(τ,τ') ↦ (x,τ') := (τ−τ',τ')` (measure-preserving on ℝ²) + Fubini  (§5.4 "Substituting
   τ = τ'+x … τ' ranges over I∩(I−x) = [T+x⁻, 2T−x⁺]"):
      𝓜[u,v] = ∫_{|x|≤T} Φ(x)² ∫_{max(T,T−x)}^{min(2T,2T−x)} u(τ'+x) v(τ') dτ' dx.
3. cos A cos B = ½cos(A−B) + ½cos(A+B): inner integral = ½J(xy_n, y_n−y_m) + ½J(xy_n, y_n+y_m),
   J(c,θ) := ∫_α^β cos(c+θτ')dτ' = (β−α)cos c (θ=0), = [sin(c+θβ)−sin(c+θα)]/θ (θ≠0), |J| ≤ 2/|θ|.
4. 𝒟 (n=m, "−"):  ½∫_{|x|≤T}Φ²(T−|x|)cos(xy_n) = πT g(y_n) + O(∫Φ²|x|)   by [eq:Phi2FT];
   𝒪₂ (all n,m, "+"):  ≤ (∫Φ²)(Σa_n)²/(2π² log 2) ≪ XL                        by [eq:cheb1];
   𝒪₁ (n≠m, "−"):  an explicit combination of 8 sums Σ_{n≠m} x_n conj(z_m)/(y_n−y_m) with
   |x_n| = a_n, |z_m| ≤ a_m ∫Φ², each ≤ C_MV·(∫Φ²)·Σ a_n²/δ_n with δ_n = 1/(2n) [eq:deltan] ≪ L²X by H-MV
   and [eq:cheb1] (Σ Λ(n)² ≪ X log X).
Constants: the paper's O(L²X) constant (and the λ=1 "18/L" sharpness) is not load-bearing;
we prove ∃ C.
-/
noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
namespace Zeta23
namespace PrimeSide
variable {cϱ lam : ℝ}
/-! ## The main-term sum  Σ_{n≤X} a_n² g(y_n) = Σ_{n≤X} Λ(n)²/n · g(log n)   (§5.4) -/
section Basics
variable {p : Setting} {F : LocalFun}
set_option linter.unusedVariables false in
axiom _root_.Zeta23.PrimeSide.Setting.log_X : ∀ (p : Zeta23.PrimeSide.Setting), Real.log p.X = p.L

set_option linter.unusedVariables false in
axiom _root_.Zeta23.PrimeSide.LocalHypsCore.two_le_X : ∀ {cϱ : ℝ} {p : Zeta23.PrimeSide.Setting} {F : Zeta23.PrimeSide.LocalFun},
  Zeta23.PrimeSide.LocalHypsCore cϱ p F → 2 ≤ p.X
set_option linter.unusedVariables false in
axiom _root_.Zeta23.PrimeSide.LocalHypsCore.L_le_X : ∀ {cϱ : ℝ} {p : Zeta23.PrimeSide.Setting} {F : Zeta23.PrimeSide.LocalFun},
  Zeta23.PrimeSide.LocalHypsCore cϱ p F → p.L ≤ p.X
end Basics
/-! ## The g-sandwich  (§5.4)

"Finally, by [eq:gbounds] and [eq:cheb2] (note a_n² = Λ(n)²/n),
  (L−2w)³/6 + O(L²) = Σ_{n≤Xe^{−2w}} a_n²(L−2w−y_n) ≤ Σ_{n≤X} a_n² g(y_n) ≤ Σ_{n≤X} a_n²(L−y_n) = L³/6+O(L²)". -/
section Sandwich
variable {p : Setting} {F : LocalFun}
end Sandwich
/-! ## Assembly of [prop:PP]  (§5.4) -/
section Assembly
variable {Φ : ℝ → ℝ} {T : ℝ}

end Assembly
/-! ## Results consumed by PrimeSideB.lean -/
section Results
end Results
end PrimeSide
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Dependencies.veff4e711c6f1.Zeta23.ThmE.Hypotheses ====
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Hypotheses.lean — Theorem E (Dirichlet L-functions), the χ-dependent densities and the
published inputs restated for L(s,χ).

Canonical text: the paper §7.2 [subsec:dirichlet], [thm:E] and its proof, items (i)–(iii), VERBATIM:
"(i) Explicit formula: with κ = (1−χ(−1))/2, Proposition prop:EF holds for
 W_χ(f,g) := Σ_ρ m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ)) (zeros of L(s,χ)) with ν_X replaced by
 ν_{X,χ} := μ_χ + P_{X,χ},  μ_χ(τ) := (1/2π)[log(q/π) + Re Γ′/Γ(1/4 + κ/2 + iτ/2)],
 P_{X,χ}(τ) := −(1/π) Re Σ_{n≤X} Λ(n)χ(n) n^{−1/2−iτ}, and no pole term (Π_X ≡ 0); the derivation of
 Appendix A applies to [IK04, Theorem 5.12] for L(s,χ). Since ν_{X,χ} is real, G is again real
 symmetric. (ii) Zero side: the multiset of zeros of L(s,χ) is invariant under ρ ↦ 1−ρ̄ with
 multiplicities (functional equation χ ↔ χ̄ composed with conj L(conj s,χ) = L(s,χ̄)), all zeros have
 0<β<1, and N_χ(t+1) − N_χ(t) ≪_q log(t+3); Section 4 is otherwise verbatim. (iii) Prime side:
 |Λ(n)χ(n)| = Λ(n)·1_{(n,q)=1}, so Lemma lem:cheb holds for these coefficients with O_q(·) errors
 (finitely many primes removed); … μ_χ = (1/2π) log(q|τ|/2π) + O(τ⁻²) satisfies (eq:mufacts)–(eq:muints)
 with ℓ₁ replaced by ℓ_{1,χ} := log(qT/2π) + 2log2 − 1, and λ₁ = L/ℓ_{1,χ} → λ as q is fixed."

This file is ζ-free AND L-free: it defines the densities μ_χ, P_{X,χ}, ν_{X,χ}
as explicit real functions of (κ, q, the coefficient character values) and states the hypotheses
for an ABSTRACT `ZeroConfig`; only `Zeta23/ThmE/Statement.lean` mentions Mathlib's
`DirichletCharacter.LFunction`.  Everything the paper derives from these inputs is proved in the sibling files;
this file only states the inputs.
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set
noncomputable section
namespace Zeta23
namespace ThmE
/-! ## 1. The χ-dependent scalars and densities  ([thm:E] proof (i), (iii)) -/
def PXc (c : ℕ → ℂ) (X : ℝ) (τ : ℝ) : ℝ :=
  -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
    ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re
structure CoeffOK (q : ℕ) (c : ℕ → ℂ) : Prop where
  norm_le : ∀ n, ‖c n‖ ≤ 1
  vanish : ∀ n, ¬ Nat.Coprime n q → c n = 0
/-- Unimodular coefficient sequences: additionally `‖c n‖ = 1` exactly on `(n,q) = 1`, `n > 0`
(true for a primitive χ).  Needed wherever the main term is TWO-sided ([prop:PP]'s diagonal uses
`|χ(n)|² = 1`); the four upper-bound statements only need `CoeffOK`. -/
structure CoeffUnimodular (q : ℕ) (c : ℕ → ℂ) : Prop extends CoeffOK q c where
  norm_eq : ∀ n, 0 < n → Nat.Coprime n q → ‖c n‖ = 1
/-! ## 2. The published inputs, restated for L(s,χ)  (abstract zero configuration Z) -/

section PXcUnfold
end PXcUnfold
/-! ## Uniform-constant ("Bounded") variants, for the hybrid range [rem:otherL](i):
same fields as `GammaFactsChi` / `ChebyshevMertensCoprime`
but with every existential constant replaced by the given bound, so families of characters can
carry ONE constant uniformly in q. -/

end ThmE
end Zeta23

end
end

-- ==== Examples.aimathpapers__Jensen_Two_Thirds_Palomar_T5.Examples.Example_c3e7a63ab594bf6e08fe_PPChi ====
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
/-- Sum_{n ≤ X, (n,q)=1} Lambda(n)²/n · g(log n) — the [prop:PP] main-term sum for L(s,chi)
(index set = ChebyshevMertensCoprime's). -/
def sumA2gCoprime (q : ℕ) (X : ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => Nat.Coprime n q),
    (Λ n : ℝ) ^ 2 / n * g (Real.log n)

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

end Estimates
/-! ## 𝒪₁ for P_{X,c} -/
section O1Chi
variable {Φ : ℝ → ℝ} {T : ℝ}

end O1Chi
/-! ## The coprime g-sandwich (§5.4 with [eq:cheb2] restricted to (n,q)=1) -/
section SandwichChi
variable {p : Setting} {F : LocalFun}
end SandwichChi
/-! ## Assembly: [prop:PP] for L(s,chi) -/
section Results
set_option linter.unusedVariables false in
/-- **prop_PP_chi, q-uniform form** (hybrid range, [rem:otherL](i)): the same constant and
threshold for every modulus and unimodular coefficient sequence — the ∃ C T₀ sit outside (q, c).
(The constant does not depend on (q, c); unimodularity enters only through the norm bound and the
diagonal identity.  `prop_PP_chi` below is the (q, c)-specialisation of this theorem.) -/
theorem prop_PP_chi_uniform (hcheb : Zeta23.ChebyshevMertens) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hlam : 0 < lam ∧ lam ≤ 1) 
    (h_Zeta23_ThmE_diag_estimate_chi : ∀ {c : ℕ → ℂ} {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
            MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2 * |x|) MeasureTheory.MeasureSpace.volume →
              ∀ {g : ℝ → ℝ},
                (∀ (y : ℝ), ∫ (x : ℝ), Φ x ^ 2 * Real.cos (x * y) = 2 * Real.pi * g y) →
                  (∀ (n : ℕ), ‖c n‖ ≤ 1) →
                    ∀ (X : ℝ),
                      |1 / (2 * Real.pi ^ 2) *
                              ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                                (Zeta23.PrimeSide.acoef n * ‖c n‖) ^ 2 *
                                  Zeta23.PrimeSide.Aminus Φ T (Real.log (↑n : ℝ)) (Real.log (↑n : ℝ)) -
                            T / Real.pi *
                              ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                                Zeta23.PrimeSide.acoef n ^ 2 * ‖c n‖ ^ 2 * g (Real.log (↑n : ℝ))| ≤
                        (1 / (2 * Real.pi ^ 2) *
                            ∑ n ∈ Zeta23.PrimeSide.primeRange X, Zeta23.PrimeSide.acoef n ^ 2) *
                          ∫ (x : ℝ), Φ x ^ 2 * |x|)
    (h_Zeta23_PrimeSide_acoef_nonneg : ∀ (n : ℕ), 0 ≤ Zeta23.PrimeSide.acoef n)
    (h_Zeta23_ThmE_sum_w_eq_sumA2gCoprime : ∀ {q : ℕ} {c : ℕ → ℂ},
      Zeta23.ThmE.CoeffUnimodular q c →
        ∀ (X : ℝ) (g : ℝ → ℝ),
          ∑ n ∈ Zeta23.PrimeSide.primeRange X,
              Zeta23.PrimeSide.acoef n ^ 2 * ‖c n‖ ^ 2 * g (Real.log (↑n : ℝ)) =
            Zeta23.ThmE.sumA2gCoprime q X g)
    (h_Zeta23_PrimeSide_Setting_le_X_of_T : ∀ {p : Zeta23.PrimeSide.Setting},
      0 < p.lam → ∀ {x₀ : ℝ}, 2 * Real.pi * Real.exp (|x₀| / p.lam) ≤ p.T → x₀ ≤ p.X)
    (h_Zeta23_PrimeSide_acoef_sq : ∀ (n : ℕ), Zeta23.PrimeSide.acoef n ^ 2 = (ArithmeticFunction.vonMangoldt : ℕ → ℝ) n ^ 2 / (↑n : ℝ))
    (h_Zeta23_ThmE_Mform_PXc_PXc : ∀ {Φ : ℝ → ℝ} {T : ℝ},
      0 ≤ T →
        Continuous Φ →
          ∀ (c : ℕ → ℂ) (X : ℝ),
            Zeta23.PrimeSide.Mform Φ T (Zeta23.ThmE.PXc c X) (Zeta23.ThmE.PXc c X) =
              1 / (2 * Real.pi ^ 2) *
                ((∑ n ∈ Zeta23.PrimeSide.primeRange X,
                      (Zeta23.PrimeSide.acoef n * ‖c n‖) ^ 2 *
                        Zeta23.PrimeSide.Aminus Φ T (Real.log (↑n : ℝ)) (Real.log (↑n : ℝ)) +
                    ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                      ∑ m ∈ Zeta23.PrimeSide.primeRange X,
                        if n = m then 0
                        else
                          Zeta23.PrimeSide.acoef n * ‖c n‖ * (Zeta23.PrimeSide.acoef m * ‖c m‖) *
                            Zeta23.ThmE.AminusPh Φ T (Real.log (↑n : ℝ)) (Real.log (↑m : ℝ)) (c n).arg
                              (c m).arg) +
                  ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                    ∑ m ∈ Zeta23.PrimeSide.primeRange X,
                      Zeta23.PrimeSide.acoef n * ‖c n‖ * (Zeta23.PrimeSide.acoef m * ‖c m‖) *
                        Zeta23.ThmE.AplusPh Φ T (Real.log (↑n : ℝ)) (Real.log (↑m : ℝ)) (c n).arg
                          (c m).arg))
    (h_Zeta23_ThmE_O1_bound_chi : ∀ {c : ℕ → ℂ} {Φ : ℝ → ℝ} {T C : ℝ},
      Zeta23.MVHilbert C →
        0 ≤ C →
          0 ≤ T →
            Continuous Φ →
              MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
                (∀ (n : ℕ), ‖c n‖ ≤ 1) →
                  ∀ (X : ℝ),
                    |∑ n ∈ Zeta23.PrimeSide.primeRange X,
                          ∑ m ∈ Zeta23.PrimeSide.primeRange X,
                            if n = m then 0
                            else
                              Zeta23.PrimeSide.acoef n * ‖c n‖ * (Zeta23.PrimeSide.acoef m * ‖c m‖) *
                                Zeta23.ThmE.AminusPh Φ T (Real.log (↑n : ℝ)) (Real.log (↑m : ℝ))
                                  (c n).arg (c m).arg| ≤
                      (16 * C * ∫ (x : ℝ), Φ x ^ 2) *
                        ∑ n ∈ Zeta23.PrimeSide.primeRange X,
                          (ArithmeticFunction.vonMangoldt : ℕ → ℝ) n ^ 2)
    (h_Zeta23_ThmE_O2_estimate_chi : ∀ {c : ℕ → ℂ} {Φ : ℝ → ℝ},
      Continuous Φ →
        MeasureTheory.Integrable (fun (x : ℝ) ↦ Φ x ^ 2) MeasureTheory.MeasureSpace.volume →
          (∀ (n : ℕ), ‖c n‖ ≤ 1) →
            ∀ (X T : ℝ),
              |∑ n ∈ Zeta23.PrimeSide.primeRange X,
                    ∑ m ∈ Zeta23.PrimeSide.primeRange X,
                      Zeta23.PrimeSide.acoef n * ‖c n‖ * (Zeta23.PrimeSide.acoef m * ‖c m‖) *
                        Zeta23.ThmE.AplusPh Φ T (Real.log (↑n : ℝ)) (Real.log (↑m : ℝ)) (c n).arg
                          (c m).arg| ≤
                (∫ (x : ℝ), Φ x ^ 2) / Real.log 2 *
                  (∑ n ∈ Zeta23.PrimeSide.primeRange X, Zeta23.PrimeSide.acoef n) ^ 2)
    :
    ∃ C T₀ : ℝ, ∀ (q : ℕ) (c : ℕ → ℂ), CoeffUnimodular q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCore cϱ p F →
      |Mform F.Phi p.T (PXc c p.X) (PXc c p.X) - p.T / π * sumA2gCoprime q p.X F.g|
        ≤ C * (p.L ^ 2 * p.X) := by
  obtain ⟨CMV, hCMV, hMV⟩ := hMV
  obtain ⟨x₀, h1b⟩ := hcheb.cheb1b
  obtain ⟨C1d, h1d⟩ := hcheb.cheb1d
  obtain ⟨C2a, h2a⟩ := hcheb.cheb2a
  refine ⟨(1 / (2 * π ^ 2)) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|) + 16 * CMV * (2 * π) * |C1d|
      + 2 * π / Real.log 2 * 9),
    max (2 * π * Real.exp (|x₀| / lam)) 1, fun q c hc p F hplam hT hF => ?_⟩
  have hc1 : ∀ n, ‖c n‖ ≤ 1 := hc.toCoeffOK.norm_le
  have hT1 : 1 ≤ p.T := le_trans (le_max_right _ _) hT
  have hT0 : 0 ≤ p.T := by linarith
  have hX0 : x₀ ≤ p.X := h_Zeta23_PrimeSide_Setting_le_X_of_T (hplam ▸ hlam.1)
    (by rw [hplam]; exact (le_max_left _ _).trans hT)
  have hX2 : 2 ≤ p.X := hF.two_le_X
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL1 : 1 ≤ p.L := by linarith
  have hLX : p.L ≤ p.X := hF.L_le_X
  have hlogX : Real.log p.X = p.L := p.log_X
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set W := ∫ x, F.Phi x ^ 2 with hWdef
  have hW0 : 0 ≤ W := integral_nonneg fun x => sq_nonneg _
  have hWle : W ≤ 2 * π * p.L := hF.integral_Phi_sq_le
  set ΛΦ := ∫ x, F.Phi x ^ 2 * |x| with hΛΦdef
  have hΛΦ0 : 0 ≤ ΛΦ := integral_nonneg fun x => mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hΛΦle : ΛΦ ≤ (8 + 8 * |cϱ|) * p.L := by
    have h1 := hF.integral_Phi_sq_mul_abs_le
    have hcϱ : 4 ≤ cϱ := hF.four_le_cϱ
    have hw : 1 ≤ p.w := hF.one_le_w
    have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
    have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) := by
      linarith [Real.log_le_sub_one_of_pos harg]
    have hfrac : cϱ * p.L / (4 * p.w) ≤ |cϱ| * p.L := by
      rw [div_le_iff₀ (by positivity), abs_of_nonneg (by linarith)]
      have hcL : 0 ≤ cϱ * p.L := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hcL (by linarith : (0:ℝ) ≤ 4 * p.w - 1)]
    calc ΛΦ ≤ 8 + 8 * Real.log (cϱ * p.L / (4 * p.w)) := h1
      _ ≤ 8 + 8 * (|cϱ| * p.L) := by linarith
      _ ≤ 8 * p.L + 8 * (|cϱ| * p.L) := by linarith
      _ = (8 + 8 * |cϱ|) * p.L := by ring
  have hsuma : ∑ n ∈ primeRange p.X, acoef n ≤ 3 * Real.sqrt p.X := h1b p.X hX0
  have hsuma0 : 0 ≤ ∑ n ∈ primeRange p.X, acoef n := Finset.sum_nonneg fun n _ => h_Zeta23_PrimeSide_acoef_nonneg n
  have hsumΛ2 : ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 ≤ |C1d| * p.X * p.L := by
    have h := h1d p.X hX2
    rw [hlogX] at h
    refine h.trans ?_
    have hXL : 0 ≤ p.X * p.L := mul_nonneg (by linarith) (by linarith)
    calc C1d * p.X * p.L = C1d * (p.X * p.L) := by ring
      _ ≤ |C1d| * (p.X * p.L) := mul_le_mul_of_nonneg_right (le_abs_self _) hXL
      _ = |C1d| * p.X * p.L := by ring
  have hsuma2 : ∑ n ∈ primeRange p.X, acoef n ^ 2 ≤ (1 / 2 + |C2a|) * p.L ^ 2 := by
    have h := h2a p.X hX2
    rw [hlogX] at h
    simp_rw [h_Zeta23_PrimeSide_acoef_sq]
    have h3 := (abs_le.mp h).2
    unfold primeRange
    calc ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) ^ 2 / n ≤ p.L ^ 2 / 2 + C2a * p.L := by linarith
      _ ≤ p.L ^ 2 / 2 + |C2a| * p.L ^ 2 := by
          have h4 : C2a * p.L ≤ |C2a| * p.L := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
          have h5 : |C2a| * p.L ≤ |C2a| * p.L ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); nlinarith
          linarith
      _ = (1 / 2 + |C2a|) * p.L ^ 2 := by ring
  have hD := h_Zeta23_ThmE_diag_estimate_chi hT0 hΦc hF.Phi_sq_integrable hF.Phi_sq_mul_abs_integrable
    hF.Phi_sq_fourier hc1 p.X
  have hO1 := h_Zeta23_ThmE_O1_bound_chi (c := c) hMV hCMV.le hT0 hΦc hF.Phi_sq_integrable hc1 p.X
  have hO2 := h_Zeta23_ThmE_O2_estimate_chi (c := c) hΦc hF.Phi_sq_integrable hc1 p.X p.T
  rw [h_Zeta23_ThmE_Mform_PXc_PXc hT0 hΦc, ← h_Zeta23_ThmE_sum_w_eq_sumA2gCoprime hc p.X F.g]
  set D := ∑ n ∈ primeRange p.X, (acoef n * ‖c n‖) ^ 2 * Aminus F.Phi p.T (Real.log n) (Real.log n)
  set O1 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    (if n = m then (0:ℝ) else (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
      * AminusPh F.Phi p.T (Real.log n) (Real.log m) (c n).arg (c m).arg)
  set O2 := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X,
    (acoef n * ‖c n‖) * (acoef m * ‖c m‖)
      * AplusPh F.Phi p.T (Real.log n) (Real.log m) (c n).arg (c m).arg
  have hk : (0:ℝ) < 1 / (2 * π ^ 2) := by positivity
  have bD : |1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n)|
      ≤ 1 / (2 * π ^ 2) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|)) * (p.L ^ 2 * p.X) := by
    refine hD.trans ?_
    rw [mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc (∑ n ∈ primeRange p.X, acoef n ^ 2) * ΛΦ
        ≤ ((1 / 2 + |C2a|) * p.L ^ 2) * ((8 + 8 * |cϱ|) * p.L) := by
          apply mul_le_mul hsuma2 hΛΦle hΛΦ0 (by positivity)
      _ ≤ ((1 / 2 + |C2a|) * p.L ^ 2) * ((8 + 8 * |cϱ|) * p.X) := by gcongr
      _ = (1 / 2 + |C2a|) * (8 + 8 * |cϱ|) * (p.L ^ 2 * p.X) := by ring
  have bO1 : |1 / (2 * π ^ 2) * O1|
      ≤ 1 / (2 * π ^ 2) * (16 * CMV * (2 * π) * |C1d|) * (p.L ^ 2 * p.X) := by
    rw [abs_mul, abs_of_pos hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc |O1| ≤ 16 * CMV * W * ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 := hO1
      _ ≤ 16 * CMV * (2 * π * p.L) * (|C1d| * p.X * p.L) := by
          apply mul_le_mul _ hsumΛ2 (Finset.sum_nonneg fun n _ => sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hWle (by positivity)
      _ = 16 * CMV * (2 * π) * |C1d| * (p.L ^ 2 * p.X) := by ring
  have bO2 : |1 / (2 * π ^ 2) * O2| ≤ 1 / (2 * π ^ 2) * (2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by
    rw [abs_mul, abs_of_pos hk, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hk.le
    calc |O2| ≤ W / Real.log 2 * (∑ n ∈ primeRange p.X, acoef n) ^ 2 := hO2
      _ ≤ (2 * π * p.L) / Real.log 2 * (3 * Real.sqrt p.X) ^ 2 := by
          apply mul_le_mul _ _ (sq_nonneg _) (by positivity)
          · exact div_le_div_of_nonneg_right hWle hlog2.le
          · exact pow_le_pow_left₀ hsuma0 hsuma 2
      _ = 2 * π / Real.log 2 * 9 * (p.L * p.X) := by
          rw [mul_pow, Real.sq_sqrt (by linarith)]; ring
      _ ≤ 2 * π / Real.log 2 * 9 * (p.L ^ 2 * p.X) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hLL : p.L ≤ p.L ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right hLL (by linarith)
  have split : 1 / (2 * π ^ 2) * (D + O1 + O2)
        - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n)
      = (1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n))
        + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2 := by ring
  rw [split]
  calc |(1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n))
        + 1 / (2 * π ^ 2) * O1 + 1 / (2 * π ^ 2) * O2|
      ≤ |1 / (2 * π ^ 2) * D - p.T / π * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ‖c n‖ ^ 2 * F.g (Real.log n)|
        + |1 / (2 * π ^ 2) * O1| + |1 / (2 * π ^ 2) * O2| := abs_add_three _ _ _
    _ ≤ 1 / (2 * π ^ 2) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|)) * (p.L ^ 2 * p.X)
        + 1 / (2 * π ^ 2) * (16 * CMV * (2 * π) * |C1d|) * (p.L ^ 2 * p.X)
        + 1 / (2 * π ^ 2) * (2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) :=
        add_le_add (add_le_add bD bO1) bO2
    _ = (1 / (2 * π ^ 2)) * ((1 / 2 + |C2a|) * (8 + 8 * |cϱ|) + 16 * CMV * (2 * π) * |C1d|
      + 2 * π / Real.log 2 * 9) * (p.L ^ 2 * p.X) := by ring
end Results
end ThmE
end Zeta23
