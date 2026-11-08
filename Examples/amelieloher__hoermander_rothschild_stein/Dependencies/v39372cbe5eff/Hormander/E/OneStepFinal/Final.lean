-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.OneStepFinal.FinalAux
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.E.CutoffChains
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.HormanderOp
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.LieWordEval
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v39372cbe5eff.Hormander.Defs.LieWordLength
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.E
open Hormander.B
/-- The localized gain statement `Hormander.D.localized_gain`, as a
hypothesis ranging over all of its binders. -/
def D1Hypothesis : Prop :=
  ∀ {k N : ℕ}
    (X : Fin (k + 1) → Hormander.B.Carrier N → Hormander.B.Carrier N)
    (c : Hormander.B.Carrier N → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c)
    (hcc : HasCompactSupport c)
    {K U : Set (Hormander.B.Carrier N)}
    (_hK : IsCompact K) (_hU : IsOpen U) (_hKU : K ⊆ U)
    (s : ℕ) (_hs : 1 ≤ s)
    (w : Fin N → Hormander.Interface.LieWord k)
    (_hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (_hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x))
    (η₁ η₂ : SchwartzMap (Hormander.B.Carrier N) ℝ)
    (_hη : Hormander.D.cutoffPrecedes (η₁ : Hormander.B.Carrier N → ℝ)
      (η₂ : Hormander.B.Carrier N → ℝ))
    (_hη₂K : tsupport (η₂ : Hormander.B.Carrier N → ℝ) ⊆ K)
    (σ : ℝ),
    ∃ C : ℝ, ∀ u : Hormander.B.TestFunction N,
      Hormander.B.sobolevNorm (σ + (2 : ℝ) / 4 ^ s)
        (Hormander.B.realMultiplierOperator η₁ u) ≤
        C * (Hormander.B.sobolevNorm σ
          (Hormander.B.realMultiplierOperator η₂
            (Hormander.C.diffusionOperator
              (Hormander.C.c9SchwartzVectorField X hX hXc)
              (Hormander.C.c9SchwartzMultiplier c hc hcc) u)) +
          Hormander.B.sobolevNorm σ
            (Hormander.B.realMultiplierOperator η₂ u))
end Hormander.E
