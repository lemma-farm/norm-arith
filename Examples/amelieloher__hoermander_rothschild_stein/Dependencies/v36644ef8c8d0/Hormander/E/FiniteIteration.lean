-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v36644ef8c8d0.Hormander.Defs.HormanderOp
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v36644ef8c8d0.Hormander.Defs.LieWordEval
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v36644ef8c8d0.Hormander.E.BootstrapBounds
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v36644ef8c8d0.Hormander.E.CutoffPath
public import Examples.amelieloher__hoermander_rothschild_stein.Dependencies.v36644ef8c8d0.Hormander.E.LocalData
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unusedSectionVars true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open SchwartzMap TemperedDistribution
open Hormander.B
open Hormander.Interface
namespace Hormander.E
/-- The exact one-step statement at fixed frame data, universally
quantified over nested Schwartz cutoffs and the Sobolev order. -/
abbrev OneStepAtFixedFrame {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N) (c : Carrier N → ℝ)
    (_hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (_hXc : ∀ i, HasCompactSupport (X i))
    (_hc : ContDiff ℝ (⊤ : ℕ∞) c) (_hcc : HasCompactSupport c)
    {K U : Set (Carrier N)} (_hK : IsCompact K) (_hU : IsOpen U) (_hKU : K ⊆ U)
    (s : ℕ) (_hs : 1 ≤ s) (w : Fin N → LieWord k)
    (_hws : ∀ a, Hormander.lieWordLength (w a) ≤ s)
    (_hw : ∀ x ∈ U,
      LinearIndependent ℝ (fun a => Hormander.lieWordEval X (w a) x)) : Prop :=
  ∀ (η₁ η₂ : SchwartzMap (Carrier N) ℝ)
    (_hη : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ)
      (η₂ : Carrier N → ℝ))
    (_hη₂K : tsupport (η₂ : Carrier N → ℝ) ⊆ K) (r : ℝ),
    ∃ C : ℝ, ∀ (u : 𝓢'(Carrier N, ℂ))
      (a b : Hormander.A.SobolevSpace N r),
      a.toDistr = Hormander.B.cutoffDistr η₂ u →
      b.toDistr = Hormander.B.cutoffDistr η₂ (Hormander.hormanderOp X c u) →
      ∃ v : Hormander.A.SobolevSpace N (r + (2 : ℝ) / 4 ^ s),
        v.toDistr = Hormander.B.cutoffDistr η₁ u ∧ ‖v‖ ≤ C * (‖b‖ + ‖a‖)
end Hormander.E
end
