/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v8b8fb661fed2.Rhone.Statistics.Identifiability.PanRiccatiUniqueness
public import Mathlib
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # The scalar reconstruction is equivalent to the full pre-merger ODE -/
@[expose] public section
namespace Rhone.Statistics.Identifiability
set_option backward.isDefEq.respectTransparency false
def PanPreEquations (rate recomb D R U : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t →
    HasDerivAt D (-(rate t+2*recomb t)*D t+rate t*R t) t ∧
    HasDerivAt R (2*recomb t*D t-(3*rate t+recomb t)*R t+4*rate t*U t) t ∧
    HasDerivAt U (recomb t*R t-6*rate t*U t) t
end Rhone.Statistics.Identifiability
