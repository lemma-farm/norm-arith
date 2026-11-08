module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.LowHeightScore
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapTranslation
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# An actual terminal-wall bound at every proper angle

The right exterior roof lies below the actual first support line. On the
left half of the middle interval, the entire outgoing first wall is a
lower bound for the actual barrier. Their support-height terms cancel
after integration. The other middle half contributes nonnegative cost.

This gives a quadratic bound in the actual quarter-width. Completing its
square yields a bound depending only on the proper terminal angle, for
every downward cap.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa
