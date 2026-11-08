module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Measure.CapScore
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# A coercive bound for the actual cap score

Every corner at a visited angle lies below the actual barrier. The two
baseline endpoints supply support witnesses at angle `π / 4`, and their
two attached inner walls give a tent below the actual barrier. The
signed tent integral on the middle half is evaluated exactly. This proves
the large-width exclusion on the full cap domain, including subunit height,
nonsmooth boundaries, and a terminal angle equal to `π / 4`.

This is a compactness reduction; the sharp estimate for intermediate widths is a
separate step.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa
