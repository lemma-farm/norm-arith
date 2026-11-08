module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.CircleAverage
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Exact endpoint margins for the terminal circle comparison

Use the cosine of the established terminal-angle endpoint. Four unit-seed
Newton updates bound this root and its sine. The resulting gap is concave in
cap width, so two endpoint checks control the whole width interval.
The circle-height bounds at both endpoints use the same Newton formulas.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
end AmbidextrousSofa
