module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.PositiveTent
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.WideCap
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# The genuine diagonal two-ray tent

At the exact angle pi/4 the two inner walls use the actual support maxima
of x+y and -x+y. Their minimum is a tent. Clipping its negative part gives
the diagonal barrier, a pointwise lower bound for every full or partial
barrier whose visited range reaches pi/4, including the terminal endpoint case.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa
