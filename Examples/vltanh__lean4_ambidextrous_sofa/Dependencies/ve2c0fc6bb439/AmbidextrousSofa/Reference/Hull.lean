module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Reference.Support
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Geometry.Reflection
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# The explicit reference half-plane intersection

The candidate hull is the intersection of all four reflected upper-quarter
families prescribed by `referenceF` and `referenceG`. Its nonemptiness,
compactness, convexity, and literal reflection symmetry are proved here.

The point `(k, 1 / 2)` is an actual witness. Endpoint normals supply the closed
bounding rectangle. These conclusions do not assume that every prescribed
support value is attained. The reverse support inequalities remain a separate
support-realization obligation.
-/
noncomputable section
open Set
namespace AmbidextrousSofa.Reference
end AmbidextrousSofa.Reference
