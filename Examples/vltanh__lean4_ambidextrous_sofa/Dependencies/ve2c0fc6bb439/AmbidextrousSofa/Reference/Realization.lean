module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Reference.Hull
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Realization of the displayed reference support

The boundary points are defined by `h μ + h' ν`. Their scalar projections
have right derivative `(h + h'') sin (φ - t)`. The right-derivative fundamental
theorem of calculus controls these projections even at the two curvature
jumps. The first upper arc meets the companion constraints through the actual
horizontal top face, and reflection supplies the lower half-plane constraints.
The second arc is the mirror image of the first about the center abscissa.

This argument constructs attaining points in the existing `referenceHull`;
it does not assume that the prescribed support has already been realized.
-/
noncomputable section
open Set
open scoped Topology
namespace AmbidextrousSofa.Reference
end AmbidextrousSofa.Reference
