module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Motions
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Rigid changes of body coordinates

The coordinate plane has the product norm, so the rotations below are handled
as explicit linear homeomorphisms. No assertion that they are isometries for
that norm is used. Rebasing a motion subtracts its initial real angle lift;
the common incoming orientation is needed only as equality of rotation maps.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
end AmbidextrousSofa
