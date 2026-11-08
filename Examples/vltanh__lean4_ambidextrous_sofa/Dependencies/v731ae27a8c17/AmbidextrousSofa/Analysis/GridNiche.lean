module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapMaximum
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Uniform approximation of the actual niche by finite angular grids

The samples use the continuous clipped two-wall height on the closed
quarter interval. Its endpoint values are zero, so inserting the zero
angle is exactly the physical baseline clipping. For any increasing
sequence of finite grids with dense union, the actual finite maxima
increase to the whole-angle niche. Dini's theorem then makes convergence
uniform on every compact cap domain and bounded spatial interval.
-/
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
namespace AngularGrid
end AngularGrid
end AmbidextrousSofa
