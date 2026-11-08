module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.CapVolumeContinuity
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Measure.CapScore
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Almost-everywhere convergence of actual cap roofs

Fubini passes planar indicator convergence to almost every vertical line.
The unit strip supplies a single integrable bound on each such line. The
fiber integral is the actual roof, including its zero extension off the
projection. No strict convexity or positive limiting width is required.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa
