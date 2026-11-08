module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.EndpointPressure
public import Mathlib.Analysis.Asymptotics.Lemmas
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Simultaneous wall and endpoint variations

The finite wall integral is differentiated while both integration endpoints
move. A uniform wall-velocity bound controls each moving sliver by a
quadratic error. This accounts for all endpoint terms without differentiating
an indicator or assuming that the end faces have positive height.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace WallExpr
variable {ι : Type*}
end WallExpr
end AmbidextrousSofa
