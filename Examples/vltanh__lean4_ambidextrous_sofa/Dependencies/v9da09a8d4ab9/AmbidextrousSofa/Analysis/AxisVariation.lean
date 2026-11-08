module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.PolygonExposure
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual endpoint movement from a positive vertical end face

Moving a displayed box wall need not move the actual projection. Here a
positive end face gives a point strictly below every nonaxis upper wall.
Its small horizontal displacement lies in the enlarged polygon and
realizes the new endpoint. All sampled upper supports stay fixed. This is
the geometric condition needed before applying the moving-window pressure
formulas.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
end FinitePolygon
end AmbidextrousSofa
