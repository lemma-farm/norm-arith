module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Measure.SupportArea
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Topology.TietzeExtension
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Absolutely continuous graph and support area

The parameter curves and their first support derivatives are absolutely
continuous. All derivative assertions are almost everywhere assertions.
The oriented graph identity retains its endpoint products and permits a
collapsed or reversed arc. A continuous extension of the actual graph
function is used only to apply the ordinary primitive chain rule. Actual
cap area is obtained from its roof and its realized boundary points, not
postulated as a support-energy certificate; continuous first derivatives
with integrable right second derivatives are covered, hence the explicit
reference even at its curvature switches.
-/
noncomputable section
open Set Filter MeasureTheory
namespace AmbidextrousSofa
end AmbidextrousSofa
