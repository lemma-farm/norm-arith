module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Reference.Stationarity
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Reference.Body
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Measure.SignedRoofIntegralAC
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Measure.SymmetricBody
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Exact value and actual area of the reference

The Euler identity against the reference itself evaluates the quadratic
part by its actual endpoint fluxes. The remaining three phase integrals
have elementary antiderivatives. The cubic root identity then converts the
result to `M`; no area or optimality statement is an input to this calculation.
The actual support-area and signed-roof formulas then identify that value with
the concrete cap score and with the area of the symmetric trimmed hull.
-/
noncomputable section
open Set MeasureTheory
open AmbidextrousSofa.Analysis
namespace AmbidextrousSofa.Reference
attribute [local fun_prop] continuous_referenceF continuous_referenceG continuous_referenceFD
  continuous_referenceGD
end AmbidextrousSofa.Reference
