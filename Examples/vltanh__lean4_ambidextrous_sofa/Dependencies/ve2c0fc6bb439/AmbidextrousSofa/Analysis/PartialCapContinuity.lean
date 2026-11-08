module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.CapMaximum
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Joint continuity for the entire partial barrier

The open swept interval has the same clipped supremum as its closed
interval: continuity at the terminal angle supplies the additional endpoint.
Rescaling that interval to `[0,1]` makes the parameter domain fixed and
compact. The resulting maximum is jointly continuous in the actual cap,
terminal angle and horizontal coordinate. The whole first terminal wall
is then retained as a separate continuous term, including at `π/2`.

Compact bounds and moving-domain dominated convergence give continuity of
the actual partial score on every boxed cap domain. No regularity or
stationarity hypothesis is imposed on these caps.
-/
noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology
namespace AmbidextrousSofa
end AmbidextrousSofa
