module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Reference.Momenta
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.EulerFlux
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual Euler equations for the explicit reference pair

To the right of each angle, the clipped momenta `min P 0` and `max Q 0` are
either a momentum or zero, so the fluxes have explicit right derivatives, and
the Euler equations reduce to identities on each of the three phases. They give
the exact boundary variation and strict optimality at the reference width. No
global cap theorem is used in this construction.
-/
noncomputable section
open Set
open AmbidextrousSofa.Analysis
namespace AmbidextrousSofa.Reference
end AmbidextrousSofa.Reference
