module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Analysis.TiltedBalanceHeight
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# The width determined by the initial-circle radius

At the small-height boundary, a dry low endpoint gives the smallest
possible initial momentum. The squared-radius bound five then determines
the comparison width. Its Newton bounds serve both the floor-energy
test and the three-triangle exclusion; no separate width tolerance is chosen.
-/
noncomputable section
attribute [local simp]
  AmbidextrousSofa.Analysis.tiltedBalanceMomentum
  AmbidextrousSofa.Analysis.tiltedBalanceFloorOffset
  AmbidextrousSofa.Analysis.tiltedBalanceGap
  AmbidextrousSofa.Analysis.tiltedBalanceDerivative
  AmbidextrousSofa.Analysis.tiltedBalanceLowerStep
  AmbidextrousSofa.Analysis.tiltedBalanceUpperStep
  AmbidextrousSofa.Analysis.tiltedBalanceLower₁
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₁
  AmbidextrousSofa.Analysis.tiltedBalanceLower₂
  AmbidextrousSofa.Analysis.tiltedBalanceUpper₂
  AmbidextrousSofa.Analysis.tiltedBalanceLower
  AmbidextrousSofa.Analysis.tiltedBalanceUpper
namespace AmbidextrousSofa.Analysis
end AmbidextrousSofa.Analysis
