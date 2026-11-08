/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3Psi2DiagramLeaves
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3Psi2DiagramMultiLevel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Weighted principal and chain diagrams

Wrappers around the chain and principal majorants of `I(Ψ³)Ψ` for the weights that occur in
`I(Ψ³)Ψ²`: the weight `Λ |δK(z, w)| |δK(z', v)| ×` (a product of powers of the distances) is a
two-level majorant (`TwoLevelLe`) with bound `Λ C ×` a power combination.  Hence every measurable `F`
dominated by it is integrable on the product with iterated integral bounded by this bound, and
sums of such weights are handled by `TwoLevelLe.add`.  The exponents are general, so that they
accommodate the factor `μ s^(-θ)` gained by one covariance in the difference of two fields.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
