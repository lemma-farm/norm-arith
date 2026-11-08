/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiPointwise
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiSigma
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiDiagramUniform
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Basic facts for the diagrams of `I(Ψ³)Ψ²`

* evenness of `Q` when `Q(x) = ∫ J(x + w) J(w) dw`;
* the covariance with a loss `δ` of the exponent, `|Q x| ≤ B 3^δ s(x)^(-(1+δ))`
  (on the slab `|t| ≤ 4`, no support hypothesis on `Q`);
* the flip `s(b - a)^(-p) ≤ 2^p s(a - b)^(-p)` of a centred power.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
