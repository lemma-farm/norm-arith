/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.Phi43.BPHZ.TreeI3Psi2DiagramBasic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.Phi43.BPHZ.TreeI3Psi2DiagramPointwise
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.Phi43.BPHZ.TreeI3PsiPrincipal
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v21091e7a4d76.RegularityStructures.Probability.SpaceTimeMeasure
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Basic integrability facts for the chaos-`1` part of `I(Ψ³)Ψ²`

Let `J` be a measurable kernel which is bounded and integrable (these qualitative properties
never enter the constants) and `Q(x) = ∫ J(x + w) J(w) dw`.  We record

* integrability of functions with a singular bound on a time slab (`integrable_of_slab_bound`);
* boundedness and evenness of `Q`;
* the identity `∫ J(a - y) J(b - y) dy = Q(a - b)`;
* integrability of `δK(z, ·)`, of `K Q²` and of `δK(z, ·) Q(· - z)²`.
-/
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
