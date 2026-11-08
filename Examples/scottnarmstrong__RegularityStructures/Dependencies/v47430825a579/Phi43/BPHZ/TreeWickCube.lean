/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianWickBlocksTwo
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianWickDiagram
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.BPHZ.TreeWickSquare
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The Wick cube of the tree `Ψ`

With `Q_ε = hairerCovariance N ρ ε` and `c_ε = hairerWickConstant N ρ ε = Q_ε(0)`, the Wick cube
`:Ψ³:(z) = Ψ(z)³ - 3 c_ε Ψ(z)` satisfies `E[:Ψ³:(u) :Ψ³:(v)] = 6 Q_ε(u - v)³`.  The proof applies
the Gaussian vector `(Ψ(u), Ψ(v))` and the diagram formula for two Wick monomials of length `3`
(`integral_wick_replicate_mul_wick_replicate`); the Wick cube is `wickMonomial C [0, 0, 0]` of that
vector (`wickMonomial_triple_self`).
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
end RegularityStructures.Phi43
end
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
variable {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ : Ω → SpaceTime → ℝ}
end RegularityStructures.Phi43
end
