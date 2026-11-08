/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v2873403e9bda.Phi43.BPHZ.TreeI2Psi2DiagramConv
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Bounded integrals of products of singular weights over a time slab

All the variables of the diagram integrals of the tree `I(Ψ²) Ψ²` lie in a time slab
`|t - τ| ≤ 2` (the kernels `K` are supported in `|t| ≤ 1` and the base points are within
distance `1` of `τ`).  On the slab every parabolic distance to a point of the slab is at most `3`,
so a product of weights `s(pᵢ - w)^(-λᵢ)` with total exponent `λ₁ + λ₂ + λ₃ < 5` has a bounded
integral: `i2Psi2LintBound_slab_triple`, [Hai14, (10.37a), Lemma 10.14].
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
theorem measurable_torusParabolicSize_sub_rpow (p : SpaceTime) (e : ℝ) :
    Measurable fun w : SpaceTime => torusParabolicSize (p - w) ^ e :=
  (Phi43.measurable_torusParabolicSize.comp (measurable_const.sub measurable_id)).pow_const _
end RegularityStructures
end
