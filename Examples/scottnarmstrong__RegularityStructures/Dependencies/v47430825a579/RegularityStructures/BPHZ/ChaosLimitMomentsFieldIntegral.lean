/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.ChaosLimitMoments
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.ChaosLimitMomentsRiemannLimit
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.ChaosLimitMomentsRiemannL2
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moment equivalence for tested polynomial fields of a white-noise field

Let `ψ` be a continuous random field (for every `ω`) such that every value `ψ(·, y)` is almost
surely a white-noise pairing `W h_y` and `E ψ(y)² ≤ V`. Let `g` be a measurable integrable test
function supported in a compact set `S`, `k(y, ·)` integrable kernels with `∫ |k(y, w)| dw ≤ L` and
supported in `S` whenever `g y ≠ 0`, and `P₁, P₂, P₃` polynomials with `deg P₁ + deg P₂ ≤ m`,
`deg P₃ ≤ m`. Then
`X = ∫ (∫ k(y, w) P₁(ψ(w)) dw · P₂(ψ(y)) + P₃(ψ(y))) g(y) dy`
satisfies `E X^(2p) ≤ A (E X²)^p` with `A = A(m, p)` independent of everything else
(`integral_pow_two_mul_le_of_chaosIntegral`), and the same for `X = ∫ P(ψ(y)) g(y) dy`
(`integral_pow_two_mul_le_of_polyIntegral`).

The proof samples `ψ` along finitely-valued measurable maps `πₙ → id`: the sampled fields are
polynomials of degree `≤ m` in finitely many values of `ψ`, hence almost surely cylindrical
polynomials of `W`; they converge pathwise by continuity of `ψ(ω, ·)` and are bounded in `L²`
by crude fixed-noise moment bounds, so the almost sure limit theorem applies.
-/
public section
open MeasureTheory Filter Topology
namespace RegularityStructures
universe u
end RegularityStructures
end
