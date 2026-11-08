/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.WhiteNoiseChaosMomentsLinear
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Probability.GaussianVector
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moment equivalence in finite white-noise chaos

For a white noise `W` and square-integrable test functions `h₁, …, hₙ`, a *cylindrical polynomial*
of degree at most `m` is `ω ↦ f (W h₁ ω, …, W hₙ ω)` with `f` a real polynomial of total degree at
most `m`.

* `exists_integral_pow_two_mul_le_of_isWhiteNoise`: all even moments of a cylindrical polynomial
  are bounded by a power of its variance, with a constant depending only on `m` and the exponent;
* `integral_pow_two_mul_le_of_tendsto_cylindricalPolynomial`: the same bound, with the same
  constant, holds for `L²` limits of cylindrical polynomials of degree at most `m`
  (the finite-chaos case), by Fatou's lemma along an a.e. convergent subsequence.
-/
public section
open MvPolynomial MeasureTheory Filter Topology
namespace RegularityStructures
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
end RegularityStructures
end
