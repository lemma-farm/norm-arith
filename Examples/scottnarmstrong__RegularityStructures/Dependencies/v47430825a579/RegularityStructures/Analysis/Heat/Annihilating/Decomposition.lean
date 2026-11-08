/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Basic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Annihilating.Scaled
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The modified decomposition `G = ∑ annShell + annRemainder`

Smoothness, support, the telescoping identity
`∑_{n<M} annShell N n = ∑_{n<M} heatShell n - ψ + (2^M)^3 ψ(S^{2^M} ·)`, the decomposition of the
heat kernel, and Assumption 5.1 with `β = 2` for `annShell N`.

Source: Hairer, arXiv:1303.5113v4, proof of Lemma 5.5.
-/
public section
open scoped ContDiff
namespace RegularityStructures
theorem exists_inv_pow_lt {z : ParabolicSpace} (hz : z ≠ 0) :
    ∃ M : ℕ, (2 : ℝ)⁻¹ ^ M < parabolicNorm z := by
  have hpos : 0 < parabolicNorm z :=
    lt_of_lt_of_le (smoothParabolicNorm_pos hz) (smoothParabolicNorm_le_parabolicNorm z)
  exact exists_pow_lt_of_lt_one hpos (by norm_num)
end RegularityStructures
end
