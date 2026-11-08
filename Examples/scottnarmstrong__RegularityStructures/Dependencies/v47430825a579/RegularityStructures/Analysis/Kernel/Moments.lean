/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Kernel.Parabolic
import Mathlib.MeasureTheory.Integral.Pi
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Moment bounds for the parabolic kernel

For `t > 0` and `r ≥ 0`, `∫ |q_t(w)| ‖w‖_𝔰^r dw ≤ M_r t^{r/4}`, with the explicit constant
`M_r = 4^r (G_{r/2} K_0³ + 3 G_0 K_r K_0²)` where `G_s = ∫ |g_1(a)| |a|^s da` and
`K_s = ∫ |k_1(b)| |b|^s db`. The proof bounds `‖w‖_𝔰^r ≤ 4^r (|w₀|^{r/2} + ∑ᵢ |wᵢ|^r)` and evaluates
the resulting product integrals by Fubini (`RegularityStructures.Analysis.Kernel.Parabolic`).
-/
@[expose] public noncomputable section
namespace RegularityStructures
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
end RegularityStructures
end
