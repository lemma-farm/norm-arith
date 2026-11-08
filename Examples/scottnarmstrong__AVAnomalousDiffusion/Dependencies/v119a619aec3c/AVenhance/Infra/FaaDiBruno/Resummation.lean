-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.Formula
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ordered-finpartition resummations

The factorial weights in the composition estimate have a closed form when
summed over Mathlib's ordered finpartitions.  This is the coefficient-level
form of the 10469 resummation needed by Proposition 10528.
-/
@[expose] public section
noncomputable section
namespace AVenhance.FaaDiBruno
open Polynomial
end AVenhance.FaaDiBruno
end
