-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.Product
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v119a619aec3c.AVenhance.Infra.FaaDiBruno.Composition
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Appendix B.2 transport estimates

This module records the numerical estimates used in the transport induction.
The corrected coefficient is kept in its source-correct form; its equal-radius
specialization is the one consumed by the paper's later application.
-/
@[expose] public section
noncomputable section
namespace AVenhance.FaaDiBruno
open MeasureTheory
end AVenhance.FaaDiBruno
end
