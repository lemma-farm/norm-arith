-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.vbc8165cb0109.AVenhance.Infra.ODE.Linear.Existence
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Energy identities for absolutely continuous curves

The chain rule is separated from the ODE existence construction.  It applies to any
absolutely-continuous curve in a real inner-product space and can therefore be reused for linear
equations with measurable coefficients.
-/
@[expose] public section
open Filter MeasureTheory Set
open scoped RealInnerProductSpace Topology
namespace AVenhance.Infra.ODE
variable {E : Type*} [NormedAddCommGroup E]
end AVenhance.Infra.ODE
