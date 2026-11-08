/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.RegularityStructures.Torus.HeatKernelRegularity
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.va037cec7ed87.RegularityStructures.Torus.KernelBoundsBasic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Gaussian majorants for the torus heat kernel

The one-dimensional majorant from `HeatKernelRegularity` can be fixed at the scale `t = 1`. This
gives a summable, `t`-independent lattice majorant for `0 < t ≤ 1`, and hence the first
time-singular estimate needed for the torus kernel bounds.  The constants in this file are
introduced before any point variable; this is the convention used by Hairer's kernel estimates.

Source: [Hai14, Assumption 5.1 and (5.4)].
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
end RegularityStructures
end
