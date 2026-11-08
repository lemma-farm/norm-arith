/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.Shift
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Continuity.DenseTimeContinuousExtension
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Shifts of dense-time paths

This file defines addition by a nonnegative rational time on the fixed dense carrier and the
induced shift of dense-time paths.  Restriction of a continuous path commutes with this shift.
No probability law or Markov property is asserted.
-/
namespace MarkovProcess
noncomputable section
namespace DenseTime
end DenseTime
namespace DenseTimePath
variable {alpha : Type*}
variable [MeasurableSpace alpha]
end DenseTimePath
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha]
end ContinuousPath
end
end MarkovProcess
