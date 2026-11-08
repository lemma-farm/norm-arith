/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Continuity.DenseTimeContinuousExtension
import Mathlib.Topology.ContinuousMap.CompactlySupported
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Integrals of finite dense-time marginals of a path measure

Integrating a compactly supported test against the finite dense-time marginal of a measure on
continuous-path space is integrating the composed test against the measure itself.  This is a
change-of-variables identity with no probabilistic content.
-/
open MeasureTheory
open scoped CompactlySupported
namespace MarkovProcess
namespace ContinuousPath
variable {alpha : Type*} [TopologicalSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
end ContinuousPath
end MarkovProcess
