/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Path.Basic
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Time.CountableDenseTime
import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Detecting closed sets from countably many path coordinates -/
open MeasureTheory Set
namespace MarkovProcess
noncomputable section
namespace ContinuousPath
variable {alpha : Type*} [PseudoMetricSpace alpha]
variable [MeasurableSpace alpha] [BorelSpace alpha]
end ContinuousPath
end
end MarkovProcess
