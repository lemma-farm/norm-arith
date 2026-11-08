-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Heat.Smooth
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.FourierCalculus
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.SmoothSeries
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
open AVenhance.Infra.Torus
open Homogenization
open scoped FourierTransform ENNReal
namespace AVenhance.Infra.Heat
end AVenhance.Infra.Heat
