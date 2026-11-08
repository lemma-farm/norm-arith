-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Classical.Drift
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.Calculus
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v7d56c35ae206.AVenhance.Infra.Torus.FrozenBridge
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Real-valued periodic integration by parts on the unit cell. -/
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open Set
open AVenhance.Infra.Torus
namespace AVenhance.Infra.Classical
end AVenhance.Infra.Classical
end
