/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Definitions.HeatKernel
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.Analysis.Heat.Basic
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.SHF.DeltaBose.CollisionWords
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v3897fced2738.Critical2DKPZ.SHF.DeltaBose.ScalarDensity
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! The free and fused kernels in Tsai’s equations (2.1)–(2.5) use product Lebesgue measure, a collision coefficient of `4π` and center heat time `t/2`. -/
@[expose] public section
open MeasureTheory
namespace Critical2DKPZ.DeltaBose
end Critical2DKPZ.DeltaBose
