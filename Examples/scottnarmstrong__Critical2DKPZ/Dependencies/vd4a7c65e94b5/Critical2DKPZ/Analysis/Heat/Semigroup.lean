/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Analysis.Heat.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Planar heat kernels satisfy Gaussian convolution and diffusive scaling identities. -/
public section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace Critical2DKPZ
theorem integral_heatKernel_sub {u : ℝ} (hu : 0 < u) (a : Plane) :
    ∫ y : Plane, heatKernel u (y - a) = 1 := by
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self (heatKernel u) (-a)).trans (integral_heatKernel hu)
end Critical2DKPZ
end
