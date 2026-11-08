/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.FiniteSparseMaximal
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.HardyLittlewoodMaximal
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Comparing interval averages with the measurable centered maximal operator

The sparse-form argument is naturally stated using arbitrary intervals,
whereas the measurable Hardy--Littlewood maximal operator uses centered balls
of positive rational radius.  Every interval containing `x` lies in such a
ball with radius less than twice the interval length.  This file records the
resulting pointwise comparison.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
