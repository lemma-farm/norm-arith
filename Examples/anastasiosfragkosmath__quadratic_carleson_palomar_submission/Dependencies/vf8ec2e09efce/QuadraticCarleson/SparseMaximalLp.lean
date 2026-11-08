/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HardyLittlewoodMaximalLp
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.IntervalMaximalComparison
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Strong bounds for the interval maximal averages in the sparse argument

This file combines the arbitrary-interval comparison with the genuine
Hardy--Littlewood `L^q` theorem. It supplies the analytic maximal-function
factor used in Lemma `l:weak11sparse` of the paper.
-/
open MeasureTheory Set
open scoped ENNReal NNReal
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
