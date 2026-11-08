/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CounterexampleErrorBudget
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.L0LacunaryOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Failure of sub-`L log₂ L` modular estimates

This file closes the negative-endpoint counterexample.  It first proves the
linear-in-`N` level-set lower bound for the canonical distributional
lacunary quadratic Carleson operator on the paper's smooth compactly
supported counterexamples.  The abstract modular contradiction then gives
failure for every Young function growing strictly slower than `t log₂ t`,
together with the normalized unit-height witnesses stated in the paper.
-/
open Filter MeasureTheory Set
open scoped ENNReal SchwartzMap
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
