/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Bohr
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Intersection of localized Bohr sets

This file proves Lemma `l:bohrintersection` of the paper by counting integer
pairs near the line of slope `m / k`. The positive-frequency hypotheses
follow the paper's explicit convention `ℕ = {1, 2, …}`. The final two lemmas
record the zero-frequency behavior for Lean's different natural-number convention.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
end QuadraticCarleson
