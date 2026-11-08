/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HarmonicPhaseSum
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.TranslatedBohrUnion
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Phase witnesses on the counterexample's translated Bohr set

This file joins the measure-theoretic construction of the paper's set `E_N`
to the almost-constant finite harmonic sum.  Every point of `E_N` supplies an
integer translate, a dyadic modulation, and the explicit logarithmic lower
bound needed in the negative endpoint argument.
-/
open MeasureTheory Set
open scoped ENNReal
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
