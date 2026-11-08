/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.CalderonZygmundBadPart
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v1b72e0a4398b.QuadraticCarleson.PositiveLevelIntegration
import Mathlib
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Calderón--Zygmund atoms on magnitude levels

This file isolates the algebraic and measure-theoretic facts about the atoms

`1_I (f 1_{F_k} - average_I (f 1_{F_k}))`

used in the positive-endpoint argument.  It does not assert the existence of
a Calderón--Zygmund decomposition: the interval (or a disjoint family of
intervals) is supplied explicitly.
-/
open MeasureTheory Set
open scoped ENNReal BigOperators Function
namespace QuadraticCarleson
namespace CalderonZygmundLevelAtoms
open PositiveEndpointOptimization PositiveLevelIntegration
set_option autoImplicit false
noncomputable section
end
end CalderonZygmundLevelAtoms
end QuadraticCarleson
