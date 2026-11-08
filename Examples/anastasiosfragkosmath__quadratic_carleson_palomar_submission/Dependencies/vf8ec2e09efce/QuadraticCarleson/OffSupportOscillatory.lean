/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.WavePacket
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Two-fold nonstationary phase away from a wave packet

This file proves the `k = 2` instance of the oscillatory estimate used in
equation (3.2) of the paper.  The proof differentiates the phase in the
original kernel variable twice; it does not use the erroneous square-root
substitution displayed in the paper.
-/
open Function MeasureTheory Set
open scoped Interval
namespace QuadraticCarleson
end QuadraticCarleson
