/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v29ef93969eff.QuadraticCarleson.PVFourierIdentity
import Mathlib
import Mathlib.Data.Real.Sign
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The ordinary Hilbert transform on `L²`

This file constructs the Fourier-multiplier realization of convolution with
the project's kernel `p.v. (1 / x)`.  Mathlib's Fourier normalization makes
the multiplier `-π i sign(ξ)`, so its `L²` operator norm is at most `π`.
-/
open Filter Function MeasureTheory Set FourierTransform
open scoped ENNReal NNReal SchwartzMap
namespace QuadraticCarleson
namespace HilbertL2Fourier
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
end
end HilbertL2Fourier
end QuadraticCarleson
