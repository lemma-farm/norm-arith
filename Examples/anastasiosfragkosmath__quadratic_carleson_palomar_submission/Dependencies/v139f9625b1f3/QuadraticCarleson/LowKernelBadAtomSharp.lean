/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.LowKernelCalderonZygmund
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.v139f9625b1f3.QuadraticCarleson.LowOscillatoryMajorant
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Sharp low-kernel estimate for a cancellative bad atom

The derivative estimate alone gives a bound growing like `2^(2B)`.  The
paper obtains the sharp `O(B)` estimate by taking the minimum of that
cancellation bound and the `1 / |t|` size bound for the telescoped low
kernel.  This file proves the resulting common pointwise majorant uniformly
in the modulation parameter `lam`, then integrates it with
`integral_lowDecayMajorant_two_pow_le`.
-/
open MeasureTheory Set
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
