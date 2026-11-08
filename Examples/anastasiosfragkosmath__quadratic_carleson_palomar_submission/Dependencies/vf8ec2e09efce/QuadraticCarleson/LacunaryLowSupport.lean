/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleRange
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.CalderonZygmundLevelAtoms
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LowKernelCalderonZygmund
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LowKernelLevelSummation
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.SchwartzOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Support vanishing in the lacunary low branch

This file proves the support observation used to discard atom scales above
the paper's middle range.  With the project's concrete cutoff the resulting
constant is stronger than the unspecified source constant: a low kernel at
modulation `2^m` cannot connect an atom interval of length in scale `j` to a
point outside its fivefold dilation when `m + 2j > 2B`.
-/
open Function Set
namespace QuadraticCarleson
namespace LacunaryLowSupport
set_option autoImplicit false
end LacunaryLowSupport
end QuadraticCarleson
