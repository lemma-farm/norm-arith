/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OffSupportKernel
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.OffSupportOscillatory
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.SchwartzModularOperator
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The canonical operator on the counterexample away from its packets

This file identifies the distributionally defined quadratic Hilbert transform
with the ordinary off-support kernel integrals used in the negative endpoint
argument.  No pointwise value is assigned by convention: the equality follows
from the proved symmetric-truncation limit because the test function vanishes
near the singularity.
-/
open Filter MeasureTheory Set
open scoped SchwartzMap Topology
namespace QuadraticCarleson
set_option autoImplicit false
end QuadraticCarleson
