/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.Bohr
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.WavePacket
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The quadratic kernel away from a wave packet

This file formalizes the first (nonoscillatory) estimate in the first lemma of
Section 3 of the paper.  An interval is represented by its centre `s` and its
positive length `t`.  The hypothesis that `x` is outside that interval makes
the singular kernel an ordinary integrable function on the support of the
packet.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
end QuadraticCarleson
