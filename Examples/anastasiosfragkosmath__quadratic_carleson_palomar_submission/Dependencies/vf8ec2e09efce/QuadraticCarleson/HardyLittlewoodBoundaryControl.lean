/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceySharpSmoothAdapter
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.HardyLittlewoodMaximalLp
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.ExtendedWeakL1Combinators
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.FiniteSparseMaximalProof
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleSparseAdapter
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryMiddleBlockWeak
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.LacunaryOscillatoryScaling
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.PositivePrincipalValueEndpoints
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# The Hardy--Littlewood boundary term in the sharp/smooth KL comparison

The smooth-to-sharp comparison produces one copy of the centered
Hardy--Littlewood maximal function, common to all modulations and truncation
radii.  This file packages that concrete boundary operator on `L0Infinity`.
In particular, its output is finite everywhere, measurable and locally
integrable, and it has the explicit weak `(1,1)` constant `4`.

This is also the operational reason that the boundary term need not be put
inside the individual Krause--Lacey sparse forms: after taking the finite
modulation maximum it is still a single maximal function, hence incurs no
cardinality loss.
-/
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
namespace QuadraticCarleson
namespace HardyLittlewoodBoundaryControl
open ExtendedWeakL1Combinators
open QuadraticHilbertMaximalMeasurable
open KrauseLaceyFiniteRadiusAdapter
open KrauseLaceySharpSmoothAdapter
open LacunaryMiddleSparseAdapter LacunaryMiddleRange
open LacunaryMiddleBlockWeak
open LacunaryOscillatoryScaling
open PositivePrincipalValueEndpoints HilbertPrincipalValueClosure
set_option autoImplicit false
noncomputable section
end
end HardyLittlewoodBoundaryControl
end QuadraticCarleson
