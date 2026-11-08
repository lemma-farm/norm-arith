/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyThreeShiftTreeInterface
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite compact-support localization into the three shifted grids

At a fixed represented scale, every consecutive central-third tile has a
unique address in one of the three translated dyadic grids.  This module
turns that global partition into three finite subfamilies for a compactly
supported input and proves exact reconstruction, including endpoints.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid
open CalderonZygmundDyadicStopping
open KrauseLaceyShiftedLocalization
set_option autoImplicit false
noncomputable section
local instance : DecidableEq RealInterval := Classical.decEq _
end
end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
