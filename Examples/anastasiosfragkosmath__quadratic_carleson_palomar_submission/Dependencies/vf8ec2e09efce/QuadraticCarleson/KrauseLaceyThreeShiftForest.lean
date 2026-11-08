/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/
import Examples.anastasiosfragkosmath__quadratic_carleson_palomar_submission.Dependencies.vf8ec2e09efce.QuadraticCarleson.KrauseLaceyThreeShiftLocalization
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Finite forests in one translated Krause--Lacey grid

A finite collection of depth/address pairs may meet several depth-zero
ancestors.  This file enlarges it, without changing the grid, to the union of
the corresponding complete parent-closed trees.  Thus the concrete
three-shift localization can be fed root by root into the finite stopping
recursion.
-/
open Function MeasureTheory Set
namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid
open CalderonZygmundDyadicStopping
set_option autoImplicit false
noncomputable section
local instance : DecidableEq RealInterval := Classical.decEq _
end
end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
