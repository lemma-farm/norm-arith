-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v547cd4055db7.CKN.Foundation.Sobolev.Mollify.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Prod
set_option autoImplicit false
set_option warningAsError true
/-!
# `L^p` bounds for normalized convolution

The proof uses Jensen for `|·|^p`, translation invariance, and Tonelli.  The
result is the contraction estimate needed in the density argument for
mollification.
-/
open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution
namespace CKN
noncomputable section
end
end CKN
