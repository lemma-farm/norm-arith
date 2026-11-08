-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Sobolev.W1p.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Sobolev.W1p.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Sobolev.Mollify.LpApproximation
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v09f1d5c1ae75.CKN.Foundation.Sobolev.Mollify.Transport
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
set_option autoImplicit false
set_option warningAsError true
/-!
# The ball Poincare inequality for representative-level `W^{1,p}` functions

The proof uses interior mollification on compactly contained balls and then
exhausts the original ball.
-/
open Function Set Filter MeasureTheory Topology
open scoped ENNReal Convolution Pointwise
namespace CKN
noncomputable section
end
end CKN
