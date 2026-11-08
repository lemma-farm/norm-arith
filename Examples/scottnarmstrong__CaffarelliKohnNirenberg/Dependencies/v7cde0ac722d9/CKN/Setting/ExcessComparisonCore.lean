-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Core.Caccioppoli.Finiteness
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Core.Caccioppoli.Conversions
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Pressure.OscillationLin34
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.Finiteness
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Parabolic.Integration.Slice
import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option autoImplicit false
set_option warningAsError true
/-!
# Tsai excess quantities

The four quantities in this file use genuine averages on the one-sided
parabolic cylinder.  The velocity norm is transported to `L²` before applying
the convexity estimate, so it is the Euclidean norm used by the scale
quantities.
-/
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
