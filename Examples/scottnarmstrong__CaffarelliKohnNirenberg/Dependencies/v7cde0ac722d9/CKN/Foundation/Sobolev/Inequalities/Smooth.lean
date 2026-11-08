-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Sobolev.Cutoff.Ball
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
set_option autoImplicit false
set_option warningAsError true
/-!
# Local Sobolev and interpolation inequalities for smooth functions

This file proves local Sobolev and interpolation inequalities for smooth
functions. The corresponding weak H¹ estimate has the form

`‖u‖₆(Bᵣ) ≤ C (‖∇u‖₂(B₂ᵣ) + r⁻¹ ‖u‖₂(B₂ᵣ))`.

Passing from smooth functions to weak H¹ functions requires local approximation
of both the function and its gradient, together with the weak product rule
for a smooth cutoff. Interpolation yields the `L³` and `L^(10/3)` estimates;
for `Q_r = (t-r²,t) × B_r`, the `L³` cylinder factor is `r^(1/2)`.
-/
open MeasureTheory Set
open scoped ENNReal
namespace CKN
noncomputable section
end
end CKN
