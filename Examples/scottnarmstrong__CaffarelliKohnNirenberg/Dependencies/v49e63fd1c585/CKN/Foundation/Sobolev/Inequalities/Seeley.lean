-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Cutoff.Ball
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option warningAsError true
/-!
# The two-reflection extension on the unit ball

The radial maps in this file are the two reflections used to continue a smooth
function across the unit sphere.  The geometric estimates are recorded on the
closed annulus and the gluing interface is kept independent of the radial maps.
-/
open Set MeasureTheory
open scoped BigOperators
open scoped ENNReal
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN
