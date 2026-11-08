-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Ambient.Euclidean
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.SeeleyL1
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Inequalities.Smooth
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.LpOne
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Poincare.Scaling
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Cutoff.NormLeVecEuclidean
set_option autoImplicit false
set_option warningAsError true
/-!
# The same-ball `W^{1,1}` to `L^{3/2}` estimate

The endpoint estimate is obtained by subtracting the ball average, applying the
two-reflection extension and a compact cutoff, and then using the global
Gagliardo--Nirenberg inequality at `p = 1`.  The affine bookkeeping is kept
explicit so that the final constant is independent of the ball.
-/
open Set MeasureTheory
open scoped ENNReal Pointwise
namespace CKN
noncomputable section
attribute [local instance] Classical.propDecidable
end
end CKN
