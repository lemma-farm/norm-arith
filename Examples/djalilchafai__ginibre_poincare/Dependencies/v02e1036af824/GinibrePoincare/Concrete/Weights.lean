module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Concrete.Vandermonde
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity
@[expose] public section
/-!
# Gaussian and Ginibre weights

This file defines the Euclidean square norm, the Gaussian weight, the
Vandermonde square, and the unnormalised Ginibre density.  The zero set of the
latter is proved to be exactly the collision locus.
-/
open scoped BigOperators NNReal
namespace GinibrePoincare
noncomputable section
def vandermondeWeight {n : ℕ} (z : Configuration n) : ℝ :=
  Complex.normSq (vandermonde z)
end
end GinibrePoincare
