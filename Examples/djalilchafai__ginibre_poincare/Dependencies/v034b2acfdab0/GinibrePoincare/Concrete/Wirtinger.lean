module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v034b2acfdab0.GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
@[expose] public section
/-!
# Concrete Wirtinger derivatives and Gaussian holomorphic distance

The coordinate operators
`∂̄_k = (∂_{x_k} + i ∂_{y_k}) / 2` are defined directly from the real
Fréchet derivative on `Configuration n`.
-/
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
end
end GinibrePoincare
