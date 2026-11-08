module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v02e1036af824.GinibrePoincare.Concrete.MeasureModel
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
/-- A vector supported in one complex coordinate. -/
def coordinateDirection {n : ℕ} (k : Fin n) (w : ℂ) :
    Configuration n :=
  fun j => if j = k then w else 0
/-- Unit direction in the real part of coordinate `k`. -/
def realCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k 1
/-- Unit direction in the imaginary part of coordinate `k`. -/
def imaginaryCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k Complex.I
end
end GinibrePoincare
