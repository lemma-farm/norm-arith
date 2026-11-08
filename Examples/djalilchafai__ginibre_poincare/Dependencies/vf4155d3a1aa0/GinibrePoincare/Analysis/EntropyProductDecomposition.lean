module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.vf4155d3a1aa0.GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
/-- The square moment of a fiber in a product probability space. -/
def fiberSquareMoment {α β : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : α × β → ℝ) (x : α) : ℝ := ∫ y, f (x, y) ^ 2 ∂ν
theorem fiberSquareMoment_nonneg {α β : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : α × β → ℝ) (x : α) : 0 ≤ fiberSquareMoment ν f x :=
  integral_nonneg (fun y => sq_nonneg (f (x, y)))
end
end GinibrePoincare
