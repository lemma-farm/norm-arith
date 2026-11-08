module
public import Examples.djalilchafai__ginibre_poincare.Dependencies.v363a8b4b3804.GinibrePoincare.Concrete.Configuration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
@[expose] public section
/-!
# Centre of mass

The real and imaginary parts of the coordinate sum are the equality
directions in the optimal Ginibre Poincaré inequality.
-/
open scoped BigOperators
namespace GinibrePoincare
/-- Sum of the particle coordinates. -/
def coordinateSum {n : ℕ} (z : Configuration n) : ℂ :=
  ∑ i : Fin n, z i
end GinibrePoincare
