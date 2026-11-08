module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.Geometry.Caps
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Compact caps, exact vertical fibers, and roofs

The cap construction is carried out on actual sets. Compactness of downward
filling follows from a continuous image of the original compact set times
`[0, 1]`. No smoothness, positive width, or height-one hypothesis is used.

The roof is extended by zero outside its exact horizontal projection. This
extension is upper semicontinuous for a compact set above the baseline. For
an intrinsic downward cap, its fibers are exactly the intervals from zero to
the roof, and convexity makes the roof concave on its projection.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
def horizontalLeft (K : Set Plane) : ℝ := sInf (horizontalProjection K)
def horizontalRight (K : Set Plane) : ℝ := sSup (horizontalProjection K)
def verticalFiber (K : Set Plane) (x : ℝ) : Set ℝ := {y | (x, y) ∈ K}
def capRoof (K : Set Plane) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ horizontalProjection K then sSup (verticalFiber K x) else 0
end AmbidextrousSofa
