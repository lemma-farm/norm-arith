module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Caps
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
theorem isCompact_horizontalProjection {K : Set Plane} (hK : IsCompact K) :
    IsCompact (horizontalProjection K) :=
  hK.image continuous_fst
def horizontalLeft (K : Set Plane) : ℝ := sInf (horizontalProjection K)
def horizontalRight (K : Set Plane) : ℝ := sSup (horizontalProjection K)
/-- A compact connected set has its exact horizontal projection interval. -/
theorem horizontalProjection_eq_Icc_of_isConnected {S : Set Plane}
    (hcompact : IsCompact S) (hconnected : IsConnected S) :
    horizontalProjection S = Icc (horizontalLeft S) (horizontalRight S) :=
  eq_Icc_of_connected_compact (hconnected.image Prod.fst continuous_fst.continuousOn)
    (isCompact_horizontalProjection hcompact)
/-- A cap has its exact horizontal projection interval. -/
theorem IsDownwardCap.horizontalProjection_eq_Icc {U : Set Plane} (hU : IsDownwardCap U) :
    horizontalProjection U = Icc (horizontalLeft U) (horizontalRight U) :=
  horizontalProjection_eq_Icc_of_isConnected hU.isCompact (hU.convex.isConnected hU.nonempty)
def verticalFiber (K : Set Plane) (x : ℝ) : Set ℝ := {y | (x, y) ∈ K}
theorem verticalFiber_nonempty_iff {K : Set Plane} {x : ℝ} :
    (verticalFiber K x).Nonempty ↔ x ∈ horizontalProjection K :=
  ⟨fun ⟨y, hy⟩ => ⟨(x, y), hy, rfl⟩, by rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp⟩⟩
theorem isCompact_verticalFiber {K : Set Plane} (hK : IsCompact K) (x : ℝ) :
    IsCompact (verticalFiber K x) := by
  convert (hK.inter_right (isClosed_eq continuous_fst continuous_const)).image continuous_snd
  ext y
  exact ⟨fun hy => ⟨(x, y), ⟨hy, rfl⟩, rfl⟩, by rintro ⟨p, ⟨hp, rfl⟩, rfl⟩; exact hp⟩
/-- The attained fiber maximum, extended by zero off the horizontal projection. -/
def capRoof (K : Set Plane) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ horizontalProjection K then sSup (verticalFiber K x) else 0
theorem capRoof_mem {K : Set Plane} (hK : IsCompact K) {x : ℝ}
    (hx : x ∈ horizontalProjection K) : (x, capRoof K x) ∈ K := by
  simpa only [capRoof, hx, ↓reduceIte, verticalFiber, Set.mem_ofPred_eq] using
    (isCompact_verticalFiber hK x).sSup_mem (verticalFiber_nonempty_iff.mpr hx)
theorem le_capRoof {K : Set Plane} (hK : IsCompact K) {x y : ℝ}
    (hxy : (x, y) ∈ K) : y ≤ capRoof K x := by
  simpa only [capRoof, show x ∈ horizontalProjection K from ⟨(x, y), hxy, rfl⟩, ↓reduceIte] using
    le_csSup (isCompact_verticalFiber hK x).bddAbove hxy
end AmbidextrousSofa
