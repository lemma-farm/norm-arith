module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Geometry.CapGeometry
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Support functions of actual planar sets

The support is defined directly from the coordinate dot product and a real
supremum. Compactness supplies boundedness and attainment; none of those facts
is stored as an extra certificate. Convex-hull invariance is proved from the
minimality of the actual convex hull. Upward support is preserved by downward
filling, which is the support identity needed by the scalar cap reduction.
-/
noncomputable section
open Set
namespace AmbidextrousSofa
/-- Euclidean coordinate pairing, independent of the product norm. -/
def coordDot (p v : Plane) : ℝ := p.1 * v.1 + p.2 * v.2
/-- Support in an arbitrary vector direction; meaningful on every compact nonempty set. -/
def support (K : Set Plane) (v : Plane) : ℝ := sSup ((fun p => coordDot p v) '' K)
def unitNormal (θ : ℝ) : Plane := (Real.cos θ, Real.sin θ)
end AmbidextrousSofa
