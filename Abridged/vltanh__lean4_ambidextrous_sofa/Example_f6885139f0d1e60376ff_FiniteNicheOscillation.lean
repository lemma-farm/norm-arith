module

public import Mathlib
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Plane ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Coordinate plane and the two unit corridors

The plane is represented by a pair of real coordinates, with its product
topology and product Lebesgue measure. The product norm is not the Euclidean
norm. Rotations are therefore defined by their coordinate formula.

The lower corridor is the union of the incoming horizontal arm and the
downward outgoing arm. The upper corridor is its reflection in `y = 1 / 2`.
-/
noncomputable section
namespace AmbidextrousSofa
abbrev Plane := ℝ × ℝ

def unitStrip : Set Plane := {p | 0 ≤ p.2 ∧ p.2 ≤ 1}

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Caps ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual convex hulls and downward caps

`IsDownwardCap` describes the broad scalar domain: nonempty compact convex
sets in the unit strip, closed downward to the baseline. It permits subunit
height, zero width, asymmetry, and nonsmooth boundary.

`upperCap` fills vertically down from a set. The lemmas below establish its
elementary containment, projection, and fixed-point properties. Compactness,
convexity, support functions, and integral scores for hull-derived caps remain
separate formalization tasks.
-/
namespace AmbidextrousSofa
def horizontalProjection (S : Set Plane) : Set ℝ := Prod.fst '' S
structure IsDownwardCap (U : Set Plane) : Prop where
  nonempty : U.Nonempty
  isCompact : IsCompact U
  convex : Convex ℝ U
  inStrip : U ⊆ unitStrip
  downward : ∀ p ∈ U, ∀ y : ℝ, 0 ≤ y → y ≤ p.2 → (p.1, y) ∈ U

end AmbidextrousSofa

end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.CapGeometry ====
public section
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

/-- The attained fiber maximum, extended by zero off the horizontal projection. -/
def capRoof (K : Set Plane) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ horizontalProjection K then sSup (verticalFiber K x) else 0

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Geometry.Support ====
public section
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

def support (K : Set Plane) (v : Plane) : ℝ := sSup ((fun p => coordDot p v) '' K)

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Measure.Partition ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Integrated spatial partition and its equality conditions

This module passes from the pointwise identities to real Lebesgue integrals.
The horizontal projection is split into a measurable middle set and its
complement. Equal measure of those pieces cancels the constant terms. The
standard middle half of a closed interval is proved to have that property.

The resulting spatial scores are genuine integrals of roofs and barriers.
The exact identity holds even when some signed fibers are negative. Only
the final ordinary-area corollaries use nonnegative physical fibers and
measurable envelope containment. No universal sharp bound on a spatial
score is postulated or proved here.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
/-! ## The middle half has the required measure -/
/-- The middle half of the closed horizontal interval `[l,r]`. -/
def middleHalfInterval (l r : ℝ) : Set ℝ :=
  Icc (l + (r - l) / 4) (r - (r - l) / 4)
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Measure.CapScore ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual cap scores and the elementary width branch

The scalar score is now instantiated with the actual cap roof, its actual
horizontal projection endpoints, and the full partial barrier including the
terminal wall. All those functions have the measurability and integrability
properties established in the preceding modules.

This file proves the elementary bound `capScore U α ≤ capWidth U / 2`.
It uses only the cap's height at most one and the barrier's nonnegativity.
Consequently widths strictly below `M` are a strictly suboptimal scalar
branch. No universal bound for larger widths is assumed or claimed.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
def capWidth (U : Set Plane) : ℝ := horizontalRight U - horizontalLeft U
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.FiniteEnvelope ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Exact differentiation of finite wall envelopes

A finite polygon roof is a minimum of affine lines. A finite physical
niche is a maximum of two-line minima and the zero line. `WallExpr` records
these literal min/max expressions. Distinct line slopes imply that ties
between different sources occur only at finitely many abscissae. Away from
those ties the selected source is locally constant under a support-height
perturbation. A uniform parameter Lipschitz bound justifies differentiating
the ordinary spatial integral.

The resulting derivative is the integral of the selected source's actual
height velocity. In particular a single moved wall contributes its height
velocity times its exposed horizontal length. No differentiability of a
maximum at a tie or convergence of polygonal arclength is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal
open scoped Topology
namespace AmbidextrousSofa
/-- A literal finite expression of wall heights. Repeated leaves are allowed. -/
inductive WallExpr (ι : Type*) where
  | leaf (i : ι)
  | minimum (left right : WallExpr ι)
  | maximum (left right : WallExpr ι)
namespace WallExpr
variable {ι : Type*}
def eval : WallExpr ι → (ι → ℝ) → ℝ
  | leaf i, v => v i
  | minimum e f, v => min (eval e v) (eval f v)
  | maximum e f, v => max (eval e v) (eval f v)
/-- A selected attaining leaf; ties consistently select the left minimum
and the right maximum. The integral result is independent of these ties. -/
def source : WallExpr ι → (ι → ℝ) → ι
  | leaf i, _ => i
  | minimum e f, v => if eval e v ≤ eval f v then source e v else source f v
  | maximum e f, v => if eval e v ≤ eval f v then source f v else source e v

def sourceDensity (e : WallExpr ι) (a b w : ι → ℝ) (x : ℝ) : ℝ :=
  w (e.source (fun i => a i * x + b i))

def sourceSet (e : WallExpr ι) (a b : ι → ℝ) (j : ι) : Set ℝ :=
  {x | e.source (fun i => a i * x + b i) = j}

end WallExpr
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.PolygonVariation ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual finite polygon support variations

`upperPolygon` is a bounded intersection of the unit strip, two actual
horizontal endpoint walls, and finitely many upper supporting halfplanes.
The outward variation changes one halfplane parameter. Every unchanged
support remains exact, while a strict point in the moved face gives an
attaining point for the increased support. Such a strict point is derived
from any two distinct points of the face when the other normals are
nonparallel; it is not a separate variational assumption.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
/-- The actual set cut out by a finite upper support system and the fixed box. -/
def upperPolygon (l r : ℝ) (normal : ι → Plane) (height : ι → ℝ) : Set Plane :=
  (Icc l r ×ˢ Icc (0 : ℝ) 1) ∩ ⋂ i, {p | coordDot p (normal i) ≤ height i}

end FinitePolygon
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.PolygonEnvelope ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Finite expressions for actual polygon roofs and hallway barriers

The outer roof and the inner wall system use the same normal indices. A
source that occurs in several corners or also supplies the proper terminal
wall is represented by the same leaf. This keeps equal slopes from being
mistaken for different moving sources.

The zero leaf is the top wall in the outer expression and the baseline in
the inner expression. All other leaves are actual supporting halfplanes.
On the actual polygon projection the outer expression equals `capRoof`.
The inner expression equals the literal maximum of the sampled physical
corners and the terminal wall. No contact ordering is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
def roofExprList : List ι → WallExpr (Option ι)
  | [] => WallExpr.leaf none
  | i :: is => WallExpr.minimum (WallExpr.leaf (some i)) (roofExprList is)
def roofExpr [Fintype ι] : WallExpr (Option ι) :=
  roofExprList (Finset.univ.toList)

def wallSlope (normal : ι → Plane) : Option ι → ℝ
  | none => 0
  | some i => -(normal i).1 / (normal i).2
def roofIntercept (normal : ι → Plane) (height : ι → ℝ) : Option ι → ℝ
  | none => 1
  | some i => height i / (normal i).2
def barrierIntercept (normal : ι → Plane) (height : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => (height i - 1) / (normal i).2
def roofEnvelope [Fintype ι] (normal : ι → Plane) (height : ι → ℝ) (x : ℝ) : ℝ :=
  (roofExpr (ι := ι)).eval (fun i => wallSlope normal i * x + roofIntercept normal height i)

def supportWall (U : Set Plane) (n : Plane) (x : ℝ) : ℝ :=
  (support U n - 1 - x * n.1) / n.2
def cornerExpr (ij : ι × ι) : WallExpr (Option ι) :=
  WallExpr.minimum (WallExpr.leaf (some ij.1)) (WallExpr.leaf (some ij.2))
def nicheExpr : List (ι × ι) → WallExpr (Option ι)
  | [] => WallExpr.leaf none
  | ij :: rest => WallExpr.maximum (cornerExpr ij) (nicheExpr rest)
def barrierExpr (corners : List (ι × ι)) (terminal : Option ι) : WallExpr (Option ι) :=
  match terminal with
  | none => nicheExpr corners
  | some j => WallExpr.maximum (nicheExpr corners) (WallExpr.leaf (some j))
/-- Literal sampled corners, always clipped from below at zero. -/
def finiteNiche (U : Set Plane) (normal : ι → Plane) : List (ι × ι) → ℝ → ℝ
  | [], _ => 0
  | ij :: rest, x => max (min (supportWall U (normal ij.1) x)
      (supportWall U (normal ij.2) x)) (finiteNiche U normal rest x)
/-- A proper terminal wall remains a whole wall. It shares its source index
with any corner in which the same support is used. -/
def finiteBarrier (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (x : ℝ) : ℝ :=
  match terminal with
  | none => finiteNiche U normal corners x
  | some j => max (finiteNiche U normal corners x) (supportWall U (normal j) x)

end FinitePolygon
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.Circumscription ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Actual finite support circumscription

Intersecting the sampled support halfplanes with the actual projection
box produces a larger downward cap. Every sampled support remains exact,
and the actual projection is unchanged. Consequently the sampled physical
barrier and any sampled support penalty remain unchanged while the charged
exterior roof can only increase. These are the recovery competitors for
finite selected spatial maximizers.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}
def circumscription (U : Set Plane) (normal : ι → Plane) : Set Plane :=
  upperPolygon (horizontalLeft U) (horizontalRight U) normal (fun i => support U (normal i))

end FinitePolygon
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.ExposureMoments ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Literal source masses and the translation balance

Every mass in this file is the Lebesgue measure of the actual selected
source set of a finite min/max expression. Integrating all wall velocities
gives a finite weighted sum of these masses. Horizontal translation then
gives the exact signed endpoint balance. No limiting niche graph or
identification of a weak limit with graph arclength is used.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace WallExpr
variable {ι : Type*}
def sourceMass (e : WallExpr ι) (a b : ι → ℝ) (l r : ℝ) (j : ι) : ℝ :=
  volume.real (Ioc l r ∩ e.sourceSet a b j)

end WallExpr
/-- Total wall variation, using the two charged exterior source masses
and the central source masses. The two expressions can have different
finite source types. -/
def finiteSourceVariation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (outer : WallExpr ι) (inner : WallExpr κ) (a b : ι → ℝ) (c d : κ → ℝ)
    (l r : ℝ) (w : ι → ℝ) (v : κ → ℝ) : ℝ :=
  (∑ i, (outer.sourceMass a b l (l + (r - l) / 4) i +
    outer.sourceMass a b (r - (r - l) / 4) r i) * w i) -
      ∑ j, inner.sourceMass c d (l + (r - l) / 4) (r - (r - l) / 4) j * v j

end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.FiniteSpatialVariation ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Spatial variation of literal finite wall expressions

A finite minimum/maximum of affine walls is globally Lipschitz. Away
from the finite set of ties, its spatial derivative is the selected
wall's slope. The absolutely continuous fundamental theorem therefore
identifies slope integrals with endpoint differences. In particular,
the two-sided height at any interior point is bounded by the integral
of the absolute selected slopes, with no interpretation of a limiting
source measure as graph arclength.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace WallExpr
variable {ι : Type*}
def affineGraph (e : WallExpr ι) (a b : ι → ℝ) (x : ℝ) : ℝ :=
  e.eval (fun i => a i * x + b i)

set_option linter.unusedVariables false in
axiom _root_.AmbidextrousSofa.WallExpr.peak_le_integral_abs_sourceSlope.{w_u_1} : ∀ {ι : Type w_u_1} [Fintype ι] (e : AmbidextrousSofa.WallExpr ι) (a b : ι → ℝ),
  Function.Injective a →
    ∀ {l x r : ℝ},
      l ≤ x →
        x ≤ r →
          2 * e.affineGraph a b x - e.affineGraph a b l - e.affineGraph a b r ≤
            ∫ (y : ℝ) in l..r, e.sourceDensity a b (fun (i : ι) ↦ |a i|) y
end WallExpr
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.ErosionMoments ====
public section
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Source moments of literal horizontal erosions

The right and left moments use the actual finite selected-source masses.
Their velocities are the positive horizontal normal components appearing
in the exact set identities for horizontal erosion. The displayed eroded
halfplanes need not be attained: their barrier is an upper bound on the
actual eroded barrier, which gives the correct comparison direction.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι κ : Type*}
def heightVelocity (normal : ι → Plane) (z : ι → ℝ) : Option ι → ℝ
  | none => 0
  | some i => z i / (normal i).2
def rightErosionVelocity (normal : ι → Plane) : Option ι → ℝ :=
  heightVelocity normal (fun i => -max (normal i).1 0)
def leftErosionVelocity (normal : ι → Plane) : Option ι → ℝ :=
  heightVelocity normal (fun i => -max (-(normal i).1) 0)

def finiteRightMoment [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    (horizontalLeft U) (horizontalRight U)
    (rightErosionVelocity normal) (rightErosionVelocity normal)
def finiteLeftMoment [Fintype ι] (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) : ℝ :=
  finiteSourceVariation (roofExpr (ι := ι)) (barrierExpr corners terminal)
    (wallSlope normal) (roofIntercept normal (fun i => support U (normal i)))
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i)))
    (horizontalLeft U) (horizontalRight U)
    (leftErosionVelocity normal) (leftErosionVelocity normal)
end FinitePolygon
end AmbidextrousSofa

end
end
end

-- ==== Examples.vltanh__lean4_ambidextrous_sofa.Examples.Example_f6885139f0d1e60376ff_FiniteNicheOscillation ====
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# Finite niche oscillation and the actual erosion moments

Adding the right and left erosion velocities gives minus the absolute
spatial slope of each wall. Thus the sum of the literal erosion moments
is the inner absolute-slope mass minus the two outer masses. Combining
the finite peak inequality with the concave-roof variation bound gives
a pointwise estimate on every sampled physical niche, including all
ties and floor segments.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa
namespace FinitePolygon
variable {ι : Type*}


set_option linter.unusedVariables false in
theorem finiteBarrier_peak_le_end_heights_and_moments [Fintype ι]
    {U : Set Plane} (hU : IsDownwardCap U) (normal : ι → Plane)
    (hnormal : ∀ i, 0 < (normal i).2) (hinjective : Function.Injective (wallSlope normal))
    (hpoly : U = circumscription U normal) (corners : List (ι × ι)) (terminal : Option ι)
    (hwidth : 0 < capWidth U) {x : ℝ}
    (hx : x ∈ middleHalfInterval (horizontalLeft U) (horizontalRight U)) 
    (h_AmbidextrousSofa_FinitePolygon_roofExpr_eval_le : ∀ {ι : Type u_1} [inst : Fintype ι] (v : Option ι → ℝ) (i : Option ι),
      AmbidextrousSofa.FinitePolygon.roofExpr.eval v ≤ v i)
    (h_AmbidextrousSofa_FinitePolygon_eqOn_roofEnvelope_of_circumscription : ∀ {ι : Type u_1} [inst : Fintype ι] {U : Set AmbidextrousSofa.Plane},
      AmbidextrousSofa.IsDownwardCap U →
        ∀ (normal : ι → AmbidextrousSofa.Plane),
          (∀ (i : ι), 0 < (normal i).2) →
            U = AmbidextrousSofa.FinitePolygon.circumscription U normal →
              Set.EqOn
                (AmbidextrousSofa.FinitePolygon.roofEnvelope normal fun (i : ι) ↦
                  AmbidextrousSofa.support U (normal i))
                (AmbidextrousSofa.capRoof U)
                (Set.Icc (AmbidextrousSofa.horizontalLeft U) (AmbidextrousSofa.horizontalRight U)))
    (h_AmbidextrousSofa_FinitePolygon_affineGraph_barrier : ∀ {ι : Type u_1} (U : Set AmbidextrousSofa.Plane) (normal : ι → AmbidextrousSofa.Plane)
      (corners : List (ι × ι)) (terminal : Option ι),
      (AmbidextrousSofa.FinitePolygon.barrierExpr corners terminal).affineGraph
          (AmbidextrousSofa.FinitePolygon.wallSlope normal)
          (AmbidextrousSofa.FinitePolygon.barrierIntercept normal fun (i : ι) ↦
            AmbidextrousSofa.support U (normal i)) =
        AmbidextrousSofa.FinitePolygon.finiteBarrier U normal corners terminal)
    (h_AmbidextrousSofa_FinitePolygon_erosionMoments_add_eq_neg_absolute_variation : ∀ {ι : Type u_1} [inst : Fintype ι] (U : Set AmbidextrousSofa.Plane)
      (normal : ι → AmbidextrousSofa.Plane),
      (∀ (i : ι), 0 < (normal i).2) →
        ∀ (corners : List (ι × ι)) (terminal : Option ι),
          AmbidextrousSofa.FinitePolygon.finiteRightMoment U normal corners terminal +
              AmbidextrousSofa.FinitePolygon.finiteLeftMoment U normal corners terminal =
            -AmbidextrousSofa.finiteSourceVariation AmbidextrousSofa.FinitePolygon.roofExpr
                (AmbidextrousSofa.FinitePolygon.barrierExpr corners terminal)
                (AmbidextrousSofa.FinitePolygon.wallSlope normal)
                (AmbidextrousSofa.FinitePolygon.roofIntercept normal fun (i : ι) ↦
                  AmbidextrousSofa.support U (normal i))
                (AmbidextrousSofa.FinitePolygon.wallSlope normal)
                (AmbidextrousSofa.FinitePolygon.barrierIntercept normal fun (i : ι) ↦
                  AmbidextrousSofa.support U (normal i))
                (AmbidextrousSofa.horizontalLeft U) (AmbidextrousSofa.horizontalRight U)
                (fun (i : Option ι) ↦ |AmbidextrousSofa.FinitePolygon.wallSlope normal i|)
                fun (i : Option ι) ↦ |AmbidextrousSofa.FinitePolygon.wallSlope normal i|)
    (h_AmbidextrousSofa_FinitePolygon_roof_outer_absSlope_integrals_le : ∀ {ι : Type u_1} [inst : Fintype ι] (a b : Option ι → ℝ),
      Function.Injective a →
        ∀ {l u v r H : ℝ},
          l ≤ u →
            u < v →
              v ≤ r →
                (∀ x ∈ Set.Icc l r, AmbidextrousSofa.FinitePolygon.roofExpr.affineGraph a b x ≤ H) →
                  (∫ (x : ℝ) in l..u,
                        AmbidextrousSofa.FinitePolygon.roofExpr.sourceDensity a b
                          (fun (i : Option ι) ↦ |a i|) x) +
                      ∫ (x : ℝ) in v..r,
                        AmbidextrousSofa.FinitePolygon.roofExpr.sourceDensity a b
                          (fun (i : Option ι) ↦ |a i|) x ≤
                    2 * H -
                          |AmbidextrousSofa.FinitePolygon.roofExpr.affineGraph a b v -
                              AmbidextrousSofa.FinitePolygon.roofExpr.affineGraph a b u| -
                        AmbidextrousSofa.FinitePolygon.roofExpr.affineGraph a b l -
                      AmbidextrousSofa.FinitePolygon.roofExpr.affineGraph a b r)
    (h_AmbidextrousSofa_finiteSourceVariation_eq_integrals : ∀ {ι κ : Type u_1} [inst : Fintype ι] [inst_1 : Fintype κ] (outer : AmbidextrousSofa.WallExpr ι)
      (inner : AmbidextrousSofa.WallExpr κ) (a b w : ι → ℝ) (c d v : κ → ℝ) {l r : ℝ},
      l ≤ r →
        AmbidextrousSofa.finiteSourceVariation outer inner a b c d l r w v =
          ((∫ (x : ℝ) in l..l + (r - l) / 4, outer.sourceDensity a b w x) +
              ∫ (x : ℝ) in r - (r - l) / 4..r, outer.sourceDensity a b w x) -
            ∫ (x : ℝ) in l + (r - l) / 4..r - (r - l) / 4, inner.sourceDensity c d v x)
    :
    2 * finiteBarrier U normal corners terminal x -
      finiteBarrier U normal corners terminal
        (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4) -
      finiteBarrier U normal corners terminal
        (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) ≤
      2 - |capRoof U (horizontalRight U - (horizontalRight U - horizontalLeft U) / 4) -
        capRoof U (horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4)| -
        capRoof U (horizontalLeft U) - capRoof U (horizontalRight U) +
        finiteRightMoment U normal corners terminal + finiteLeftMoment U normal corners terminal := by
  have hlr : horizontalLeft U < horizontalRight U := sub_pos.mp hwidth
  have houter := h_AmbidextrousSofa_FinitePolygon_roof_outer_absSlope_integrals_le (wallSlope normal)
    (roofIntercept normal (fun i => support U (normal i))) hinjective (H := 1)
    (show horizontalLeft U ≤ horizontalLeft U + (horizontalRight U - horizontalLeft U) / 4 by
      linarith)
    (show _ < horizontalRight U - (horizontalRight U - horizontalLeft U) / 4 by linarith)
    (show _ ≤ horizontalRight U by linarith)
    (fun z _ => (h_AmbidextrousSofa_FinitePolygon_roofExpr_eval_le _ none).trans_eq (by simp [wallSlope, roofIntercept]))
  have hroof : ∀ z ∈ Icc (horizontalLeft U) (horizontalRight U), (roofExpr (ι := ι)).affineGraph
      (wallSlope normal) (roofIntercept normal (fun i => support U (normal i))) z = capRoof U z :=
    h_AmbidextrousSofa_FinitePolygon_eqOn_roofEnvelope_of_circumscription hU normal hnormal hpoly
  rw [hroof _ ⟨by linarith only [hlr], by linarith only [hlr]⟩,
    hroof _ ⟨by linarith only [hlr], by linarith only [hlr]⟩,
    hroof _ ⟨le_rfl, hlr.le⟩, hroof _ ⟨hlr.le, le_rfl⟩] at houter
  have hpeak := (barrierExpr corners terminal).peak_le_integral_abs_sourceSlope
    (wallSlope normal) (barrierIntercept normal (fun i => support U (normal i))) hinjective
    hx.1 hx.2
  rw [h_AmbidextrousSofa_FinitePolygon_affineGraph_barrier] at hpeak
  have hbalance := h_AmbidextrousSofa_FinitePolygon_erosionMoments_add_eq_neg_absolute_variation U normal hnormal corners terminal
  rw [h_AmbidextrousSofa_finiteSourceVariation_eq_integrals _ _ _ _ _ _ _ _ hlr.le] at hbalance
  linarith
end FinitePolygon
end AmbidextrousSofa
