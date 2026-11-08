module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v9da09a8d4ab9.AmbidextrousSofa.Analysis.ExposureMoments
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
theorem affineEnvelope_barrier_zero (U : Set Plane) (normal : ι → Plane)
    (corners : List (ι × ι)) (terminal : Option ι) (w : Option ι → ℝ) :
    (barrierExpr corners terminal).affineEnvelope (wallSlope normal)
        (barrierIntercept normal (fun i => support U (normal i))) w 0 =
      finiteBarrier U normal corners terminal := by
  funext x
  rw [finiteBarrier_eq_eval normal _ (fun _ => rfl)]
  simp only [WallExpr.affineEnvelope, zero_mul, add_zero]
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
