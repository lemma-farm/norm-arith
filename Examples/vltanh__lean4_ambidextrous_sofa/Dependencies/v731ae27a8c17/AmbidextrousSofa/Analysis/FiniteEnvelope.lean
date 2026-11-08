module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.v731ae27a8c17.AmbidextrousSofa.Analysis.RoofContinuity
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
end WallExpr
end AmbidextrousSofa
