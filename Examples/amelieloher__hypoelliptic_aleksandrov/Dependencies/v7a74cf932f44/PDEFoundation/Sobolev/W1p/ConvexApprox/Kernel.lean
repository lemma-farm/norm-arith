module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Measure.AffineVolume
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v7a74cf932f44.PDEFoundation.Sobolev.W1p.ConvexApprox.Geometry
public import Mathlib
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Convex-domain smoothing kernels

This file defines the normalized smooth kernel and the affine
convex-approximation operator. It also records the exact positive-dilation
Jacobian formulas and the convolution representation used by later smoothness,
weak-derivative, and convergence modules.
-/
@[expose] public section
open scoped Pointwise Convolution
namespace PDE
/-- Cache smooth-bump existence on native vectors for this module and its
transitive importers. -/
private instance instHasContDiffBumpVec (d : ℕ) :
    HasContDiffBump (Vec d) :=
  inferInstance
/-- A nonnegative smooth unit-mass kernel supported in the closed unit ball
for the inherited native-vector norm. -/
structure IsConvexApproxKernel {d : ℕ} (ρ : Vec d → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) ρ
  compactSupport : HasCompactSupport ρ
  support_subset_closedBall :
    tsupport ρ ⊆ Metric.closedBall (0 : Vec d) 1
  nonneg : ∀ z, 0 ≤ ρ z
  setIntegral_one : ∫ z in tsupport ρ, ρ z = 1
namespace IsConvexApproxKernel
theorem continuous {d : ℕ} {ρ : Vec d → ℝ}
    (hρ : IsConvexApproxKernel ρ) :
    Continuous ρ :=
  hρ.smooth.continuous
end IsConvexApproxKernel
namespace ContDiffBump
end ContDiffBump
end PDE
