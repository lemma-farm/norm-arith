module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Ambient.Basic ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Ambient carriers

The common finite-dimensional carriers used by the PDE libraries. The
inherited norm on `Vec d` is the finite-product supremum norm; Euclidean
quadratic structure is defined explicitly in `PDEFoundation.Ambient.EuclideanNorm`.
-/
@[expose] public section
namespace PDE
/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Ambient.EuclideanNorm ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Explicit Euclidean norm on native vectors

`PDE.Vec d = Fin d → ℝ` inherits the finite-product supremum norm. This
module supplies the distinct Euclidean dot product, squared norm, and norm
needed by energy estimates.
-/
@[expose] public section
open scoped BigOperators
namespace PDE
/-- The Euclidean dot product on native project vectors. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i
/-- The square of the Euclidean norm on native project vectors. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x
/-- The Euclidean norm on native project vectors. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)

axiom vecEuclideanNorm_smul {d : ℕ} (c : ℝ) (x : Vec d) :
    vecEuclideanNorm (c • x) = |c| * vecEuclideanNorm x

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Geometry.ConvexSegment ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Segment geometry in convex domains

This file provides the affine parametrization of a segment and the elementary
lemmas needed to keep that segment inside a convex domain. It contains no
Sobolev or Poincaré theory.

## Main definitions

- `PDE.segmentBlend`: the point with parameter `t` on the segment from `y` to `x`.

## Main results

- `PDE.segmentBlend_mem`: a segment between two points of a convex set stays in the set.
- `PDE.segmentBlend_mapsTo`: the corresponding `Set.MapsTo` statement.
- `PDE.ray_mem_of_endpoint_mem_of_isOpenBoundedConvexDomain`: a shorter point on a
  nonnegative ray remains in the domain when the endpoint does.
-/
@[expose] public section
namespace PDE
/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t

/-- The segment parametrization in basepoint-plus-displacement form. -/
axiom segmentBlend_eq_add_smul_sub {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = y + t • (x - y)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Ambient.Basis ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Coordinate basis of the native ambient space

The coordinate basis and its exact dot-product and Euclidean-length formulas.
-/
@[expose] public section
namespace PDE
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

axiom vecEuclideanNorm_basisVec {d : ℕ} (i : Fin d) :
    vecEuclideanNorm (basisVec i) = 1

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Sobolev.ClassicalGradient ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Classical gradients in the native ambient space

The inherited norm on `PDE.Vec d` is the finite-product supremum norm. This
file packages the coordinate gradient of a classically differentiable scalar
function as a native vector and relates directional derivatives to the
explicit Euclidean dot product. Quantitative PDE estimates should use the
resulting Euclidean Cauchy--Schwarz inequality, not the operator norm induced
by the inherited product norm.
-/
@[expose] public section
namespace PDE
/-- The coordinate gradient of a scalar function, expressed in the native
vector carrier. -/
noncomputable def classicalGradient {d : ℕ}
    (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => (fderiv ℝ f x) (basisVec i)

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vc98ffab9772d.PDEFoundation.Sobolev.Inequalities.SmoothSegment ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Smooth Euclidean estimates along affine segments

These are the domain-independent fundamental-theorem-of-calculus estimates
used by the diameter-only convex-domain Poincaré proof. Directional
derivatives are paired with `classicalGradient` through the explicit
Euclidean dot product, so no norm from the inherited finite-product metric
enters the estimate.
-/
@[expose] public section
namespace PDE

/-- Jensen along the unit segment followed by Euclidean Cauchy--Schwarz. -/
axiom abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
    {d : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (x y : Vec d) :
    |u x - u y| ^ p ≤
      ∫ t in (0 : ℝ)..1,
        (vecEuclideanNorm
            (classicalGradient u (segmentBlend x t y)) *
          vecEuclideanNorm (x - y)) ^ p

end PDE

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_813b0a51b6097dccb93c_SpatialDifferenceQuotientSmoothL2 ====
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Global `L²` control of smooth spatial difference quotients

This file proves the constant-one whole-space estimate needed before local
cutoffs are introduced.
-/
@[expose] public section
open MeasureTheory

private theorem spatialDifferenceQuotient_sq_le_segmentIntegral
    {d : ℕ} (φ : PDE.Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (k : Fin d) (h : ℝ) (hh : h ≠ 0) (y : PDE.Vec d) :
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 ≤
      ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
  let z : PDE.Vec d := h • PDE.basisVec k
  have hbase := PDE.abs_sub_rpow_le_integral_euclideanGradient_mul_distance_rpow
    (p := (2 : ℝ)) (by norm_num) hφ (y + z) y
  have hnormz : PDE.vecEuclideanNorm z = |h| := by
    rw [show z = h • PDE.basisVec k by rfl,
      PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_basisVec]
    simp
  have hbase' : |φ (y + z) - φ y| ^ (2 : ℝ) ≤
      ∫ t in (0 : ℝ)..1,
        (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ) := by
    simpa only [PDE.segmentBlend_eq_add_smul_sub, add_sub_cancel_left, hnormz] using hbase
  have hsq : 0 < h ^ 2 := sq_pos_of_ne_zero hh
  have hdivide : |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 ≤
      (∫ t in (0 : ℝ)..1,
        (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ)) / h ^ 2 :=
    (div_le_div_iff_of_pos_right hsq).mpr hbase'
  rw [← intervalIntegral.integral_div] at hdivide
  have hrewrite : (fun t : ℝ =>
      (PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) * |h|) ^ (2 : ℝ) / h ^ 2) =
      fun t => PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) ^ 2 := by
    funext t
    rw [Real.rpow_two]
    ring_nf
    rw [sq_abs]
    field_simp
  rw [hrewrite] at hdivide
  have hleft : ((φ (y + z) - φ y) / h) ^ 2 =
      |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 := by
    rw [Real.rpow_two, sq_abs]
    field_simp
  calc
    ((φ (y + h • PDE.basisVec k) - φ y) / h) ^ 2 =
        ((φ (y + z) - φ y) / h) ^ 2 := by simp only [z]
    _ = |φ (y + z) - φ y| ^ (2 : ℝ) / h ^ 2 := hleft
    _ ≤ ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm (PDE.classicalGradient φ (y + t • z)) ^ 2 := hdivide
    _ = ∫ t in (0 : ℝ)..1,
        PDE.vecEuclideanNorm
          (PDE.classicalGradient φ (y + t • (h • PDE.basisVec k))) ^ 2 := by
      simp only [z]
