module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Doubling
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Analysis.Normed.Module.RCLike.Real

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Foundation.Parabolic.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic space-time geometry

The spatial geometry uses the Euclidean norm on `Fin 3 → ℝ`, defined from the
finite sum of squares.  This is deliberate: the ambient function space's
default norm can be the sup norm, whereas the cylinders here are Euclidean.
-/
@[expose] public section
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
abbrev Vec3 := Fin 3 → ℝ

def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

axiom vec3EuclideanNorm_eq_l2 (v : Vec3) :
    vec3EuclideanNorm v = ‖WithLp.toLp 2 v‖
axiom vec3EuclideanNorm_nonneg (v : Vec3) : 0 ≤ vec3EuclideanNorm v

end CKN.Foundation.Parabolic

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Foundation.Sobolev.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Ambient coordinate carriers

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port keeps only the coordinate carrier needed by the
weak-derivative API and uses the `CKN` namespace.
-/
@[expose] public section
namespace CKN
/-- The native coordinate model of a finite-dimensional real vector space. -/
abbrev Vec (d : ℕ) := Fin d → ℝ
end CKN

end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Foundation.Sobolev.Ambient.Basis ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Coordinate basis for native vectors

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port retains the coordinate basis and reconstruction facts
needed to state coordinate weak derivatives, under the `CKN` namespace.
-/
@[expose] public section
namespace CKN
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

end CKN

end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Pressure.LeibnizLaplacian ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# The Leibniz rule for the spatial Laplacian, in weak form

The paper's identity `eq:leibniz-lap`,
`Δ(η T) = η Δ T + 2 ∂_j η ∂_j T + T Δ η`,
is stated there for a scalar distribution `T` and a smooth `η`.  This file
proves the underlying pointwise second-order product rule for smooth functions
on `Vec3 := Fin 3 → ℝ`, and then integrates it against a locally integrable
weight to obtain the weak (test-function) form used in the paper.

Spatial partial derivatives are ordinary partial derivatives, expressed as the
Fréchet derivative applied to a coordinate basis vector, matching the
convention of `CKN.spatialPartial`.
-/
@[expose] public section
open MeasureTheory Set
open CKN.Foundation.Parabolic
namespace CKN
noncomputable section
/-! ## Spatial partial derivatives and their product rules -/
/-- The `i`th spatial partial derivative `∂_i f`, as the Fréchet derivative applied
to the `i`th coordinate basis vector. -/
def spatialDeriv (f : Vec3 → ℝ) (i : Fin 3) : Vec3 → ℝ :=
  fun x => (fderiv ℝ f x) (basisVec i)

end
end CKN

end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Foundation.Harmonic.NewtonianRepresentation ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal NNReal Topology Interval
open MeasureTheory MeasureTheory.Measure Set Filter
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
/-! The Newtonian kernel representation obtained from the heat semigroup. -/
/-- The positive three-dimensional Newtonian kernel. -/
def newtonianKernel (z : Vec3) : ℝ :=
  1 / (4 * Real.pi * vec3EuclideanNorm z)

end CKN.Foundation.Heat

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Foundation.Harmonic.InteriorBasic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic
set_option autoImplicit false
/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section
namespace CKN.Foundation.Heat
def q (z : Vec3) : ℝ := ∑ i : Fin 3, z i ^ 2

axiom q_eq_vec3Norm_sq (z : Vec3) :
    q z = vec3EuclideanNorm z ^ 2

axiom newtonianKernel_spatialDeriv_formula {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv newtonianKernel i z =
      -(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)

end CKN.Foundation.Heat

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.vccdae5d5e899.CKN.Foundation.Parabolic.Vec3Norm ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic

/-- Each component of a vector in `Vec3` is bounded in absolute value by the Euclidean norm. -/
axiom abs_apply_le_vec3EuclideanNorm (v : Vec3) (i : Fin 3) :
    |v i| ≤ vec3EuclideanNorm v

end CKN.Foundation.Parabolic

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Examples.Example_7115ea4817cf00f2520d_EllipticKernelBounds ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open MeasureTheory Set Filter
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CIV
/-!
# Ball integral of the Newtonian kernel gradient

The gradient `∂ₗN` of the Newtonian kernel is bounded by `(4π)⁻¹` times the Euclidean-norm
power `|z|^{-2}`, so its integral over the Euclidean ball `{y : |y - x| ≤ ρ}` is absolutely
convergent and scales linearly in `ρ`: `∫_{|y-x|≤ρ} |∂ₗN(x - y)| ≤ Cρ`. The scaling identity
`∫_{|z|≤ρ} |z|^{-2} = ρ · ∫_{|z|≤1} |z|^{-2}` is obtained from the Haar-measure scaling formula
`∫ f(c • z) dz = |c|^{-n} ∫ f(z) dz` applied to the indicator of the unit ball. This is an elliptic
kernel estimate of the interior estimates of `lem:aniso:annulus`.
-/
private axiom abs_neg_mul_rpow_nonneg (a b : ℝ) {X : ℝ} (hX : 0 ≤ X) :
    |(-a * b * X)| = |a| * |b| * X
private theorem abs_spatialDeriv_newtonianKernel_le_euclidean {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    |spatialDeriv newtonianKernel i z| ≤ (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
  rw [newtonianKernel_spatialDeriv_formula hz i]
  have hqi : q z ^ (-(3 : ℝ) / 2) = vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
    rw [q_eq_vec3Norm_sq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) from by ring,
      show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) from by norm_num,
      ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
    congr 1
    ring
  rw [hqi]
  have hzpos : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hz0
    exact hz ((WithLp.toLp_eq_zero 2).mp hz0)
  have hnn3 : 0 ≤ vec3EuclideanNorm z ^ (-(3 : ℝ)) :=
    Real.rpow_nonneg (vec3EuclideanNorm_nonneg z) _
  rw [abs_neg_mul_rpow_nonneg (4 * Real.pi)⁻¹ (z i) hnn3]
  have hcoord : |z i| ≤ vec3EuclideanNorm z := abs_apply_le_vec3EuclideanNorm z i
  have hstep : vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
      vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
    have h1 : vec3EuclideanNorm z ^ (1 : ℝ) * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
        vec3EuclideanNorm z ^ ((1 : ℝ) + -(3 : ℝ)) := (Real.rpow_add hzpos _ _).symm
    rw [Real.rpow_one] at h1
    rw [h1]
    norm_num
  calc |(4 * Real.pi)⁻¹| * |z i| * vec3EuclideanNorm z ^ (-(3 : ℝ)) ≤
      |(4 * Real.pi)⁻¹| * vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)) hnn3
    _ = (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ))) := by
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (4 * Real.pi)⁻¹)]
        ring
    _ = (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by rw [hstep]
/-! ## Part 2: integrability and the scaling identity on the Euclidean ball -/
end CIV
