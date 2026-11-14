module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CKN.Foundation.Parabolic.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
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

def ParabolicPoint := Vec3 × ℝ

def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

def vec3Ball (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) < r}

end CKN.Foundation.Parabolic

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.Meridional ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The point `(x₁, 0, x₃)` of the meridional plane `{x₂ = 0}`. -/
def meridional (x₁ x₃ : ℝ) : Vec3 := ![x₁, 0, x₃]
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CKN.Statements.SpaceTimeSet ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
set_option autoImplicit false
open CKN.Foundation.Parabolic
namespace CKN
/-- The open space-time carrier `Ω × I` from paper label `def:sws`. -/
def spaceTimeSet (Ω : Set Vec3) (I : Set ℝ) : Set ParabolicPoint := Ω ×ˢ I
end CKN

end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.UnitCylinder ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open Set
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The unit parabolic cylinder `Q = B(1) × (-1, 0)` on which the solutions of
arXiv:2609.20803 live; its upper time endpoint `t = 0` is the blow-up time. -/
def unitCylinder : Set ParabolicPoint := spaceTimeSet (vec3Ball 0 1) (Ioo (-1) 0)
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CKN.Foundation.Sobolev.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CKN.Foundation.Sobolev.Ambient.Basis ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CKN.Statements.SpatialPartial ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
/-- Factor-wise spatial derivative on the ordinary product space described in docs/DESIGN_NOTES.md. -/
def spatialPartial (g : ParabolicPoint → ℝ) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  (fderiv ℝ (fun x : Vec3 => g (x, z.2)) z.1) (basisVec i)
end CKN

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.RadialQuotient ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The quotient `u_r / r` read on the meridional plane: `u₁ / x₁` off the axis and `∂₁ u₁` on
it. For a field that is smooth and axisymmetric, `u₁` vanishes on the axis, so the axis value is
the limit of `u₁ / x₁`: this is the manuscript's "`u_r/r` extended continuously across the axis"
(paragraph after `eq:aniso:G`; design note R7). -/
def radialQuotient (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  if z.1 0 = 0 then CKN.spatialPartial (fun w => u w 0) 0 z else u z 0 / z.1 0
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.RotZ ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The rotation `Q_φ` through the angle `φ` about the `z`-axis. -/
def rotZ (φ : ℝ) (x : Vec3) : Vec3 :=
  ![Real.cos φ * x 0 - Real.sin φ * x 1, Real.sin φ * x 0 + Real.cos φ * x 1, x 2]
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.RotField ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The rotated field `(ℛ_φ u)(x, t) = Q_φ u(Q_φ⁻¹ x, t)` of `eq:interior:average`. -/
def rotField (φ : ℝ) (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  rotZ φ (u (rotZ (-φ) z.1, z.2))
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.AngularMean ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open MeasureTheory
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The angular mean `𝒫u = (2π)⁻¹ ∫₀^{2π} ℛ_φ u dφ` of `eq:interior:average`, the
axisymmetric part of a field. -/
def angularMean (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : Vec3 :=
  (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), rotField φ u z
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v776d4fd04eec.CIV.Statements.IsAxisymmetricOn ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CIV
/-- A field is axisymmetric on a set when its non-axisymmetric part `w = u - 𝒫u`
vanishes there (Section `sec:aniso:notation`). -/
def IsAxisymmetricOn (u : ParabolicPoint → Vec3) (S : Set ParabolicPoint) : Prop :=
  ∀ z ∈ S, angularMean u z = u z
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Examples.Example_057e7749dddbded575f6_AxisQuotients ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# The axis quotient, its integral representation, and the three-term selection

This file publishes the representation of the radial quotient `u_r / r` on the meridional
plane as an average of `∂_r u_r` along the segment from the axis (the paragraph after
`eq:aniso:circulation:pde`), together with the pointwise bounds this representation gives
on that segment, and the reflection-symmetric three-term selection used when
`MeridionalSmallness` fails (the paragraph after `eq:aniso:zoom:selected`).
-/
@[expose] public section
open Set Filter Topology
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-! ### Smoothness and differentiability of an axial slice, at a general component -/

/-! ### The meridional segment through the axis -/

/-! ### The integral representation of the radial quotient -/
/-- The manuscript's `u_r/r`, extended across the axis, is the average of the radial
derivative `∂_r u_r` along the segment from the axis to `(x₁, x₃)` (the paragraph after
`eq:aniso:circulation:pde`). Public form of the `radialQuotient_eq_integral`. -/
axiom radialQuotient_eq_integral (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) :
    radialQuotient u (meridional x₁ x₃, t) =
      ∫ s in (0:ℝ)..1, spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)
/-! ### Bound 1: the radial quotient on a segment through the axis -/
/-- `|u_r/r| ≤ M` at `(x₁, x₃)` whenever `|∂_r u_r| ≤ M` along the segment
`{(s x₁, x₃) : s ∈ [0, 1]}` from the axis, via the integral representation
`radialQuotient_eq_integral` (the paragraph after `eq:aniso:circulation:pde`). -/
theorem abs_radialQuotient_le_of_segment_bound (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ M : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1,
      |spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t)| ≤ M) :
    |radialQuotient u (meridional x₁ x₃, t)| ≤ M := by
  rw [radialQuotient_eq_integral u t hu haxi ht x₁ x₃ hx]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (C := M)
    (f := fun s => spatialPartial (fun w => u w 0) 0 (meridional (s * x₁) x₃, t))
    (fun s hs => by
      rw [uIoc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hs
      simpa [Real.norm_eq_abs] using hM s ⟨hs.1.le, hs.2⟩)
  simpa [Real.norm_eq_abs] using hbound
/-! ### Second partial derivatives along the meridional segment -/
end CIV
