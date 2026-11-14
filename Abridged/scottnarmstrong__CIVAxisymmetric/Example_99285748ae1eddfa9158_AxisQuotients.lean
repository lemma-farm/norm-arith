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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CKN.Foundation.Parabolic.Basic ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Statements.Meridional ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CKN.Statements.SpaceTimeSet ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Statements.UnitCylinder ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CKN.Foundation.Sobolev.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CKN.Foundation.Sobolev.Ambient.Basis ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Identities.MeridionalSlices ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# The meridional segment through the axis

The continuity statements for `u_r / r` and for `ω_θ / r` across the axis are all proved the
same way: the quotient at `(x₁, 0, x₃)` is an average of a radial derivative along the segment
`s ↦ (s x₁, 0, x₃)`, `s ∈ [0, 1]`, which stays inside the unit ball. This module collects the
elementary facts about that segment and about the clamp `s ↦ max 0 (min s 1)` used to extend
the segment parameter to all of `ℝ`, so that the several quotient modules share one copy.
-/
@[expose] public section
open Set
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV

/-- The first coordinate of a meridional point is its axis distance. -/
axiom meridional_apply_zero (x₁ x₃ : ℝ) : meridional x₁ x₃ 0 = x₁

end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CKN.Statements.SpatialPartial ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Statements.RotZ ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Statements.RotField ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Statements.AngularMean ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Statements.IsAxisymmetricOn ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CKN.Statements.SpatialSecondPartial ====
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
/-- The iterated spatial derivative used in the local energy inequality. -/
def spatialSecondPartial (g : ParabolicPoint → ℝ) (i j : Fin 3)
    (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => spatialPartial g i w) j z
end CKN

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Identities.Axisymmetric ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# Infinitesimal consequences of rotation invariance

An axisymmetric field on the unit cylinder is equivariant, `u (Q_φ x, t) = Q_φ u (x, t)`
(`apply_rotZ`). Differentiating this identity in the angle at `φ = 0` gives the three
scalar identities of `angularGenerator_zero`, `angularGenerator_one` and
`angularGenerator_two`: with the generator `J x = (-x₂, x₁, 0)` of the rotations,
`J u(x, t) = Du(x, t) (J x)`.

On the meridional plane `{x₂ = 0}` away from the axis these become the `θ`-derivative
relations `∂₂u₁ = -u₂/r`, `∂₂u₂ = u₁/r`, `∂₂u₃ = 0` (design note R4: the cylindrical
coefficients of an axisymmetric field are read on that plane, where `u_r = u₁`,
`u_θ = u₂`, `u_z = u₃` and `∂_r = ∂₁`, `∂_z = ∂₃`). They are what turns the Cartesian
divergence, curl and Laplacian into their cylindrical forms
`eq:aniso:scalar:nse:div`, `eq:aniso:vorticity` and the right-hand sides of
`eq:aniso:scalar:nse`.

Differentiating the equivariance in the space variable instead gives
`fderiv_comp_rotZ`, the commutation `Du(Q_φ x) Q_φ = Q_φ Du(x)`. At `φ = π` it yields
the structure on the axis quoted in the standing assumptions of Section
`sec:aniso:equations`: `u_r`, `u_θ`, `∂_z u_r`, `∂_z u_θ` and `∂_r u_z` all vanish
there, and the components are odd, odd and even under the reflection
`(x₁, 0, x₃) ↦ (-x₁, 0, x₃)` of the meridional plane.
-/
@[expose] public section
open Set
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-! ### Spatial slices of a field on the cylinder -/
section Slice
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ParabolicPoint → E}

end Slice

/-! ### The generator of the rotations -/

/-! ### Equivariance of an axisymmetric field -/

/-! ### The three infinitesimal identities -/

/-! ### The `θ`-derivative relations on the meridional plane -/

/-! ### The derivative intertwines the rotations -/

/-! ### The axis and the reflection of the meridional plane -/

/-- On the axis the vertical derivative of the radial component vanishes: `∂_z u_r = 0`
(the paragraph after `eq:aniso:circulation:pde`). -/
axiom spatialPartial_two_zero_axis {u : ParabolicPoint → Vec3}
    (h : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ 1 (fun z : Vec3 × ℝ => u z) unitCylinder) {z : ParabolicPoint}
    (hz : z ∈ unitCylinder) (h0 : z.1 0 = 0) (h1 : z.1 1 = 0) :
    spatialPartial (fun w => u w 0) 2 z = 0

end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v355bf9870ed8.CIV.Analysis.SegmentQuotient ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-- If `g` is differentiable on the interval between `0` and `x` with
`|deriv g| ≤ M` there, then `|g x / x| ≤ M` whenever `x ≠ 0`. -/
axiom abs_div_le_of_deriv_bound {g : ℝ → ℝ} {x M : ℝ} (hg0 : g 0 = 0)
    (hd : ∀ s ∈ uIcc (0 : ℝ) x, DifferentiableAt ℝ g s)
    (hM : ∀ s ∈ uIcc (0 : ℝ) x, |deriv g s| ≤ M) (hx : x ≠ 0) :
    |g x / x| ≤ M

end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Examples.Example_99285748ae1eddfa9158_AxisQuotients ====
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

/-! ### Bound 1: the radial quotient on a segment through the axis -/

/-! ### Second partial derivatives along the meridional segment -/

private axiom meridional_shift_mem_vec3Ball {x₁ x₃ s : ℝ} (hx : x₁ ^ 2 + x₃ ^ 2 < 1)
    (hs : s ∈ Set.uIcc (0:ℝ) x₁) : meridional s x₃ ∈ vec3Ball (0 : Vec3) 1
private axiom hasDerivAt_second_partial_segment (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (ht : t ∈ Set.Ioo (-1 : ℝ) 0) (k i : Fin 3) (x₃ s : ℝ)
    (hmem : meridional s x₃ ∈ vec3Ball (0 : Vec3) 1) :
    HasDerivAt (fun a : ℝ => spatialPartial (fun w => u w k) i (meridional a x₃, t))
      (spatialSecondPartial (fun w => u w k) i 0 (meridional s x₃, t)) s
/-! ### Bound 2: `∂_z u_r / x₁` on a segment through the axis -/
/-- `|∂_z u_r / x₁| ≤ M` at `(x₁, x₃)` with `x₁ ≠ 0` whenever `|∂_r ∂_z u_r| ≤ M` along the
segment from the axis, since `∂_z u_r` vanishes on the axis (`spatialPartial_two_zero_axis`). -/
theorem abs_spatialPartial_two_zero_div_le_of_segment_bound (u : ParabolicPoint → Vec3) (t : ℝ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (ht : t ∈ Set.Ioo (-1 : ℝ) 0)
    (x₁ x₃ M : ℝ) (hx : x₁ ^ 2 + x₃ ^ 2 < 1) (hx1 : x₁ ≠ 0)
    (hM : ∀ a ∈ Set.uIcc (0:ℝ) x₁,
      |spatialSecondPartial (fun w => u w 0) 2 0 (meridional a x₃, t)| ≤ M) :
    |spatialPartial (fun w => u w 0) 2 (meridional x₁ x₃, t) / x₁| ≤ M := by
  have hu1 : ContDiffOn ℝ (1 : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder :=
    hu.of_le (by exact_mod_cast le_top)
  have hmem0 : ((meridional 0 x₃, t) : ParabolicPoint) ∈ unitCylinder :=
    ⟨meridional_shift_mem_vec3Ball hx Set.left_mem_uIcc, ht⟩
  have hg0 : spatialPartial (fun w => u w 0) 2 (meridional (0:ℝ) x₃, t) = 0 :=
    spatialPartial_two_zero_axis haxi hu1 hmem0 (meridional_apply_zero 0 x₃) (by simp [meridional])
  have hd : ∀ s ∈ Set.uIcc (0:ℝ) x₁,
      DifferentiableAt ℝ (fun a : ℝ => spatialPartial (fun w => u w 0) 2 (meridional a x₃, t)) s :=
    fun s hs => (hasDerivAt_second_partial_segment u t hu ht 0 2 x₃ s
      (meridional_shift_mem_vec3Ball hx hs)).differentiableAt
  have hMd : ∀ s ∈ Set.uIcc (0:ℝ) x₁,
      |deriv (fun a : ℝ => spatialPartial (fun w => u w 0) 2 (meridional a x₃, t)) s| ≤ M :=
    fun s hs => by
      rw [(hasDerivAt_second_partial_segment u t hu ht 0 2 x₃ s
        (meridional_shift_mem_vec3Ball hx hs)).deriv]
      exact hM s hs
  exact abs_div_le_of_deriv_bound hg0 hd hMd hx1
/-! ### Bound 3: `∂_r u_z / x₁` on a segment through the axis -/
end CIV
