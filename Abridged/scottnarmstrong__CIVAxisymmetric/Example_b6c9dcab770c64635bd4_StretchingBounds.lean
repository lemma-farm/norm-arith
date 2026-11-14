module

public import Mathlib
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Snowflaking
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Foundation.Parabolic.Basic ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Foundation.Sobolev.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Foundation.Sobolev.Ambient.Basis ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Statements.SpatialPartial ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.Meridional ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CKN.Statements.SpaceTimeSet ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.UnitCylinder ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.RotZ ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.RotField ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.AngularMean ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.IsAxisymmetricOn ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Identities.Vorticity ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# The vorticity and the circulation of an axisymmetric field

The Cartesian curl `curlComp u i` of a field is written with CKN's classical spatial
partial derivatives. For a smooth axisymmetric field, on the meridional plane `{x₂ = 0}`
away from the axis, its components are the cylindrical ones of `eq:aniso:vorticity`,
`ω_r = -∂_z u_θ`, `ω_θ = ∂_z u_r - ∂_r u_z`, `ω_z = ∂_r u_θ + u_θ/r`; the middle one is
the definition itself, the outer two use the `θ`-derivative relations of design note R4.
The circulation `Γ = r u_θ` of `eq:aniso:vorticity` is `x₁ u₂` on that plane.
-/
@[expose] public section
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-- The `i`-th Cartesian component of the curl, `(∇ × u)_i = ∂_{i+1} u_{i+2} - ∂_{i+2} u_{i+1}`
with the indices read cyclically. -/
def curlComp (u : ParabolicPoint → Vec3) (i : Fin 3) (z : ParabolicPoint) : ℝ :=
  spatialPartial (fun w => u w (i + 2)) (i + 1) z
    - spatialPartial (fun w => u w (i + 1)) (i + 2) z

end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.RadialQuotient ====
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

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Dependencies.v7b2e46bca3b2.CIV.Statements.MeridionalQuantity ====
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
/-- The integrand of `G_ρ` in `eq:aniso:G`: `|∂_r u_r| + |u_r/r| + |∂_z u_z| + |∂_z u_r|`
on the meridional plane. -/
def meridionalQuantity (u : ParabolicPoint → Vec3) (z : ParabolicPoint) : ℝ :=
  |CKN.spatialPartial (fun w => u w 0) 0 z| + |radialQuotient u z| +
    |CKN.spatialPartial (fun w => u w 2) 2 z| + |CKN.spatialPartial (fun w => u w 0) 2 z|
end CIV

end
end
end

-- ==== Examples.scottnarmstrong__CIVAxisymmetric.Examples.Example_b6c9dcab770c64635bd4_StretchingBounds ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated false
set_option warningAsError true
/-!
# The stretching-term bounds of `lem:aniso:closure`

This file proves two of the estimates that go into the tested vortex-stretching term of
`lem:aniso:closure`, from *Regularity of asymptotically axisymmetric solutions to the 3D
Navier–Stokes equations with analytic forcing*, arXiv:2609.20803: the unlabeled prose bound,
right after `eq:aniso:closure:stretch`, of the first three terms and the `∂_z u_r` term by
`C G Y`, and the labeled `eq:aniso:closure:angular:bound`.

## The plane-to-ball transfer

`CIV.Identities.PlaneTransfer` proves the cylindrical identities `stretching_meridional` and
`gradient_sq_meridional` on the meridional plane `{x₂ = 0}`, and transfers *rotation-invariant
scalars* (the Frobenius norm of `∇u`, the Euclidean norm of `curl u`, the vortex-stretching
scalar) to the whole ball via `exists_rotZ_meridional`: every `x` is `rotZ φ (meridional r x₃)`
for a unique `r ≥ 0`. The uniqueness is made explicit here: `r` is forced to be
`polarR x = √(x₀² + x₁²)` and `x₃` is forced to be `x 2` (`polarR_eq_of_rotZ_meridional`), so the
representative point of `x` is the *explicit*, globally continuous map
`x ↦ meridional (polarR x) (x 2)` — continuous everywhere (including on the axis, where it is
the identity), though not differentiable there.

This lets us read the cylindrical quantities of `eq:aniso:closure:stretch` at the representative
of a general point `x`, and bound them there: `stretchGTerm u x t` packages the first three terms
of the stretching sum and the `∂_z u_r` term, and `stretchAngularSwirl u x t` packages the
angular term's swirl factor `u_θ · (ω_r/r)`. Both are built from `radialQuotient`, which is
already known continuous across the axis (`continuousOn_radialQuotient_plane`), so both are
continuous on the whole open unit ball, and the pointwise bounds of `abs_stretchGTerm_le` and
`abs_two_mul_stretchAngularSwirl_mul_curlComp_one_le` integrate directly against `χ²` to the two
inequalities `stretchGTerm_integral_le` and `stretchAngularTerm_integral_abs_le`.

The remaining piece of `eq:aniso:closure:stretch`, the mixed term `(∂_r u_z) ω_r ω_z`, is
bounded by integration by parts in the `z`-direction (`eq:aniso:closure:mixed`,
`CIV.integral_cutoff_sq_stretchMixedTerm_eq`), which needs differentiability off the axis rather
than the continuity of the representative map used here.
`CIV.energy_inequality_of_mixed_term_bound` sums this file's two bounds with the mixed term into
`eq:aniso:closure:energy`.
-/
@[expose] public section
open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN
set_option autoImplicit false
noncomputable section
namespace CIV
/-! ### The explicit meridional representative -/
/-- The distance from `x` to the vertical axis, `√(x₀² + x₁²)`. This is the modulus used by
`exists_rotZ_meridional`, made explicit: continuous on all of `Vec3` (though not differentiable
on the axis). -/
def polarR (x : Vec3) : ℝ := Real.sqrt (x 0 ^ 2 + x 1 ^ 2)

/-! ### The two invariant scalars, read at the explicit representative -/

/-! ### Smoothness of the vorticity field -/

/-! ### The four-term part of `eq:aniso:closure:stretch` -/
/-- The first three terms and the `∂_z u_r` term of `eq:aniso:closure:stretch`, read at the
meridional representative of `x`: `(∂_r u_r) ω_r² + (u_r/r) ω_θ² + (∂_z u_z) ω_z² + (∂_z u_r)
ω_r ω_z`, all evaluated at `meridional (polarR x) (x 2)`. On the meridional plane itself
(`x 1 = 0`, `x 0 ≥ 0`) the representative is `x`, and this is literally the manuscript's
expression. -/
def stretchGTerm (u : ParabolicPoint → Vec3) (x : Vec3) (t : ℝ) : ℝ :=
  spatialPartial (fun w => u w 0) 0 (meridional (polarR x) (x 2), t)
      * (curlComp u 0 (meridional (polarR x) (x 2), t)) ^ 2
    + radialQuotient u (meridional (polarR x) (x 2), t)
        * (curlComp u 1 (meridional (polarR x) (x 2), t)) ^ 2
    + spatialPartial (fun w => u w 2) 2 (meridional (polarR x) (x 2), t)
        * (curlComp u 2 (meridional (polarR x) (x 2), t)) ^ 2
    + spatialPartial (fun w => u w 0) 2 (meridional (polarR x) (x 2), t)
        * curlComp u 0 (meridional (polarR x) (x 2), t)
        * curlComp u 2 (meridional (polarR x) (x 2), t)
set_option linter.unusedVariables false in
/-- **The pointwise bound behind `eq:aniso:closure:stretch`'s four-term estimate.**
`stretchGTerm` is bounded, at every point of the ball `B(ρ)` (for `ρ ≤ 1`),
by `2 G` times the local enstrophy density, whenever the four cylindrical quantities of
`meridionalQuantity` are bounded by `G` at every meridional-plane point of `B(ρ)`. Each of
the four coefficients of `stretchGTerm` is one of those four quantities (`meridionalQuantity`'s
definition), and the two mixed products are split by `2|ab| ≤ a² + b²`. -/
theorem abs_stretchGTerm_le {u : ParabolicPoint → Vec3} (haxi : IsAxisymmetricOn u unitCylinder)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    {t G ρ : ℝ} (hρ1 : vec3Ball (0 : Vec3) ρ ⊆ vec3Ball (0 : Vec3) 1)
    (hG : ∀ x₁ x₃ : ℝ, meridional x₁ x₃ ∈ vec3Ball (0 : Vec3) ρ →
        meridionalQuantity u (meridional x₁ x₃, t) ≤ G)
    (hGnn : 0 ≤ G) {x : Vec3} (hxρ : x ∈ vec3Ball (0 : Vec3) ρ) (ht : t ∈ Ioo (-1 : ℝ) 0) 
    (h_CIV_curlSq_eq_polarR : ∀ {v : CKN.Foundation.Parabolic.ParabolicPoint → CKN.Foundation.Parabolic.Vec3},
      CIV.IsAxisymmetricOn v CIV.unitCylinder →
        ContDiffOn ℝ 1 (fun (z : CKN.Foundation.Parabolic.Vec3 × ℝ) ↦ v z) CIV.unitCylinder →
          ∀ {x : CKN.Foundation.Parabolic.Vec3} {t : ℝ},
            (x, t) ∈ CIV.unitCylinder →
              ∑ i : Fin 3, CIV.curlComp v i (x, t) ^ 2 =
                ∑ i : Fin 3, CIV.curlComp v i (CIV.meridional (CIV.polarR x) (x 2), t) ^ 2)
    (h_CIV_rep_mem_vec3Ball : ∀ {x : CKN.Foundation.Parabolic.Vec3} {ρ : ℝ},
      x ∈ CKN.Foundation.Parabolic.vec3Ball 0 ρ →
        CIV.meridional (CIV.polarR x) (x 2) ∈ CKN.Foundation.Parabolic.vec3Ball 0 ρ)
    :
    |stretchGTerm u x t| ≤ 2 * G * ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 := by
  have hz : (x, t) ∈ unitCylinder := ⟨hρ1 hxρ, ht⟩
  set rep : Vec3 := meridional (polarR x) (x 2) with hrep
  have hrepmem : rep ∈ vec3Ball (0 : Vec3) ρ := h_CIV_rep_mem_vec3Ball hxρ
  have hGrep : meridionalQuantity u (rep, t) ≤ G := by
    have hkey := hG (polarR x) (x 2) hrepmem
    rw [hrep]; exact hkey
  have hmq : meridionalQuantity u (rep, t)
      = |spatialPartial (fun w => u w 0) 0 (rep, t)| + |radialQuotient u (rep, t)|
        + |spatialPartial (fun w => u w 2) 2 (rep, t)|
        + |spatialPartial (fun w => u w 0) 2 (rep, t)| := rfl
  have h1 : |spatialPartial (fun w => u w 0) 0 (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have := abs_nonneg (radialQuotient u (rep, t))
    have := abs_nonneg (spatialPartial (fun w => u w 2) 2 (rep, t))
    have := abs_nonneg (spatialPartial (fun w => u w 0) 2 (rep, t))
    linarith only [hGrep, this, ‹0 ≤ |radialQuotient u (rep, t)|›,
      ‹0 ≤ |spatialPartial (fun w => u w 2) 2 (rep, t)|›]
  have h2 : |radialQuotient u (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have hb1 := abs_nonneg (spatialPartial (fun w => u w 0) 0 (rep, t))
    have hb3 := abs_nonneg (spatialPartial (fun w => u w 2) 2 (rep, t))
    have hb4 := abs_nonneg (spatialPartial (fun w => u w 0) 2 (rep, t))
    linarith only [hGrep, hb1, hb3, hb4]
  have h3 : |spatialPartial (fun w => u w 2) 2 (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have hb1 := abs_nonneg (spatialPartial (fun w => u w 0) 0 (rep, t))
    have hb2 := abs_nonneg (radialQuotient u (rep, t))
    have hb4 := abs_nonneg (spatialPartial (fun w => u w 0) 2 (rep, t))
    linarith only [hGrep, hb1, hb2, hb4]
  have h4 : |spatialPartial (fun w => u w 0) 2 (rep, t)| ≤ G := by
    rw [hmq] at hGrep
    have hb1 := abs_nonneg (spatialPartial (fun w => u w 0) 0 (rep, t))
    have hb2 := abs_nonneg (radialQuotient u (rep, t))
    have hb3 := abs_nonneg (spatialPartial (fun w => u w 2) 2 (rep, t))
    linarith only [hGrep, hb1, hb2, hb3]
  set a0 := curlComp u 0 (rep, t)
  set a1 := curlComp u 1 (rep, t)
  set a2 := curlComp u 2 (rep, t)
  set c1 := spatialPartial (fun w => u w 0) 0 (rep, t)
  set c2 := radialQuotient u (rep, t)
  set c3 := spatialPartial (fun w => u w 2) 2 (rep, t)
  set c4 := spatialPartial (fun w => u w 0) 2 (rep, t)
  have hbound : |c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2 + c4 * a0 * a2|
      ≤ 2 * G * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) := by
    have hprod : |c4 * a0 * a2| ≤ G * (a0 ^ 2 + a2 ^ 2) := by
      have hsplit : |c4 * a0 * a2| ≤ |c4| * (a0 ^ 2 + a2 ^ 2) / 2 := by
        have hsq : (0 : ℝ) ≤ (|a0| - |a2|) ^ 2 := sq_nonneg _
        have hae : |a0 * a2| ≤ (a0 ^ 2 + a2 ^ 2) / 2 := by
          have habs : |a0 * a2| = |a0| * |a2| := abs_mul a0 a2
          have hsq0 : |a0| ^ 2 = a0 ^ 2 := sq_abs a0
          have hsq2 : |a2| ^ 2 = a2 ^ 2 := sq_abs a2
          nlinarith only [hsq, habs, hsq0, hsq2]
        calc |c4 * a0 * a2| = |c4| * |a0 * a2| := by rw [mul_assoc, abs_mul]
          _ ≤ |c4| * ((a0 ^ 2 + a2 ^ 2) / 2) :=
            mul_le_mul_of_nonneg_left hae (abs_nonneg c4)
          _ = |c4| * (a0 ^ 2 + a2 ^ 2) / 2 := by ring
      have hGa : |c4| * (a0 ^ 2 + a2 ^ 2) / 2 ≤ G * (a0 ^ 2 + a2 ^ 2) := by
        have hnn : (0 : ℝ) ≤ a0 ^ 2 + a2 ^ 2 := by positivity
        have hprodle := mul_le_mul_of_nonneg_right h4 hnn
        have hGnn2 : (0 : ℝ) ≤ G * (a0 ^ 2 + a2 ^ 2) := mul_nonneg hGnn hnn
        linarith only [hprodle, hGnn2]
      linarith only [hsplit, hGa]
    have hsum1 : |c1 * a0 ^ 2| ≤ G * a0 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a0)]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg a0)
    have hsum2 : |c2 * a1 ^ 2| ≤ G * a1 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a1)]
      exact mul_le_mul_of_nonneg_right h2 (sq_nonneg a1)
    have hsum3 : |c3 * a2 ^ 2| ≤ G * a2 ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg a2)]
      exact mul_le_mul_of_nonneg_right h3 (sq_nonneg a2)
    have htri : |c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2 + c4 * a0 * a2|
        ≤ |c1 * a0 ^ 2| + |c2 * a1 ^ 2| + |c3 * a2 ^ 2| + |c4 * a0 * a2| := by
      have e1 := abs_add_le (c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2) (c4 * a0 * a2)
      have e2 := abs_add_le (c1 * a0 ^ 2 + c2 * a1 ^ 2) (c3 * a2 ^ 2)
      have e3 := abs_add_le (c1 * a0 ^ 2) (c2 * a1 ^ 2)
      linarith only [e1, e2, e3]
    have hGa1 : (0 : ℝ) ≤ G * a1 ^ 2 := mul_nonneg hGnn (sq_nonneg a1)
    linarith only [htri, hsum1, hsum2, hsum3, hprod, hGa1]
  have hval : stretchGTerm u x t = c1 * a0 ^ 2 + c2 * a1 ^ 2 + c3 * a2 ^ 2 + c4 * a0 * a2 := rfl
  have hcurl : ∑ i : Fin 3, (curlComp u i (x, t)) ^ 2 = a0 ^ 2 + a1 ^ 2 + a2 ^ 2 := by
    rw [h_CIV_curlSq_eq_polarR haxi (hu.of_le (by exact_mod_cast le_top)) hz]
    simp only [Fin.sum_univ_three]
    rfl
  rw [hval, hcurl]
  exact hbound
/-! ### Continuity, and the integral form of the four-term estimate -/
end CIV
