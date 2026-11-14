module

public import Mathlib
public import Mathlib.Analysis.Normed.Module.WeakDual

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v306806dafb41.RequestProject.Euler.Basic ====
public section
/-!
# Two-dimensional Euler on the torus: definitions and principal statements

This file formalizes Section 1 of the paper (*Definitions and principal statements*):
the square torus `𝕋² = ℝ² / (2π ℤ)²`, weak Euler solutions (Definition `def:weak-euler`),
and the objects in which the main theorem (`Theorem main`) is stated.

## Modelling conventions

* A field on the torus is modelled by a field on `ℝ²` restricted to the fundamental square
  `torusBox = [0, 2π)²`.  Elements of `L²(𝕋²; ℝ²)` are elements of the Lebesgue space
  `Lp ℝ² 2` for the Lebesgue measure restricted to `torusBox` (total mass `4π²`).
* Periodicity enters through the test functions: all test functions are smooth and
  `2π`-periodic in each space variable, so that distributional derivatives are the
  distributional derivatives on the torus.
* The space–time `L²((0,T) × 𝕋²)` norm is written as the iterated integral
  `∫₀ᵀ ‖u(t)‖²_{L²(𝕋²)} dt`.
* `L^∞(0,T; L^p)` bounds on the vorticity are stated as a uniform bound valid at *every*
  time `t ∈ [0,T]` (which is what the paper proves).
-/
@[expose] public section
open MeasureTheory Real
open scoped ContDiff
namespace Euler2D
/-- The Euclidean plane `ℝ²`. -/
abbrev R2 := EuclideanSpace ℝ (Fin 2)

/-- The partial derivative `∂ᵢ f(x)`. -/
noncomputable def pd {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i : Fin 2) (f : R2 → F) (x : R2) : F :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

/-! The statement of the main theorem (`Theorem main`), its reduction to Proposition
`cp:limit`, and the refinement (`Corollary intro:refinement`) are in
`RequestProject/Euler/Theorems.lean`. -/
end Euler2D
end

end

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v306806dafb41.RequestProject.Euler.Stationary ====
public section
/-!
# Periodic integration by parts and smooth stationary Euler fields

The integration domain is the actual Euclidean fundamental square
`[0,2π)²` used by `μT`. Coordinate Fubini and the fundamental theorem of
calculus remove the periodic boundary terms.
-/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff
noncomputable section
namespace Euler2D
/-- A point of the Euclidean plane specified by its two real coordinates. -/
def torusVec (a b : ℝ) : R2 := WithLp.toLp 2 ![a, b]

end Euler2D
end

end
end

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v306806dafb41.RequestProject.Euler.CircularCell ====
public section
/-!
# The circular two-interface cell

Formalization of the following statements of the paper:

* Lemma `bv:two-interface-norms` (norms of a two-interface label),
* Definition `def:circular-cell` (the circular two-interface vorticity `W`),
* the circulation computation in Lemma `bv:circular-velocity` and Lemma `pc:circular-period`
  (angular velocities `Ω(r) = (2πr²)⁻¹ ∫_{B_r} W`, the interface values `1/2` and `0`, and the
  common period `P = 4π`),
* the scaling identity of Lemma `bv:circular-velocity` for the planar Biot–Savart law
  (Definition `def:kernel`).
-/
@[expose] public section
open MeasureTheory Real Metric
namespace Euler2D
/-! ### Norms of a two-interface label -/
section TwoInterface
variable {D₁ D₂ : Set R2}

/-- The two-interface label `ω = (5/2) 1_{D₁} - (3/2) 1_{D₂}`. -/
noncomputable def twoInterface (D₁ D₂ : Set R2) (x : R2) : ℝ :=
  D₁.indicator (fun _ => (5 / 2 : ℝ)) x - D₂.indicator (fun _ => (3 / 2 : ℝ)) x

end TwoInterface
/-! ### The circular cell `W` and its angular velocity -/

/-! ### The planar Biot–Savart law and the scaling identity -/
/-- `J x = x^⊥ = (-x₂, x₁)`. -/
noncomputable def perpJ (x : R2) : R2 := !₂[-x 1, x 0]

end Euler2D
end

end

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v306806dafb41.RequestProject.Euler.RadialStationary ====
public section
/-!
# Actual radial velocity blocks

`cellW` and `datumTerm` are scalar vorticities. Their circular velocity
profile is `cellOmega ‖x‖ • perpJ x`. This file works with that vector
field, translating its unit support disk into the interior of the
fundamental square before constructing a torus datum.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff
noncomputable section
namespace Euler2D
/-- The circular angular velocity as a continuous function of squared radius.
The minimum and maximum encode the two physical interfaces without a
singularity at the origin. -/
def cellOmegaSq (s : ℝ) : ℝ :=
  3 * (1 - min (max s (3 / 5)) 1) / (4 * max s (3 / 5))

/-- The center of the actual fundamental square. -/
def torusCenter : R2 := torusVec Real.pi Real.pi

/-- A radial rotating velocity, parameterized by squared radius. -/
def radialVelocity (f : ℝ → ℝ) (c : R2) (x : R2) : R2 :=
  f (‖x - c‖ ^ 2) • perpJ (x - c)

/-- A scalar primitive used to smooth a continuous radial profile. -/
def profilePrimitive (f : ℝ → ℝ) (s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, f t

/-- The forward average of a profile. Forward averaging preserves the
exact exterior cutoff `f s = 0` for `s ≥ 1`. -/
def profileAverage (f : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ε⁻¹ * (profilePrimitive f (s + ε) - profilePrimitive f s)

def radialApproxScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

end Euler2D
end

end
end

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Dependencies.v306806dafb41.RequestProject.Euler.ScaledRadialSobolev ====
public section
/-!
# Localized Sobolev estimates for scaled physical velocity blocks

The first derivative bound scales with the vorticity amplitude `A`,
while its support has radius `r`. Together these give the paper's
`A * r^(2/q)` Sobolev majorant.
-/
@[expose] public section
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff
noncomputable section
namespace Euler2D

/-- A genuine scaled smooth velocity block in the coordinate disk. -/
def scaledRadialAverage (A r ε : ℝ) (x : R2) : R2 :=
  (A * r) • radialVelocity (profileAverage cellOmegaSq ε) 0 (r⁻¹ • (x - torusCenter))

end Euler2D
end

end
end

-- ==== Examples.geogleswift_glitch___euler2d_finite_lp_nonuniqueness_palomar.Examples.Example_b0b42ac32e82502c7a10_ScaledCellCurl ====
/-!
# The exact curl of the physical circular datum series

The actual scaled blocks have their prescribed scaled two-interface
vorticities. The infinite velocity and vorticity series retain this
identity under their strong Lebesgue-space limits.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff
namespace Euler2D

def scaledApproxCellCurl (A r : ℝ) (n : ℕ) (x : R2) : ℝ :=
  pd 0 (scaledRadialAverage A r (radialApproxScale n)) x 1 -
    pd 1 (scaledRadialAverage A r (radialApproxScale n)) x 0


set_option linter.unusedVariables false in
lemma norm_scaledApproxCellCurl_le {r : ℝ} (hr : 0 < r) (A : ℝ) (n : ℕ) (x : R2) 
    (h_Euler2D_radialApproxScale_pos : ∀ (n : ℕ), 0 < Euler2D.radialApproxScale n)
    (h_Euler2D_norm_pd_scaledRadialAverage_le : ∀ {ε r : ℝ},
      0 < ε →
        0 < r →
          ∀ (A : ℝ) (x : Euler2D.R2) (i : Fin 2),
            ‖Euler2D.pd i (Euler2D.scaledRadialAverage A r ε) x‖ ≤ 7 * |A|)
    (h_Euler2D_abs_coord_le : ∀ (x : Euler2D.R2) (i : Fin 2), |x.ofLp i| ≤ ‖x‖)
    :
    ‖scaledApproxCellCurl A r n x‖ ≤ 14 * |A| := by
  have h0 := (h_Euler2D_abs_coord_le (pd 0 (scaledRadialAverage A r (radialApproxScale n)) x) 1).trans
    (h_Euler2D_norm_pd_scaledRadialAverage_le (h_Euler2D_radialApproxScale_pos n) hr A x 0)
  have h1 := (h_Euler2D_abs_coord_le (pd 1 (scaledRadialAverage A r (radialApproxScale n)) x) 0).trans
    (h_Euler2D_norm_pd_scaledRadialAverage_le (h_Euler2D_radialApproxScale_pos n) hr A x 1)
  exact (norm_sub_le _ _).trans (by
    simpa only [Real.norm_eq_abs] using (show
      |pd 0 (scaledRadialAverage A r (radialApproxScale n)) x 1| +
        |pd 1 (scaledRadialAverage A r (radialApproxScale n)) x 0| ≤ 14 * |A| by linarith))
end Euler2D
end
