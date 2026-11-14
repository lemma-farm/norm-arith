import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Snowflaking
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Parabolic.Basic ====
section
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
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
abbrev Vec3 := Fin 3 → ℝ

def vec3EuclideanNorm (v : Vec3) : ℝ := Real.sqrt (∑ i, v i ^ 2)

end CKN.Foundation.Parabolic

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Euclidean.DegreeOneSymbol ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Symbols homogeneous of degree one

External Input `ext:heat-kernel` of `paper/ckn.tex` quantifies over every Fourier
multiplier `ς(D)` whose symbol `ς` is smooth on `ℝ³ ∖ {0}` and homogeneous of
degree one, and the manuscript's pressure-multiplier discussion uses the concrete symbols
`ς_{jl}(ξ) = i ξ ξ_j ξ_l / |ξ|²` of that class.  This file records the
homogeneity predicate for such a symbol and proves the linear growth bound
`‖ς ξ‖ ≤ C |ξ|` that makes the associated Fourier integrals absolutely
convergent.  Symbols are complex valued, as `ς_{jl}` is.
-/
open scoped BigOperators
open Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
/-- A complex symbol on `Vec3` is homogeneous of degree one when
`ς (a • ξ) = a • ς ξ` for every positive real dilation `a`.  This is the
homogeneity hypothesis of External Input `ext:heat-kernel`. -/
def IsDegreeOneHomogeneous (σ : Vec3 → ℂ) : Prop :=
  ∀ a : ℝ, 0 < a → ∀ ξ : Vec3, σ (a • ξ) = (a : ℂ) * σ ξ
end CKN.Foundation.Euclidean

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Euclidean.SpatialMultiplierKernel ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# The spatial Fourier multiplier applied to the heat kernel

External Input `ext:heat-kernel` of `paper/ckn.tex` records the size, gradient
and time-derivative bounds of `ς(D)W₊`, where `W₊(t,x) = 1_{t>0}(4πt)^{-3/2}
e^{-|x|²/(4t)}` and `ς(D)` is the spatial Fourier multiplier of a symbol `ς`
smooth away from the origin and homogeneous of degree one; the display
`eq:heat-kernel-bounds` in the proof of Proposition `prop:heat-morrey-hoelder`
is the same list.

At each positive time the spatial Fourier transform of `W₊(·,t)` is
`e^{-t|ξ|²}` in the paper's normalization `ĝ(ξ) = ∫ g(y) e^{-i y·ξ} dy`, so
`ς(D)W₊(·,t)` is the inverse transform `(2π)^{-3} ∫ e^{i x·ξ} ς(ξ) e^{-t|ξ|²} dξ`.
This file records that kernel, its causal vanishing for nonpositive times, and
the fact that the defining frequency integral converges absolutely for every
symbol of the class.  The three pointwise estimates themselves are the content
of the external input and are not proved here.
-/
open scoped BigOperators
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic 
/-- The integrand of the frequency integral for `ς(D)W₊` at the space-time
point `(x,t)`: the phase `e^{i x·ξ}`, the symbol `ς(ξ)`, and the Gaussian
`e^{-t|ξ|²}` that is the spatial Fourier transform of `W₊(·,t)`. -/
def spatialMultiplierHeatIntegrand (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) (ξ : Vec3) : ℂ :=
  Complex.exp (Complex.I * ((∑ j : Fin 3, x j * ξ j : ℝ) : ℂ)) * σ ξ *
    Complex.exp (-((t * vec3EuclideanNorm ξ ^ 2 : ℝ) : ℂ))
/-- The kernel `ς(D)W₊` of External Input `ext:heat-kernel`, written as the
inverse spatial Fourier integral at positive times and extended by zero to
nonpositive times, as `W₊` itself is.  The value on the time-zero hyperplane is
the causal one; a spatial multiplier is nonlocal, so no pointwise derivative
claim is made across that hyperplane. -/
def spatialMultiplierHeatKernel (σ : Vec3 → ℂ) (x : Vec3) (t : ℝ) : ℂ :=
  if 0 < t then
    (2 * Real.pi : ℂ) ^ (-3 : ℤ) * ∫ ξ : Vec3, spatialMultiplierHeatIntegrand σ x t ξ
  else 0
end CKN.Foundation.Euclidean

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelGaussianDerivativeBounds ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Derivative bounds for the frequency Gaussian
-/
open scoped BigOperators
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic 
/-- The complex extension of the squared Euclidean norm on frequency space. -/
def complexEuclideanSquare (ξ : Vec3) : ℂ :=
  (vec3EuclideanNorm ξ ^ 2 : ℝ)

end CKN.Foundation.Euclidean

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelScaling ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Parabolic scaling for multiplier heat kernels
-/
open scoped BigOperators
open MeasureTheory
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic 

/-- A homogeneous degree-`d` symbol has the scale-invariant kernel bound of order `d+3`. -/
axiom exists_spatialMultiplierHeatKernel_bound_of_homogeneous
    {τ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d) (hd3 : d ≤ 3)
    (hτ : ContDiffOn ℝ (⊤ : ℕ∞) τ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      τ (a • ξ) = (a ^ d : ℝ) • τ ξ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      ‖spatialMultiplierHeatKernel τ x t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-(d + 3 : ℝ))
end CKN.Foundation.Euclidean

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Sobolev.Ambient.Basic ====
section
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
namespace CKN
/-- The native coordinate model of a finite-dimensional real vector space. -/
abbrev Vec (d : ℕ) := Fin d → ℝ
end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Sobolev.Ambient.Basis ====
section
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
namespace CKN
/-- The `i`th coordinate basis vector in the native ambient space. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

end CKN

end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelSpatialDerivative ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Spatial differentiability of multiplier heat kernels
-/
open scoped BigOperators FourierTransform
open MeasureTheory
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic  VectorFourier

/-- Multiplication of a symbol by one spatial frequency. -/
def spatialMultiplierCoordinateSymbol (σ : Vec3 → ℂ) (j : Fin 3) (ξ : Vec3) : ℂ :=
  (Complex.I * (ξ j : ℂ)) * σ ξ
/-- A smooth degree-`d` symbol remains smooth after one coordinate-frequency factor. -/
axiom spatialMultiplierCoordinateSymbol_contDiffOn
    {σ : Vec3 → ℂ} (j : Fin 3)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialMultiplierCoordinateSymbol σ j) ({0}ᶜ : Set Vec3)
/-- Homogeneity degree increases by one after a spatial frequency factor. -/
axiom spatialMultiplierCoordinateSymbol_homogeneous
    {σ : Vec3 → ℂ} (d : ℕ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    (j : Fin 3) :
    ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      spatialMultiplierCoordinateSymbol σ j (a • ξ) =
        (a ^ (d + 1) : ℝ) • spatialMultiplierCoordinateSymbol σ j ξ

/-- The multiplier heat kernel is differentiable in space at every positive time. -/
axiom spatialMultiplierHeatKernel_hasFDerivAt_spatial
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasFDerivAt (fun y => spatialMultiplierHeatKernel σ y t)
      (fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) x
/-- The spatial derivative of the kernel is the kernel of the coordinate-multiplied symbol. -/
axiom spatialMultiplierHeatKernel_fderiv_apply_basis
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) (x : Vec3) (j : Fin 3) :
    (fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j) =
      spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t
end CKN.Foundation.Euclidean

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5ec1df69b442.CKN.Foundation.Euclidean.SpatialMultiplierHeatKernelTimeDerivative ====
section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Time differentiability of multiplier heat kernels
-/
open scoped BigOperators
open MeasureTheory
open Filter
open TopologicalSpace
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic 
/-- Multiplication of a symbol by the negative squared frequency. -/
def spatialMultiplierTimeSymbol (σ : Vec3 → ℂ) (ξ : Vec3) : ℂ :=
  -complexEuclideanSquare ξ * σ ξ
/-- The time-differentiated symbol stays smooth away from the origin. -/
axiom spatialMultiplierTimeSymbol_contDiffOn
    {σ : Vec3 → ℂ} (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (spatialMultiplierTimeSymbol σ) ({0}ᶜ : Set Vec3)
/-- Multiplication by the negative squared frequency raises homogeneity by two. -/
axiom spatialMultiplierTimeSymbol_homogeneous
    {σ : Vec3 → ℂ} (d : ℕ)
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ) :
    ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      spatialMultiplierTimeSymbol σ (a • ξ) =
        (a ^ (d + 2) : ℝ) • spatialMultiplierTimeSymbol σ ξ

/-- The time derivative is the kernel of the symbol multiplied by `-|ξ|²`. -/
axiom spatialMultiplierHeatKernel_hasDerivAt_time
    {σ : Vec3 → ℂ} (d : ℕ) (hd : 0 < d)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ d : ℝ) • σ ξ)
    {t : ℝ} (ht : 0 < t) (x : Vec3) :
    HasDerivAt (fun s => spatialMultiplierHeatKernel σ x s)
      (spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t) t
end CKN.Foundation.Euclidean

end
end

-- ==== Examples.scottnarmstrong__CaffarelliKohnNirenberg.Examples.Example_5bcc6664496904de963d_SpatialMultiplierHeatKernelBoundsAssembly ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option warningAsError true
/-!
# Bounds for degree-one multiplier heat kernels

The frequency representation gives the size, spatial-gradient, and time-derivative
bounds for every smooth degree-one symbol, with one symbol-dependent constant.
-/
open scoped BigOperators
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic 
/-- A smooth degree-one multiplier heat kernel and its first derivatives have
the parabolic bounds of orders four, five, and six, with one constant fixed
before the space-time point. -/
theorem exists_spatialMultiplierHeatKernel_bounds_of_degreeOne
    (σ : Vec3 → ℂ)
    (hσ : ContDiffOn ℝ (⊤ : ℕ∞) σ ({0}ᶜ : Set Vec3))
    (hhom : IsDegreeOneHomogeneous σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      DifferentiableAt ℝ (fun y => spatialMultiplierHeatKernel σ y t) x ∧
      DifferentiableAt ℝ (fun s => spatialMultiplierHeatKernel σ x s) t ∧
      ‖spatialMultiplierHeatKernel σ x t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-4 : ℝ) ∧
      Real.sqrt (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ^ 2) ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-5 : ℝ) ∧
      ‖deriv (fun s => spatialMultiplierHeatKernel σ x s) t‖ ≤
        C * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-6 : ℝ) := by
  have hhom1 : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      σ (a • ξ) = (a ^ 1 : ℝ) • σ ξ := by
    intro a ha ξ
    simpa [pow_one, RCLike.real_smul_eq_coe_mul] using hhom a ha ξ
  obtain ⟨C₀, hC₀, hB₀⟩ := exists_spatialMultiplierHeatKernel_bound_of_homogeneous
    (τ := σ) 1 (by norm_num) (by norm_num) hσ hhom1
  have htimeCont : ContDiffOn ℝ (⊤ : ℕ∞)
      (spatialMultiplierTimeSymbol σ) ({0}ᶜ : Set Vec3) :=
    spatialMultiplierTimeSymbol_contDiffOn hσ
  have htimeHom : ∀ a : ℝ, 0 < a → ∀ ξ : Vec3,
      spatialMultiplierTimeSymbol σ (a • ξ) =
        (a ^ 3 : ℝ) • spatialMultiplierTimeSymbol σ ξ := by
    intro a ha ξ
    simpa using
      (spatialMultiplierTimeSymbol_homogeneous (σ := σ) 1 hhom1 a ha ξ)
  obtain ⟨Cₜ, hCₜ, hBₜ⟩ := exists_spatialMultiplierHeatKernel_bound_of_homogeneous
    (τ := spatialMultiplierTimeSymbol σ) 3 (by norm_num) (by norm_num)
      htimeCont htimeHom
  let Ecoord : Fin 3 → Prop := fun j =>
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      ‖spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t‖ ≤
        c * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-5 : ℝ)
  have hEcoord : ∀ j : Fin 3, Ecoord j := by
    intro j
    obtain ⟨c, hc, hbound⟩ := exists_spatialMultiplierHeatKernel_bound_of_homogeneous
      (τ := spatialMultiplierCoordinateSymbol σ j) 2 (by norm_num) (by norm_num)
      (spatialMultiplierCoordinateSymbol_contDiffOn j hσ)
      (spatialMultiplierCoordinateSymbol_homogeneous 1 hhom1 j)
    refine ⟨c, hc, ?_⟩
    intro x t ht
    convert hbound x t ht using 1
    congr 1
    norm_num
  let Cj : Fin 3 → ℝ := fun j => Classical.choose (hEcoord j)
  have hCj : ∀ j : Fin 3, 0 ≤ Cj j := by
    intro j
    exact (Classical.choose_spec (hEcoord j)).1
  have hBcoord : ∀ j : Fin 3, ∀ x : Vec3, ∀ t : ℝ, 0 < t →
      ‖spatialMultiplierHeatKernel (spatialMultiplierCoordinateSymbol σ j) x t‖ ≤
        Cj j * (max (vec3EuclideanNorm x) (Real.sqrt t)) ^ (-5 : ℝ) := by
    intro j x t ht
    exact (Classical.choose_spec (hEcoord j)).2 x t ht
  let Ccoord : ℝ := ∑ j : Fin 3, Cj j
  let Cgrad : ℝ := Real.sqrt 3 * Ccoord
  let C : ℝ := max C₀ (max Cₜ Cgrad)
  have hCcoord : 0 ≤ Ccoord := by
    dsimp [Ccoord]
    exact Finset.sum_nonneg fun j _ => hCj j
  have hCgrad : 0 ≤ Cgrad := by dsimp [Cgrad]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x t ht
  let R : ℝ := max (vec3EuclideanNorm x) (Real.sqrt t)
  have hR : 0 < R := by
    dsimp [R]
    exact (Real.sqrt_pos.2 ht).trans_le (le_max_right _ _)
  have hp4 : 0 ≤ R ^ (-4 : ℝ) := Real.rpow_nonneg hR.le _
  have hp5 : 0 ≤ R ^ (-5 : ℝ) := Real.rpow_nonneg hR.le _
  have hp6 : 0 ≤ R ^ (-6 : ℝ) := Real.rpow_nonneg hR.le _
  have hkernel0 : ‖spatialMultiplierHeatKernel σ x t‖ ≤ C₀ * R ^ (-4 : ℝ) := by
    dsimp [R]
    convert hB₀ x t ht using 1
    norm_num
  have hkernelTime :
      ‖spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t‖ ≤
        Cₜ * R ^ (-6 : ℝ) := by
    dsimp [R]
    convert hBₜ x t ht using 1
    norm_num
  have hcoord : ∀ j : Fin 3,
      ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ≤
        Cj j * R ^ (-5 : ℝ) := by
    intro j
    rw [spatialMultiplierHeatKernel_fderiv_apply_basis
      1 (by norm_num) hσ hhom1 ht x j]
    simpa [R] using hBcoord j x t ht
  let B : ℝ := Ccoord * R ^ (-5 : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcoordB : ∀ j : Fin 3,
      ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ≤ B := by
    intro j
    have hsum : Cj j ≤ Ccoord := by
      dsimp [Ccoord]
      exact Finset.single_le_sum (fun i _ => hCj i) (Finset.mem_univ j)
    dsimp [B]
    exact (hcoord j).trans (mul_le_mul_of_nonneg_right hsum hp5)
  have hsumSq :
      (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ^ 2) ≤
        3 * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin 3, B ^ 2 := Finset.sum_le_sum fun j _ => by
        have hnonneg := norm_nonneg
          ((fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j))
        nlinarith only [hnonneg, hB, hcoordB j]
      _ = 3 * B ^ 2 := by simp
  have hgrad :
      Real.sqrt (∑ j : Fin 3,
        ‖(fderiv ℝ (fun y => spatialMultiplierHeatKernel σ y t) x) (basisVec j)‖ ^ 2) ≤
        Cgrad * R ^ (-5 : ℝ) := by
    calc
      _ ≤ Real.sqrt (3 * B ^ 2) := Real.sqrt_le_sqrt hsumSq
      _ = Cgrad * R ^ (-5 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
        dsimp [Cgrad, B]
        ring
  have htimeDeriv := spatialMultiplierHeatKernel_hasDerivAt_time
    1 (by norm_num) hσ hhom1 ht x
  have htimeDerivEq : deriv (fun s => spatialMultiplierHeatKernel σ x s) t =
      spatialMultiplierHeatKernel (spatialMultiplierTimeSymbol σ) x t :=
    htimeDeriv.deriv
  have htime : ‖deriv (fun s => spatialMultiplierHeatKernel σ x s) t‖ ≤
      C * R ^ (-6 : ℝ) := by
    rw [htimeDerivEq]
    exact hkernelTime.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left Cₜ Cgrad) (le_max_right C₀ (max Cₜ Cgrad))) hp6)
  have hspaceDiff := spatialMultiplierHeatKernel_hasFDerivAt_spatial
    1 (by norm_num) hσ hhom1 ht x
  refine ⟨hspaceDiff.differentiableAt, htimeDeriv.differentiableAt, ?_, ?_, ?_⟩
  · exact hkernel0.trans (mul_le_mul_of_nonneg_right
      (le_max_left C₀ (max Cₜ Cgrad)) hp4)
  · exact hgrad.trans (mul_le_mul_of_nonneg_right
      (le_trans (le_max_right Cₜ Cgrad) (le_max_right C₀ (max Cₜ Cgrad))) hp5)
  · simpa [R] using htime
end CKN.Foundation.Euclidean
