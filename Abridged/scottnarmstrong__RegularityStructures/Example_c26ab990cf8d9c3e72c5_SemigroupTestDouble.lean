module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Group.AddCircle
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vcf8a52064a9c.RegularityStructures.Torus.Basic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The three-torus and space-time

We write `T³ = ℝ³/ℤ³` as `UnitAddTorus (Fin 3)` and space-time `ℝ × T³` as a product. Points of
`ℝ³` are functions `Fin 3 → ℝ`, with the Euclidean square norm written out by hand. A function on
the torus is smooth if its periodic lift to `ℝ³` is smooth.

Source: the statement, Section 2.
-/
@[expose] public noncomputable section
open scoped ContDiff
namespace RegularityStructures
/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)
/-- Space-time `ℝ × T³`. -/
abbrev SpaceTime : Type := ℝ × Torus3

/-- The representative of a point of `T³` in `[0, 1)³`. -/
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)
/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vcf8a52064a9c.RegularityStructures.Torus.KernelBoundsBasic ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Parabolic size on space-time over `T³`

The singular estimates for the massive heat kernel use the parabolic size
`|z|_s = |t|^(1/2) + |x|`, with the spatial point represented in the centred fundamental cube
`[-1/2,1/2)^3`.  The representative is defined here rather than changing the existing `[0,1)`
representative used by `heatKernel`.

Sources: [Hai14] = arXiv:1303.5113v4, §2 and Assumption 5.1; [Hos25] = arXiv:2310.07396v2, §2.1.
-/
@[expose] public noncomputable section
open Real Set
namespace RegularityStructures
/-- The centred representative of a point of `T³`, in `[-1/2,1/2)³`. -/
def torusCenteredRep (x : Torus3) : Fin 3 → ℝ := fun i =>
  if (1 / 2 : ℝ) ≤ torusRep x i then torusRep x i - 1 else torusRep x i
/-- The Euclidean spatial norm of the centred representative. -/
def torusSpatialNorm (x : Torus3) : ℝ := √(sqNorm3 (torusCenteredRep x))
/-- The parabolic size of a space-time point. -/
def torusParabolicSize (z : SpaceTime) : ℝ :=
  √|z.1| + torusSpatialNorm z.2

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vcf8a52064a9c.Phi43.BPHZ.SemigroupTestProfile ====
public section
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Profiles of semigroup test functions on space-time

A *semigroup test profile* at scale `lam` and base point `x` is a measurable function
`g : ℝ × T³ → ℝ` that is bounded by `B lam⁻⁵` and whose absolute moments
`∫ |g| s(· - x)^r` are integrable and at most `Mom r lam^r` for every `r ≥ 0`.  Here
`s = torusParabolicSize`.  This is the abstract shape of the periodised semigroup kernel
`q^♯_t(x, ·)`, `lam = t^(1/4)`, which has a rapidly decaying (non-compactly supported) tail.

The two pieces of information (sup bound and moments) suffice for all the weighted integral bounds
of the chaos reduction:

* `SemigroupTestProfile.integral_rpow_le`: `∫ |g| s(· - x)^a ≤ C lam^a` for every `a > -5`;
* `SemigroupTestProfile.integral_mul_rpow_sub_le`: `∫ |g v| s(u - v)^(-q) dv ≤ C lam^(-q)` for
  `0 < q < 5`, uniformly in `u`.

For negative exponents the singularity is integrated against the sup bound on the ball
`s ≤ lam`, and the exterior is controlled by `lam^(-p)` times the `L¹` norm.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures
/-- A semigroup test profile at scale `lam > 0` and base point `x`: measurable, bounded by
`B lam⁻⁵`, with integrable absolute moments `∫ |g| s(· - x)^r ≤ Mom r lam^r`, `r ≥ 0`. -/
structure SemigroupTestProfile (x : SpaceTime) (lam B : ℝ) (Mom : ℝ → ℝ)
    (g : SpaceTime → ℝ) : Prop where
  measurable : Measurable g
  abs_le : ∀ u, |g u| ≤ B * (lam ^ 5)⁻¹
  integrable_moment : ∀ r : ℝ, 0 ≤ r →
    Integrable (fun u => |g u| * torusParabolicSize (u - x) ^ r)
  integral_moment_le : ∀ r : ℝ, 0 ≤ r →
    ∫ u, |g u| * torusParabolicSize (u - x) ^ r ≤ Mom r * lam ^ r
/-- The constant of `SemigroupTestProfile.integral_rpow_le`. -/
def semigroupTestMomConst (B : ℝ) (Mom : ℝ → ℝ) (a : ℝ) : ℝ :=
  if 0 ≤ a then Mom a else B * (80 / (5 + a)) + Mom 0
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}
namespace SemigroupTestProfile
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.measurable_abs : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g →
    Measurable fun (u : RegularityStructures.SpaceTime) ↦ |g u|
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.integrable_abs : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g →
    MeasureTheory.Integrable (fun (u : RegularityStructures.SpaceTime) ↦ |g u|)
      MeasureTheory.MeasureSpace.volume
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.integral_abs_le : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g →
    ∫ (u : RegularityStructures.SpaceTime), |g u| ≤ Mom 0

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.mom_zero_nonneg : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g → 0 ≤ Mom 0
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.mom_nonneg : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g → 0 < lam → ∀ {r : ℝ}, 0 ≤ r → 0 ≤ Mom r

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.integral_rpow_le : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g →
    ∀ {a : ℝ},
      -5 < a →
        0 < lam →
          MeasureTheory.Integrable
              (fun (u : RegularityStructures.SpaceTime) ↦
                |g u| * RegularityStructures.torusParabolicSize (u - x) ^ a)
              MeasureTheory.MeasureSpace.volume ∧
            ∫ (u : RegularityStructures.SpaceTime),
                |g u| * RegularityStructures.torusParabolicSize (u - x) ^ a ≤
              RegularityStructures.semigroupTestMomConst B Mom a * lam ^ a
end SemigroupTestProfile
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_c26ab990cf8d9c3e72c5_SemigroupTestDouble ====
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The chaos-reduction double integral for a semigroup test profile

For a semigroup test profile `g` at scale `lam` and base point `x` (see `SemigroupTestProfile`) and
real exponents `ζ, e > -5`,
`∫∫ |g u| |g v| s(u - x)^ζ s(u - v)^e ≤ C lam^(ζ+e)`
(`SemigroupTestProfile.integral_double_le`).  This is the analogue of
`chaosReduction_integral_left` with the compactly supported test function replaced by a profile
with unbounded support, for which only a sup bound and moment bounds are available.

* For `e < 0` the inner integral over `v` is bounded uniformly in `u` by
  `SemigroupTestProfile.integral_mul_rpow_sub_le`.
* For `e ≥ 0` we use `s(u - v)^e ≤ 16^e (s(u - x)^e + s(v - x)^e)` and the moment bounds.
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The constant of `SemigroupTestProfile.integral_double_le`. -/
def semigroupTestDoubleConst (B : ℝ) (Mom : ℝ → ℝ) (ζ e : ℝ) : ℝ :=
  if e < 0 then (B * (80 / (5 + e)) + Mom 0) * semigroupTestMomConst B Mom ζ
  else 16 ^ e * (Mom 0 * semigroupTestMomConst B Mom (ζ + e) +
    Mom e * semigroupTestMomConst B Mom ζ)
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

namespace SemigroupTestProfile
variable {x : SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ} {g : SpaceTime → ℝ}

set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.measurable_double_T : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g →
    ∀ (e : ℝ),
      Measurable fun (w : RegularityStructures.SpaceTime × RegularityStructures.SpaceTime) ↦
        |g w.2| * RegularityStructures.torusParabolicSize (w.1 - w.2) ^ e
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SemigroupTestProfile.measurable_double_A : ∀ {x : RegularityStructures.SpaceTime} {lam B : ℝ} {Mom : ℝ → ℝ}
  {g : RegularityStructures.SpaceTime → ℝ},
  RegularityStructures.SemigroupTestProfile x lam B Mom g →
    ∀ (ζ : ℝ),
      Measurable fun (u : RegularityStructures.SpaceTime) ↦
        |g u| * RegularityStructures.torusParabolicSize (u - x) ^ ζ


set_option linter.unusedVariables false in
/-- Case `e ≥ 0` of the double integral. -/
private theorem integral_double_le_nonneg (h : SemigroupTestProfile x lam B Mom g) {ζ e : ℝ}
    (hζ : -5 < ζ) (he0 : 0 ≤ e) (hlam : 0 < lam) 
    (h_RegularityStructures_SemigroupTestProfile_double_integrand_eq : ∀ (g : RegularityStructures.SpaceTime → ℝ) (x : RegularityStructures.SpaceTime) (ζ e : ℝ)
      (w : RegularityStructures.SpaceTime × RegularityStructures.SpaceTime),
      |g w.1| * |g w.2| *
          (RegularityStructures.torusParabolicSize (w.1 - x) ^ ζ *
            RegularityStructures.torusParabolicSize (w.1 - w.2) ^ e) =
        |g w.1| * RegularityStructures.torusParabolicSize (w.1 - x) ^ ζ *
          (|g w.2| * RegularityStructures.torusParabolicSize (w.1 - w.2) ^ e))
    (h_RegularityStructures_integrable_integral_prod_mul_le : ∀ {A K : RegularityStructures.SpaceTime → ℝ}
      {T : RegularityStructures.SpaceTime → RegularityStructures.SpaceTime → ℝ},
      Measurable A →
        (∀ (u : RegularityStructures.SpaceTime), 0 ≤ A u) →
          (Measurable fun (w : RegularityStructures.SpaceTime × RegularityStructures.SpaceTime) ↦
              T w.1 w.2) →
            (∀ (u v : RegularityStructures.SpaceTime), 0 ≤ T u v) →
              (∀ (u : RegularityStructures.SpaceTime),
                  MeasureTheory.Integrable (T u) MeasureTheory.MeasureSpace.volume ∧
                    ∫ (v : RegularityStructures.SpaceTime), T u v ≤ K u) →
                MeasureTheory.Integrable (fun (u : RegularityStructures.SpaceTime) ↦ A u * K u)
                    MeasureTheory.MeasureSpace.volume →
                  MeasureTheory.Integrable
                      (fun (w : RegularityStructures.SpaceTime × RegularityStructures.SpaceTime) ↦
                        A w.1 * T w.1 w.2)
                      MeasureTheory.MeasureSpace.volume ∧
                    ∫ (w : RegularityStructures.SpaceTime × RegularityStructures.SpaceTime),
                        A w.1 * T w.1 w.2 ≤
                      ∫ (u : RegularityStructures.SpaceTime), A u * K u)
    (h_RegularityStructures_ae_rpow_mul_rpow_eq : ∀ (x : RegularityStructures.SpaceTime) (ζ e : ℝ),
      ∀ᵐ (u : RegularityStructures.SpaceTime),
        RegularityStructures.torusParabolicSize (u - x) ^ ζ *
            RegularityStructures.torusParabolicSize (u - x) ^ e =
          RegularityStructures.torusParabolicSize (u - x) ^ (ζ + e))
    (h_RegularityStructures_torusParabolicSize_nonneg : ∀ (z : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.torusParabolicSize z)
    (h_RegularityStructures_SemigroupTestProfile_nonneg_double_T : ∀ (g : RegularityStructures.SpaceTime → ℝ) (e : ℝ) (u v : RegularityStructures.SpaceTime),
      0 ≤ |g v| * RegularityStructures.torusParabolicSize (u - v) ^ e)
    (h_RegularityStructures_torusParabolicSize_sub_rpow_le : ∀ {e : ℝ},
      0 ≤ e →
        ∀ (u v x : RegularityStructures.SpaceTime),
          RegularityStructures.torusParabolicSize (u - v) ^ e ≤
            16 ^ e *
              (RegularityStructures.torusParabolicSize (u - x) ^ e +
                RegularityStructures.torusParabolicSize (v - x) ^ e))
    (h_RegularityStructures_SemigroupTestProfile_nonneg_double_A : ∀ (g : RegularityStructures.SpaceTime → ℝ) (x : RegularityStructures.SpaceTime) (ζ : ℝ)
      (u : RegularityStructures.SpaceTime),
      0 ≤ |g u| * RegularityStructures.torusParabolicSize (u - x) ^ ζ)
    (h_RegularityStructures_Phi43_measurable_torusParabolicSize : Measurable RegularityStructures.torusParabolicSize)
    :
    Integrable (fun w : SpaceTime × SpaceTime => |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e)) ∧
      ∫ w : SpaceTime × SpaceTime, |g w.1| * |g w.2| *
        (torusParabolicSize (w.1 - x) ^ ζ * torusParabolicSize (w.1 - w.2) ^ e) ≤
      semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
  have hζe : -5 < ζ + e := by linarith
  have h16 : (0 : ℝ) ≤ 16 ^ e := Real.rpow_nonneg (by norm_num) _
  have hAint := (h.integral_rpow_le hζ hlam)
  have hBint := (h.integral_rpow_le hζe hlam)
  -- the inner bound
  have hinner : ∀ u, Integrable (fun v => |g v| * torusParabolicSize (u - v) ^ e) ∧
      ∫ v, |g v| * torusParabolicSize (u - v) ^ e ≤
        16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e) := by
    intro u
    have hdom : Integrable (fun v => 16 ^ e * torusParabolicSize (u - x) ^ e * |g v| +
        16 ^ e * (|g v| * torusParabolicSize (v - x) ^ e)) :=
      (h.integrable_abs.const_mul _).add ((h.integrable_moment e he0).const_mul _)
    have hpt : ∀ v, |g v| * torusParabolicSize (u - v) ^ e ≤
        16 ^ e * torusParabolicSize (u - x) ^ e * |g v| +
          16 ^ e * (|g v| * torusParabolicSize (v - x) ^ e) := by
      intro v
      have := mul_le_mul_of_nonneg_left (h_RegularityStructures_torusParabolicSize_sub_rpow_le he0 u v x)
        (abs_nonneg (g v))
      linarith
    have hm : Measurable (fun v => |g v| * torusParabolicSize (u - v) ^ e) :=
      h.measurable_abs.mul ((h_RegularityStructures_Phi43_measurable_torusParabolicSize.comp
        (measurable_const.sub measurable_id)).pow_const _)
    refine ⟨hdom.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_), ?_⟩
    · rw [Real.norm_of_nonneg (h_RegularityStructures_SemigroupTestProfile_nonneg_double_T g e u v)]
      exact hpt v
    · calc ∫ v, |g v| * torusParabolicSize (u - v) ^ e
          ≤ ∫ v, (16 ^ e * torusParabolicSize (u - x) ^ e * |g v| +
              16 ^ e * (|g v| * torusParabolicSize (v - x) ^ e)) :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall (h_RegularityStructures_SemigroupTestProfile_nonneg_double_T g e u)) hdom
              (Filter.Eventually.of_forall hpt)
        _ = (16 ^ e * torusParabolicSize (u - x) ^ e * ∫ v, |g v|) +
              16 ^ e * ∫ v, |g v| * torusParabolicSize (v - x) ^ e := by
            rw [integral_add ((h.integrable_abs.const_mul _))
              ((h.integrable_moment e he0).const_mul _), integral_const_mul, integral_const_mul]
        _ ≤ 16 ^ e * torusParabolicSize (u - x) ^ e * Mom 0 + 16 ^ e * (Mom e * lam ^ e) := by
            have hc : 0 ≤ 16 ^ e * torusParabolicSize (u - x) ^ e :=
              mul_nonneg h16 (Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _)
            exact add_le_add (mul_le_mul_of_nonneg_left h.integral_abs_le hc)
              (mul_le_mul_of_nonneg_left (h.integral_moment_le e he0) h16)
        _ = 16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e) := by ring
  -- integrability of `A K`
  have hAK_eq : ∀ᵐ u : SpaceTime ∂volume,
      (|g u| * torusParabolicSize (u - x) ^ ζ) *
        (16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e)) =
      (16 ^ e * Mom 0) * (|g u| * torusParabolicSize (u - x) ^ (ζ + e)) +
        (16 ^ e * Mom e * lam ^ e) * (|g u| * torusParabolicSize (u - x) ^ ζ) := by
    filter_upwards [h_RegularityStructures_ae_rpow_mul_rpow_eq x ζ e] with u hu
    rw [← hu]
    ring
  have hAK : Integrable (fun u => (|g u| * torusParabolicSize (u - x) ^ ζ) *
      (16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e))) :=
    ((hBint.1.const_mul _).add (hAint.1.const_mul _)).congr (hAK_eq.mono fun u hu => hu.symm)
  have key := h_RegularityStructures_integrable_integral_prod_mul_le
    (A := fun u => |g u| * torusParabolicSize (u - x) ^ ζ)
    (K := fun u => 16 ^ e * (Mom 0 * torusParabolicSize (u - x) ^ e + Mom e * lam ^ e))
    (T := fun u v => |g v| * torusParabolicSize (u - v) ^ e)
    (h.measurable_double_A ζ) (h_RegularityStructures_SemigroupTestProfile_nonneg_double_A g x ζ) (h.measurable_double_T e)
    (h_RegularityStructures_SemigroupTestProfile_nonneg_double_T g e) hinner hAK
  simp only [h_RegularityStructures_SemigroupTestProfile_double_integrand_eq]
  refine ⟨key.1, key.2.trans ?_⟩
  rw [integral_congr_ae hAK_eq, integral_add (hBint.1.const_mul _) (hAint.1.const_mul _),
    integral_const_mul, integral_const_mul]
  have hm0 := h.mom_zero_nonneg
  have hMe : 0 ≤ Mom e := h.mom_nonneg hlam he0
  calc (16 ^ e * Mom 0 * ∫ u, |g u| * torusParabolicSize (u - x) ^ (ζ + e)) +
        16 ^ e * Mom e * lam ^ e * ∫ u, |g u| * torusParabolicSize (u - x) ^ ζ
      ≤ 16 ^ e * Mom 0 * (semigroupTestMomConst B Mom (ζ + e) * lam ^ (ζ + e)) +
        16 ^ e * Mom e * lam ^ e * (semigroupTestMomConst B Mom ζ * lam ^ ζ) :=
        add_le_add (mul_le_mul_of_nonneg_left hBint.2 (mul_nonneg h16 hm0))
          (mul_le_mul_of_nonneg_left hAint.2 (mul_nonneg (mul_nonneg h16 hMe)
            (Real.rpow_nonneg hlam.le _)))
    _ = semigroupTestDoubleConst B Mom ζ e * lam ^ (ζ + e) := by
        simp only [semigroupTestDoubleConst, not_lt.2 he0, ↓reduceIte]
        rw [Real.rpow_add hlam]
        ring
end SemigroupTestProfile
end RegularityStructures
end
