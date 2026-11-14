module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Tactic

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.RegularityStructures.Torus.Basic ====
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
set_option linter.unusedVariables false
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.RegularityStructures.BPHZ.TreeI2Psi2DiagramLint ====
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
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Lower-integral bounds: a small calculus

`i2Psi2LintBound μ f M` says `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`.  It is the form in which the
singular-integral estimates of the tree `I(Ψ²) Ψ²` ([Hai14, (10.39)-(10.42)]) are chained: it needs
no integrability bookkeeping, is monotone, additive, scales by constants, and passes through
Tonelli (`i2Psi2LintBound.of_prod_symm`) and products of independent factors.  The final
`abs_integral_le_of_i2Psi2LintBound` turns such a bound on `|f|` into integrability of `f` and a
bound on `|∫ f|`.
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures
/-- `f` has lower integral at most `M`: `∫⁻ ofReal (f a) ∂μ ≤ ofReal M`. -/
def i2Psi2LintBound {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) (M : ℝ) :
    Prop :=
  ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ENNReal.ofReal M
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.i2Psi2LintBound.mono_ae.{w_u_1} : ∀ {α : Type w_u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ}
  {M M' : ℝ},
  RegularityStructures.i2Psi2LintBound μ g M →
    (∀ᵐ (a : α) ∂μ, f a ≤ g a) → M ≤ M' → RegularityStructures.i2Psi2LintBound μ f M'
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.i2Psi2LintBound.add.{w_u_1} : ∀ {α : Type w_u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f g : α → ℝ} {M N : ℝ},
  AEMeasurable f μ →
    (∀ (a : α), 0 ≤ f a) →
      (∀ (a : α), 0 ≤ g a) →
        0 ≤ M →
          0 ≤ N →
            RegularityStructures.i2Psi2LintBound μ f M →
              RegularityStructures.i2Psi2LintBound μ g N →
                RegularityStructures.i2Psi2LintBound μ (fun (a : α) ↦ f a + g a) (M + N)
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.i2Psi2LintBound.const_mul.{w_u_1} : ∀ {α : Type w_u_1} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} {f : α → ℝ} {M c : ℝ},
  0 ≤ c →
    RegularityStructures.i2Psi2LintBound μ f M →
      RegularityStructures.i2Psi2LintBound μ (fun (a : α) ↦ c * f a) (c * M)
variable {β : Type*} [MeasurableSpace β] {ν : Measure β}
end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.RegularityStructures.Torus.KernelBoundsBasic ====
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
set_option linter.unusedVariables false
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v9094c93fb545.Phi43.BPHZ.TreeI2Psi2DiagramBounded ====
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
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Bounded integrals of products of singular weights over a time slab

All the variables of the diagram integrals of the tree `I(Ψ²) Ψ²` lie in a time slab
`|t - τ| ≤ 2` (the kernels `K` are supported in `|t| ≤ 1` and the base points are within
distance `1` of `τ`).  On the slab every parabolic distance to a point of the slab is at most `3`,
so a product of weights `s(pᵢ - w)^(-λᵢ)` with total exponent `λ₁ + λ₂ + λ₃ < 5` has a bounded
integral: `i2Psi2LintBound_slab_triple`, [Hai14, (10.37a), Lemma 10.14].
-/
@[expose] public noncomputable section
namespace RegularityStructures
/-- The indicator of the time slab `|t - τ| ≤ 2`. -/
def i2Psi2Slab (τ : ℝ) (w : SpaceTime) : ℝ :=
  if |w.1 - τ| ≤ 2 then 1 else 0
end RegularityStructures
end
public section
open MeasureTheory
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_52ba0f018120b0aca10f_GammaMomentMajorant ====
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
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
/-!
# Lower-integral bounds for kernels with a pointwise majorant

The estimates of `TreeI2Psi2DiagramMulti*` are stated for the increment of a kernel `K` of order
`3`.  We prove the same estimates for an arbitrary kernel `A` (a gradient increment, a Taylor
remainder, ...) that is only known through the pointwise majorant

`|A w| ≤ slab(w) * M * r^a * (s(y - w)^(-p) + s(x - w)^(-p))`,

where `slab(w) = 1` for `|w₀ - x₀| ≤ 2` and `0` otherwise (`gammaMajorant`).  The exponent `p` is
the decay of `A` at its singularities and `a` the gain in `r = s(y - x)`; they are independent.

* `gammaMajorant_lint_single`: `∫ |A| s(g - w)^(-e) ≲ M r^a (s(y-g)^(-(p+e-5)) + s(x-g)^(-(p+e-5)))`
  for `0 < p < 5`, `0 < e < 5`, `p + e > 5`;
* `gammaMajorant_lint_slab`: `∫ |A| s(g₁ - w)^(-l₁) s(g₂ - w)^(-l₂) ≲ M r^a` for `p + l₁ + l₂ < 5`;
* `gammaMajorant_lint_diag`: `∬ |A(w)| |A'(w')| s(w' - w)^(-e) ≲ M M' r^a r'^a'`.
-/
@[expose] public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
/-- The pointwise majorant `|A w| ≤ slab * M r^a (s(y-w)^(-p) + s(x-w)^(-p))`, `r = s(y-x)`. -/
def gammaMajorant (A : SpaceTime → ℝ) (x y : SpaceTime) (r M a p : ℝ) : Prop :=
  0 ≤ r ∧ 0 ≤ M ∧ Measurable A ∧ ∀ w : SpaceTime, 0 < torusParabolicSize (y - w) →
    0 < torusParabolicSize (x - w) →
      |A w| ≤ i2Psi2Slab x.1 w * (M * r ^ a *
        (torusParabolicSize (y - w) ^ (-p) + torusParabolicSize (x - w) ^ (-p)))
end RegularityStructures.Phi43
end
public section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures


set_option linter.unusedVariables false in
/-- **Majorant kernel against `s(g - w)^(-e)`.** -/
theorem gammaMajorant_lint_single {a p e : ℝ} (hp : 0 < p) (hp5 : p < 5) (he : 0 < e)
    (he5 : e < 5) (hpe : 5 < p + e) 
    (h_RegularityStructures_i2Psi2LintBound_rpow_mul_rpow_of_gt : ∀ {a b : ℝ},
      0 < a →
        a < 5 →
          0 < b →
            b < 5 →
              5 < a + b →
                ∃ (C : ℝ),
                  0 ≤ C ∧
                    ∀ (p q : RegularityStructures.SpaceTime),
                      0 < RegularityStructures.torusParabolicSize (p - q) →
                        RegularityStructures.i2Psi2LintBound MeasureTheory.MeasureSpace.volume
                          (fun (w : RegularityStructures.SpaceTime) ↦
                            RegularityStructures.torusParabolicSize (p - w) ^ (-a) *
                              RegularityStructures.torusParabolicSize (q - w) ^ (-b))
                          (C * RegularityStructures.torusParabolicSize (p - q) ^ (5 - a - b)))
    (h_RegularityStructures_Phi43_gmaj_weight_nonneg : ∀ (p g : RegularityStructures.SpaceTime) (a b : ℝ) (w : RegularityStructures.SpaceTime),
      0 ≤
        RegularityStructures.torusParabolicSize (p - w) ^ a *
          RegularityStructures.torusParabolicSize (g - w) ^ b)
    (h_RegularityStructures_Phi43_gmaj_measurable_weight : ∀ (p g : RegularityStructures.SpaceTime) (a b : ℝ),
      Measurable fun (w : RegularityStructures.SpaceTime) ↦
        RegularityStructures.torusParabolicSize (p - w) ^ a *
          RegularityStructures.torusParabolicSize (g - w) ^ b)
    (h_RegularityStructures_i2Psi2Slab_le_one : ∀ (τ : ℝ) (w : RegularityStructures.SpaceTime), RegularityStructures.i2Psi2Slab τ w ≤ 1)
    (h_RegularityStructures_ae_torusParabolicSize_sub_pos : ∀ (z : RegularityStructures.SpaceTime),
      ∀ᵐ (w : RegularityStructures.SpaceTime), 0 < RegularityStructures.torusParabolicSize (z - w))
    (h_RegularityStructures_torusParabolicSize_nonneg : ∀ (z : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.torusParabolicSize z)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : SpaceTime → ℝ} {x y : SpaceTime} {r M : ℝ},
      gammaMajorant A x y r M a p → ∀ g : SpaceTime, 0 < torusParabolicSize (y - g) →
        0 < torusParabolicSize (x - g) →
        i2Psi2LintBound volume (fun w => |A w| * torusParabolicSize (g - w) ^ (-e))
          (C * M * r ^ a *
            (torusParabolicSize (y - g) ^ (-(p + e - 5)) +
              torusParabolicSize (x - g) ^ (-(p + e - 5)))) := by
  obtain ⟨CG, hCG, hG⟩ := h_RegularityStructures_i2Psi2LintBound_rpow_mul_rpow_of_gt (a := p) (b := e) hp hp5 he he5 hpe
  refine ⟨CG, hCG, ?_⟩
  intro A x y r M hA g hyg hxg
  obtain ⟨hr0, hM, -, hAb⟩ := hA
  have e0 : (5 : ℝ) - p - e = -(p + e - 5) := by ring
  have gy := hG y g hyg
  have gx := hG x g hxg
  rw [e0] at gy gx
  have s := gy.add (g := fun w => torusParabolicSize (x - w) ^ (-p) *
      torusParabolicSize (g - w) ^ (-e)) (h_RegularityStructures_Phi43_gmaj_measurable_weight y g _ _).aemeasurable
    (h_RegularityStructures_Phi43_gmaj_weight_nonneg y g _ _) (h_RegularityStructures_Phi43_gmaj_weight_nonneg x g _ _)
    (mul_nonneg hCG (Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _))
    (mul_nonneg hCG (Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _)) gx
  have hr := Real.rpow_nonneg hr0 a
  have c := s.const_mul (c := M * r ^ a) (mul_nonneg hM hr)
  refine c.mono_ae ?_ (le_of_eq (by ring))
  filter_upwards [h_RegularityStructures_ae_torusParabolicSize_sub_pos y, h_RegularityStructures_ae_torusParabolicSize_sub_pos x]
    with w hy hx
  have h := hAb w hy hx
  have n2 : 0 ≤ torusParabolicSize (g - w) ^ (-e) :=
    Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _
  have hsl := h_RegularityStructures_i2Psi2Slab_le_one x.1 w
  have hsum : 0 ≤ M * r ^ a * (torusParabolicSize (y - w) ^ (-p) +
      torusParabolicSize (x - w) ^ (-p)) :=
    mul_nonneg (mul_nonneg hM hr) (add_nonneg (Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _)
      (Real.rpow_nonneg (h_RegularityStructures_torusParabolicSize_nonneg _) _))
  calc |A w| * torusParabolicSize (g - w) ^ (-e)
      ≤ (M * r ^ a * (torusParabolicSize (y - w) ^ (-p) +
        torusParabolicSize (x - w) ^ (-p))) * torusParabolicSize (g - w) ^ (-e) :=
        mul_le_mul_of_nonneg_right (h.trans (mul_le_of_le_one_left hsum hsl)) n2
    _ = _ := by ring
end RegularityStructures.Phi43
end
