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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.vba9978046141.Phi43.BPHZ.TreeI3PsiPowers ====
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
# Integrals of products of two centred parabolic powers

For a centre `c` and exponent `a`, `singularPow a c w = s(c - w)^(-a)`.  If `0 < a, b < 5` and
`a + b > 5`, the product `singularPow a p * singularPow b q` is integrable and its integral is
at most `C * s(p - q)^(5 - a - b)` (the whole-space convolution estimate of [Hai14, Lemma 10.14],
in the form with two arbitrary centres, together with integrability of the integrand).

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14, (10.37a).
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- The parabolic power weight `s(c - w)^(-a)` centred at `c`. -/
def singularPow (a : ℝ) (c w : SpaceTime) : ℝ := torusParabolicSize (c - w) ^ (-a)
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_f42a62991528724c400e_TreeI3Psi2DiagramMultiChaosOnePot ====
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
# Convolution estimates for potentials with general kernel exponents

Generalisations of `power_mul_abs_J_le`, `abs_J_mul_J_le` and `integral_pot_mul_pot_le` of the
chaos-`1` part of `I(Ψ³)Ψ²` to kernels `J` with `|J| ≤ B s^(-j)` of possibly different orders
`j` (the kernel `J_a` of order `3` and the kernel difference `ΔJ` of order `3 + θ`), and to two
different kernels in the pairing of two potentials.
-/
public section
open MeasureTheory
namespace RegularityStructures
set_option linter.unusedVariables false in
/-- `∫ |J₁(w - y)| |J₂(w' - y)| dy ≤ C B₁ B₂ s(w - w')^(5-j₁-j₂)`. -/
theorem abs_J_mul_J_le_gen {j₁ j₂ : ℝ} (hj₁ : 0 < j₁)
    (hj₁5 : j₁ < 5) (hj₂ : 0 < j₂) (hj₂5 : j₂ < 5) (hj : 5 < j₁ + j₂) 
    (h_RegularityStructures_ae_torusParabolicSize_sub_pos : ∀ (z : RegularityStructures.SpaceTime),
      ∀ᵐ (w : RegularityStructures.SpaceTime), 0 < RegularityStructures.torusParabolicSize (z - w))
    (h_RegularityStructures_integrable_and_integral_singularPow_mul_le : ∀ {a b : ℝ},
      0 < a →
        a < 5 →
          0 < b →
            b < 5 →
              5 < a + b →
                ∃ (C : ℝ),
                  0 ≤ C ∧
                    ∀ (p q : RegularityStructures.SpaceTime),
                      0 < RegularityStructures.torusParabolicSize (p - q) →
                        MeasureTheory.Integrable
                            (fun (w : RegularityStructures.SpaceTime) ↦
                              RegularityStructures.singularPow a p w *
                                RegularityStructures.singularPow b q w)
                            MeasureTheory.MeasureSpace.volume ∧
                          ∫ (w : RegularityStructures.SpaceTime),
                              RegularityStructures.singularPow a p w *
                                RegularityStructures.singularPow b q w ≤
                            C * RegularityStructures.torusParabolicSize (p - q) ^ (5 - a - b))
    (h_RegularityStructures_singularPow_nonneg : ∀ (a : ℝ) (c w : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.singularPow a c w)
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {J₁ J₂ : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      Measurable J₁ → Measurable J₂ →
      (∀ x, 0 < torusParabolicSize x → |J₁ x| ≤ B₁ * torusParabolicSize x ^ (-j₁)) →
      (∀ x, 0 < torusParabolicSize x → |J₂ x| ≤ B₂ * torusParabolicSize x ^ (-j₂)) →
      ∀ w w' : SpaceTime, 0 < torusParabolicSize (w - w') →
        Integrable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) ∧
          ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤
            C * B₁ * B₂ * torusParabolicSize (w - w') ^ (5 - j₁ - j₂) := by
  obtain ⟨C, hC, h⟩ := h_RegularityStructures_integrable_and_integral_singularPow_mul_le (a := j₁) (b := j₂)
    hj₁ hj₁5 hj₂ hj₂5 hj
  refine ⟨C, hC, fun {J₁ J₂ B₁ B₂} hB₁ hB₂ hJ₁m hJ₂m hJ₁ hJ₂ w w' hww => ?_⟩
  obtain ⟨i, b⟩ := h w w' hww
  have hmaj : Integrable (fun y => B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y)) :=
    i.const_mul _
  have hm : Measurable (fun y => |J₁ (w - y)| * |J₂ (w' - y)|) :=
    (continuous_abs.measurable.comp (hJ₁m.comp (measurable_const.sub measurable_id))).mul
      (continuous_abs.measurable.comp (hJ₂m.comp (measurable_const.sub measurable_id)))
  have hle : ∀ᵐ y : SpaceTime ∂volume, |J₁ (w - y)| * |J₂ (w' - y)| ≤
      B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y) := by
    filter_upwards [h_RegularityStructures_ae_torusParabolicSize_sub_pos w, h_RegularityStructures_ae_torusParabolicSize_sub_pos w'] with y a' b'
    have := mul_le_mul (hJ₁ _ a') (hJ₂ _ b') (abs_nonneg _) (mul_nonneg hB₁
      (h_RegularityStructures_singularPow_nonneg j₁ w y))
    refine this.trans (le_of_eq ?_)
    unfold singularPow
    ring
  refine ⟨Integrable.mono' hmaj hm.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hle] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hy
  · calc ∫ y, |J₁ (w - y)| * |J₂ (w' - y)| ≤
          ∫ y, B₁ * B₂ * (singularPow j₁ w y * singularPow j₂ w' y) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y =>
            mul_nonneg (abs_nonneg _) (abs_nonneg _)) hmaj hle
      _ = B₁ * B₂ * ∫ y, singularPow j₁ w y * singularPow j₂ w' y := by rw [integral_const_mul]
      _ ≤ B₁ * B₂ * (C * torusParabolicSize (w - w') ^ (5 - j₁ - j₂)) :=
          mul_le_mul_of_nonneg_left b (mul_nonneg hB₁ hB₂)
      _ = _ := by ring
end RegularityStructures
end
