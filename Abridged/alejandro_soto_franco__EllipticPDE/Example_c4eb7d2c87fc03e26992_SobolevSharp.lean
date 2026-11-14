module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Tactic.Module
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

-- ==== Examples.alejandro_soto_franco__EllipticPDE.Examples.Example_c4eb7d2c87fc03e26992_SobolevSharp ====
/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Sharpness of the Sobolev embedding

The embedding of `H₀¹(Ω)` into `L^q(Ω)` is compact below the Sobolev conjugate and at the
conjugate itself is bounded. It is not compact there, and the obstruction is scaling: the
dilates of a fixed test function, renormalised to keep their `L^{2⋆}` norm, keep their gradient
norm as well and lose their `L²` norm.

Writing `φ_λ(x) = φ(x/λ)` and `v_λ = λ^{1 - d/2} φ_λ`, the three identities are

`‖v_λ‖_{L^{2⋆}} = ‖φ‖_{L^{2⋆}}`, `‖v_λ‖_{L²} = λ‖φ‖_{L²}`, `‖∂ᵢ v_λ‖_{L²} = ‖∂ᵢφ‖_{L²}`,

and the reason is `d/2⋆ = d/2 - 1`, the Sobolev relation itself. A family bounded in
`H₀¹(Ω)` whose images keep a fixed positive `L^{2⋆}` norm and tend to zero in `L²` has no
`L^{2⋆}`-convergent subsequence.

## Main declarations

* `EllipticPdes.Embedding.eLpNorm_dilate`: the `Lᵖ` seminorm of a dilate on the unit ball.
* `EllipticPdes.Embedding.eLpNorm_partialD_dilate`: the same for its partial derivatives.
* `EllipticPdes.Embedding.isTestFn_dilate`: a dilate of a test function is a test function.

## References

Y. Guo, *Partial Differential Equations*, Example IV.2.11.
-/
@[expose] public section
open MeasureTheory Metric
open scoped ENNReal NNReal
noncomputable section
namespace EllipticPdes.Embedding

variable {d : ℕ}

def sharpBump (d : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
variable {Ω : Set (EuclideanSpace ℝ (Fin d))}
def sharpFamily (d : ℕ) (lam : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (lam ^ (1 - (d : ℝ) / 2)) • fun x => (sharpBump d) (lam⁻¹ • x)

set_option linter.unusedVariables false in
/-- The `Lᵖ` seminorm of a renormalised dilate, with the two powers of `lam` collected. -/
lemma eLpNorm_sharpFamily {lam : ℝ} (h0 : 0 < lam) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞) 
    (h_EllipticPdes_Embedding_eLpNorm_dilate : ∀ {d : ℕ} {φ : EuclideanSpace ℝ (Fin d) → ℝ},
      Measurable φ →
        ∀ {lam : ℝ},
          0 < lam →
            ∀ {p : ENNReal},
              p ≠ 0 →
                p ≠ ⊤ →
                  MeasureTheory.eLpNorm (fun (x : EuclideanSpace ℝ (Fin d)) ↦ φ (lam⁻¹ • x)) p
                      MeasureTheory.MeasureSpace.volume =
                    ENNReal.ofReal (lam ^ d) ^ (1 / p.toReal) *
                      MeasureTheory.eLpNorm φ p MeasureTheory.MeasureSpace.volume)
    (h_EllipticPdes_Embedding_rpow_pow_mul : ∀ {lam : ℝ}, 0 < lam → ∀ (n : ℕ) (t : ℝ), (lam ^ n) ^ t = lam ^ ((↑n : ℝ) * t))
    :
    eLpNorm (sharpFamily d lam) p volume
      = ENNReal.ofReal (lam ^ (1 - (d : ℝ) / 2 + (d : ℝ) * (1 / p.toReal)))
        * eLpNorm (⇑(sharpBump d)) p volume := by
  rw [sharpFamily, eLpNorm_const_smul,
    h_EllipticPdes_Embedding_eLpNorm_dilate (sharpBump d).continuous.measurable h0 hp0 hpt,
    ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos h0 _),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (one_div_nonneg.mpr ENNReal.toReal_nonneg),
    h_EllipticPdes_Embedding_rpow_pow_mul h0, ← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos h0 _)),
    ← Real.rpow_add h0]
variable {lam : ℝ}
section Crit
variable {p' : ℝ≥0} [Fact (1 ≤ (p' : ℝ≥0∞))]
end Crit
end EllipticPdes.Embedding
