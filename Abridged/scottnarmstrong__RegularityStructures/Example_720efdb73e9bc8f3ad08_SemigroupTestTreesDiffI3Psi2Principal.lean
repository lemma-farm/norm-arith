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
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.RegularityStructures.Torus.Basic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.RegularityStructures.Torus.KernelBoundsBasic ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiPowers ====
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

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiLeaves ====
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
# Integrable majorants with an explicit integral bound

`SingularIntLe f X` records that `f` is integrable on space-time with `∫ f ≤ X`.  Using it we
package the integral estimates of products of centred parabolic powers that are needed for the
diagram bounds of the tree `I(Ψ³)Ψ`:

* two powers of total order `5 + η > 5` (from `integrable_and_integral_singularPow_mul_le`);
* three powers of total order `5 + η`, two of which have total order `< 5`;
* two powers of total order `< 5`, restricted to the time slab `|t| ≤ 2`.

Source: [Hai14] = arXiv:1303.5113v4, Lemma 10.14 and (10.37a).
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- `f` is integrable on space-time with integral at most `X`. -/
def SingularIntLe (f : SpaceTime → ℝ) (X : ℝ) : Prop :=
  Integrable f ∧ ∫ w, f w ≤ X
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.add : ∀ {f g : RegularityStructures.SpaceTime → ℝ} {X Y : ℝ},
  RegularityStructures.SingularIntLe f X →
    RegularityStructures.SingularIntLe g Y →
      RegularityStructures.SingularIntLe (fun (w : RegularityStructures.SpaceTime) ↦ f w + g w)
        (X + Y)
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.const_mul : ∀ {f : RegularityStructures.SpaceTime → ℝ} {X c : ℝ},
  RegularityStructures.SingularIntLe f X →
    0 ≤ c →
      RegularityStructures.SingularIntLe (fun (w : RegularityStructures.SpaceTime) ↦ c * f w)
        (c * X)
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.mono_right : ∀ {f : RegularityStructures.SpaceTime → ℝ} {X Y : ℝ},
  RegularityStructures.SingularIntLe f X → X ≤ Y → RegularityStructures.SingularIntLe f Y
set_option linter.unusedVariables false in
axiom _root_.RegularityStructures.SingularIntLe.of_le : ∀ {f F : RegularityStructures.SpaceTime → ℝ} {X : ℝ},
  RegularityStructures.SingularIntLe f X →
    MeasureTheory.AEStronglyMeasurable F MeasureTheory.MeasureSpace.volume →
      (∀ᵐ (w : RegularityStructures.SpaceTime), 0 ≤ F w) →
        (∀ᵐ (w : RegularityStructures.SpaceTime), F w ≤ f w) →
          RegularityStructures.SingularIntLe F X

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Dependencies.v8869557360b5.Phi43.BPHZ.TreeI3PsiDiagramMultiBasic ====
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
# Building blocks for the diagrams of `I(Ψ³)Ψ` with general exponents

* `TwoLevelLe G X`: a double-integral majorant `G` whose inner integrals are dominated by an
  integrable function of integral at most `X`; it yields integrability and a bound for every
  integrand dominated by `G`.
* the outer leaf and the inner integral of the chain diagram with the exponents
  `3`, `1 + α`, `1 + κ` (outer) and `4 + γ`, `2 + β` (inner), generalising the case
  `α = γ = 0`, `β = κ = δ` of `singularIntLe_outer_leaf` and `singularIntLe_inner`.

Source: [Hai14] = arXiv:1303.5113v4, (10.37a), Lemma 10.14, p. 167--168.
-/
@[expose] public noncomputable section
open MeasureTheory Set
namespace RegularityStructures
/-- A function `G` of two space-time variables is a **two-level majorant with bound `X`** if, for
almost every `w`, `G w` is integrable and its integral is at most `H w`, where `H` is integrable
with `∫ H ≤ X`. -/
def TwoLevelLe (G : SpaceTime → SpaceTime → ℝ) (X : ℝ) : Prop :=
  (∀ᵐ w : SpaceTime ∂volume, Integrable (G w)) ∧
    ∃ H : SpaceTime → ℝ, SingularIntLe H X ∧ ∀ᵐ w : SpaceTime ∂volume, ∫ v, G w v ≤ H w
end RegularityStructures
end
public section
open MeasureTheory Set
namespace RegularityStructures

end RegularityStructures
end

end

-- ==== Examples.scottnarmstrong__RegularityStructures.Examples.Example_720efdb73e9bc8f3ad08_SemigroupTestTreesDiffI3Psi2Principal ====
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
# The weighted principal diagram of the difference of `I(Ψ³)Ψ²`, for arbitrary `z, z'`

Without Hölder gains the weight `|δK(z, w)| |δK(z', v)| s(w - v)^(-(3+τ))` is dominated by
`B² 1_{|w.1| ≤ |z.1|+1} (s₃(z;w) + s₃(0;w)) (s₃(z';v) + s₃(0;v)) s_{3+τ}(w;v)`, a two-level majorant
with bound `C (1 + |z.1|)` (`i3Psi2PrincipalWeighted_twoLevelLe_global`).
-/
public section
open MeasureTheory Set
namespace RegularityStructures
set_option linter.unusedVariables false in
/-- **Two-level bound for the plain principal majorant on a slab.** -/
theorem twoLevelLe_principalPlain {τ : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1 / 2) 
    (h_RegularityStructures_singularPow_mul_le : ∀ {a b : ℝ},
      0 ≤ a →
        0 ≤ b →
          ∀ {p q w : RegularityStructures.SpaceTime},
            0 < RegularityStructures.torusParabolicSize (p - w) →
              0 < RegularityStructures.torusParabolicSize (q - w) →
                RegularityStructures.singularPow a p w * RegularityStructures.singularPow b q w ≤
                  RegularityStructures.singularPow (a + b) p w +
                    RegularityStructures.singularPow (a + b) q w)
    (h_RegularityStructures_singularIntLe_slab_singularPow : ∀ {a T : ℝ},
      0 < a →
        a < 5 →
          0 ≤ T →
            ∀ (c : RegularityStructures.SpaceTime),
              RegularityStructures.SingularIntLe
                ({w : RegularityStructures.SpaceTime | |w.1| ≤ T}.indicator
                  (RegularityStructures.singularPow a c))
                (80 / (5 - a) + 2 * T))
    (h_RegularityStructures_measurableSet_abs_fst_le : ∀ (T : ℝ), MeasurableSet {w : RegularityStructures.SpaceTime | |w.1| ≤ T})
    (h_RegularityStructures_singularPow_nonneg : ∀ (a : ℝ) (c w : RegularityStructures.SpaceTime), 0 ≤ RegularityStructures.singularPow a c w)
    (h_RegularityStructures_singularIntLe_mul_two : ∀ {a b η : ℝ},
      0 < a →
        a < 5 →
          0 < b →
            b < 5 →
              0 < η →
                a + b = 5 + η →
                  ∃ (C : ℝ),
                    0 ≤ C ∧
                      ∀ (p q : RegularityStructures.SpaceTime),
                        0 < RegularityStructures.torusParabolicSize (p - q) →
                          RegularityStructures.SingularIntLe
                            (fun (w : RegularityStructures.SpaceTime) ↦
                              RegularityStructures.singularPow a p w *
                                RegularityStructures.singularPow b q w)
                            (C * RegularityStructures.torusParabolicSize (p - q) ^ (-η)))
    (h_RegularityStructures_ae_torusParabolicSize_sub_pos : ∀ (z : RegularityStructures.SpaceTime),
      ∀ᵐ (w : RegularityStructures.SpaceTime), 0 < RegularityStructures.torusParabolicSize (z - w))
    (h_RegularityStructures_measurable_singularPow : ∀ (a : ℝ) (c : RegularityStructures.SpaceTime), Measurable (RegularityStructures.singularPow a c))
    :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : ℝ}, 0 ≤ T → ∀ z z' : SpaceTime,
      TwoLevelLe (fun w v => Set.indicator {w : SpaceTime | |w.1| ≤ T}
          (fun w => singularPow 3 z w + singularPow 3 0 w) w *
        ((singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v))
        (C * (1 + T)) := by
  obtain ⟨C1, hC1, h1⟩ := h_RegularityStructures_singularIntLe_mul_two (a := 3) (b := 3 + τ) (η := 1 + τ) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by ring)
  refine ⟨8 * C1 * 160, by positivity, ?_⟩
  intro T hT z z'
  set S : Set SpaceTime := {w : SpaceTime | |w.1| ≤ T} with hS
  set m : SpaceTime → ℝ := Set.indicator S (fun w => singularPow 3 z w + singularPow 3 0 w)
    with hm
  have hm0 : ∀ w, 0 ≤ m w := fun w => Set.indicator_nonneg (fun w _ =>
    add_nonneg (h_RegularityStructures_singularPow_nonneg _ _ _) (h_RegularityStructures_singularPow_nonneg _ _ _)) w
  have hmm : Measurable m := (((h_RegularityStructures_measurable_singularPow 3 z).add (h_RegularityStructures_measurable_singularPow 3 0))
    ).indicator (h_RegularityStructures_measurableSet_abs_fst_le T)
  have sl : ∀ c : SpaceTime, SingularIntLe (Set.indicator S (singularPow (4 + τ) c))
      (80 / (5 - (4 + τ)) + 2 * T) := fun c => h_RegularityStructures_singularIntLe_slab_singularPow (by linarith)
    (by linarith) hT c
  have hsum : SingularIntLe (fun w => 2 * Set.indicator S (singularPow (4 + τ) z) w +
      2 * Set.indicator S (singularPow (4 + τ) z') w + 4 * Set.indicator S (singularPow (4 + τ) 0) w)
      (2 * (80 / (5 - (4 + τ)) + 2 * T) + 2 * (80 / (5 - (4 + τ)) + 2 * T) +
        4 * (80 / (5 - (4 + τ)) + 2 * T)) :=
    (((sl z).const_mul (c := 2) (by norm_num)).add ((sl z').const_mul (c := 2)
      (by norm_num))).add ((sl 0).const_mul (c := 4) (by norm_num))
  set H : SpaceTime → ℝ := fun w => m w * (C1 * (singularPow (1 + τ) z' w +
    singularPow (1 + τ) 0 w)) with hH
  have hHle : SingularIntLe H (C1 * (2 * (80 / (5 - (4 + τ)) + 2 * T) +
      2 * (80 / (5 - (4 + τ)) + 2 * T) + 4 * (80 / (5 - (4 + τ)) + 2 * T))) := by
    refine ((hsum.const_mul (c := C1) hC1)).of_le ?_ ?_ ?_
    · exact ((hmm.mul (measurable_const.mul
        ((h_RegularityStructures_measurable_singularPow (1 + τ) z').add (h_RegularityStructures_measurable_singularPow (1 + τ) 0))))
        ).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun w => mul_nonneg (hm0 w)
        (mul_nonneg hC1 (add_nonneg (h_RegularityStructures_singularPow_nonneg _ _ _) (h_RegularityStructures_singularPow_nonneg _ _ _)))
    · filter_upwards [h_RegularityStructures_ae_torusParabolicSize_sub_pos z, h_RegularityStructures_ae_torusParabolicSize_sub_pos z',
        h_RegularityStructures_ae_torusParabolicSize_sub_pos 0] with w a b c
      by_cases hw : w ∈ S
      · simp only [hH, hm, Set.indicator_of_mem hw]
        have e1 := h_RegularityStructures_singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) a b
        have e2 := h_RegularityStructures_singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) a c
        have e3 := h_RegularityStructures_singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) c b
        have e4 := h_RegularityStructures_singularPow_mul_le (a := 3) (b := 1 + τ) (by norm_num) (by linarith) c c
        have e : (3 : ℝ) + (1 + τ) = 4 + τ := by ring
        rw [e] at e1 e2 e3 e4
        have : (singularPow 3 z w + singularPow 3 0 w) *
            (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w) ≤
            2 * singularPow (4 + τ) z w + 2 * singularPow (4 + τ) z' w +
              4 * singularPow (4 + τ) 0 w := by
          calc _ = singularPow 3 z w * singularPow (1 + τ) z' w +
                singularPow 3 z w * singularPow (1 + τ) 0 w +
                singularPow 3 0 w * singularPow (1 + τ) z' w +
                singularPow 3 0 w * singularPow (1 + τ) 0 w := by ring
            _ ≤ _ := by linarith
        calc (singularPow 3 z w + singularPow 3 0 w) *
            (C1 * (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w))
            = C1 * ((singularPow 3 z w + singularPow 3 0 w) *
              (singularPow (1 + τ) z' w + singularPow (1 + τ) 0 w)) := by ring
          _ ≤ C1 * (2 * singularPow (4 + τ) z w + 2 * singularPow (4 + τ) z' w +
              4 * singularPow (4 + τ) 0 w) := mul_le_mul_of_nonneg_left this hC1
      · simp [hH, hm, hw]
  have hint : ∀ p q : SpaceTime, 0 < torusParabolicSize (p - q) → SingularIntLe
      (fun v => singularPow 3 p v * singularPow (3 + τ) q v)
      (C1 * singularPow (1 + τ) p q) := fun p q hpq => by
    simpa [singularPow] using h1 p q hpq
  refine ⟨?_, H, ?_, ?_⟩
  · filter_upwards [h_RegularityStructures_ae_torusParabolicSize_sub_pos z', h_RegularityStructures_ae_torusParabolicSize_sub_pos 0] with w a b
    have i1 := (hint z' w a).1
    have i2 := (hint 0 w b).1
    exact ((i1.add i2).congr (Filter.Eventually.of_forall fun v => by
      simp only [Pi.add_apply]; ring)).const_mul (m w)
  · refine hHle.mono_right ?_
    have hτ' : 80 / (5 - (4 + τ)) ≤ 160 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hC : 0 ≤ C1 := hC1
    nlinarith
  · filter_upwards [h_RegularityStructures_ae_torusParabolicSize_sub_pos z', h_RegularityStructures_ae_torusParabolicSize_sub_pos 0] with w a b
    have j1 := hint z' w a
    have j2 := hint 0 w b
    have hs := j1.add j2
    rw [integral_const_mul]
    have := hs.2
    simp only at this
    rw [show (∫ v, (singularPow 3 z' v + singularPow 3 0 v) * singularPow (3 + τ) w v) =
      ∫ v, (singularPow 3 z' v * singularPow (3 + τ) w v +
        singularPow 3 0 v * singularPow (3 + τ) w v) from
        integral_congr_ae (Filter.Eventually.of_forall fun v => by ring)]
    refine mul_le_mul_of_nonneg_left (this.trans (le_of_eq ?_)) (hm0 w)
    simp only [singularPow, zero_sub]
    ring_nf
end RegularityStructures
end
