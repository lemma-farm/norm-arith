module

public import Mathlib
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.FDeriv.Partial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.Homogenization.Ambient.Basic ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
open scoped BigOperators
namespace Homogenization
abbrev Vec (d : ℕ) := Fin d → ℝ

end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.Homogenization.Sobolev.WeakDerivatives ====
public section
-- Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi.
-- Released under Apache 2.0 license.
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
namespace Homogenization
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)

namespace HasWeakPartialDerivOn
end HasWeakPartialDerivOn
end Homogenization

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Statements.Roots.SpaceGrad ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Statement file: `spaceGrad` (Roots).
This file contains exactly one declaration of the formalization's public statement surface. -/
@[expose] public section
open MeasureTheory Filter Topology Homogenization
namespace AVenhance
/-- Classical gradient of a differentiable function, coordinatewise. -/
noncomputable def spaceGrad (f : Vec 2 → ℝ) : Vec 2 → Vec 2 :=
  fun x i => fderiv ℝ f x (basisVec i)
end AVenhance

end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.Calculus ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Calculus infrastructure for the AMNR tensors. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
/-! The mixed calculus below keeps spatial and material operations ordered. -/
/-- Space-time coordinate carrier used only to express the differential operators. -/
abbrev AmnrSpace := ℝ × Vec 2
/-- `none` is the material direction; `some i` is the i-th spatial direction. -/
def amnrDirection (b : AmnrSpace → Vec 2) (d : Option (Fin 2)) (z : AmnrSpace) : AmnrSpace :=
  match d with
  | none => (1, b z)
  | some i => (0, basisVec i)
/-- A directional differential operator on the actual space-time function. -/
def amnrOp (b : AmnrSpace → Vec 2) (d : Option (Fin 2))
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ := fderiv ℝ f z (amnrDirection b d z)
/-- Ordered differential words, with the outermost operator at the head. -/
def amnrWord (b : AmnrSpace → Vec 2) : List (Option (Fin 2)) →
    (AmnrSpace → ℝ) → AmnrSpace → ℝ
  | [], f => f
  | d :: w, f => amnrOp b d (amnrWord b w f)

/-- Radius weights associated with an ordered mixed derivative. -/
def amnrWeight (S H : ℝ) (w : List (Option (Fin 2))) : ℝ :=
  (w.map (fun d => match d with | none => H | some _ => S)).prod
axiom amnrWeight_nonneg {S H : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (w : List (Option (Fin 2))) : 0 ≤ amnrWeight S H w

def amnrBudget (w : List (Option (Fin 2))) : ℕ :=
  (w.map (fun d => match d with | none => 2 | some _ => 1)).sum
axiom amnrBudget_length_le (w : List (Option (Fin 2))) : w.length ≤ amnrBudget w
axiom amnrWord_append {b : AmnrSpace → Vec 2} (w v : List (Option (Fin 2)))
    (f : AmnrSpace → ℝ) : amnrWord b (w ++ v) f = amnrWord b w (amnrWord b v f)

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.Induction ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Induction infrastructure for the AMNR tensors. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

def amnrMixedWord (α : List (Fin 2)) (ℓ : ℕ) : List (Option (Fin 2)) :=
  α.map some ++ List.replicate ℓ none

axiom amnrMixedWord_budget (α : List (Fin 2)) (ℓ : ℕ) :
    amnrBudget (amnrMixedWord α ℓ) = α.length + 2 * ℓ
axiom amnrMixedWord_weight (S H : ℝ) (α : List (Fin 2)) (ℓ : ℕ) :
    amnrWeight S H (amnrMixedWord α ℓ) = S ^ α.length * H ^ ℓ
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.FrozenBridge ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Infrastructure for the AMNR tensors: bridge from the recursion to the actual flow data. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
def amnrVelocityGradient (b : AmnrSpace → Vec 2) (i p : Fin 2) (z : AmnrSpace) : ℝ :=
  AVenhance.spaceGrad (fun y => b (z.1, y) i) z.2 p
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.SpatialCommutator ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Explicit spatial/material commutators used in the temperature cascade. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
/-- Every finite ordered word preserves classical smoothness on an open domain. -/
axiom amnrWord_contDiffOn_infty {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (w : List (Option (Fin 2))) : ContDiffOn ℝ (⊤ : ℕ∞) (amnrWord b w f) U

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.MixedSubwordBudget ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Separate spatial and material budgets for actual Leibniz subwords. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- A Leibniz subword is canonical and never gains spatial or material
budget. The material count is controlled separately for strong induction. -/
axiom amnrMixedWord_subword_normalForm {α : List (Fin 2)} {n : ℕ}
    {v : List (Option (Fin 2))} (hv : v.Sublist (amnrMixedWord α n)) :
    ∃ η : List (Fin 2), ∃ r : ℕ, v = amnrMixedWord η r ∧
      r ≤ n ∧ η.length + 2 * r ≤ α.length + 2 * n
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v44cb4a5eb9cc.AVenhance.Infra.Section4.Amnr.MaterialGradientEstimate ====
public section
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Quantitative material/spatial commutation for arbitrary outer words. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
/-- Every outer word can be applied to the actual material/spatial
commutator; complementary subwords control each product factor. -/
axiom amnr_word_material_spatial_abs_le_of_bounds
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (w : List (Option (Fin 2))) (i : Fin 2) (z : AmnrSpace) {S H F B G : ℝ}
    (hS : 0 ≤ S) (hH : 0 ≤ H) (hB : 0 ≤ B) (hG : 0 ≤ G)
    (hF : |amnrWord b (w ++ [some i, none]) f z| ≤ F)
    (hBb : ∀ p v, v.Sublist w →
      |amnrWord b v (amnrVelocityGradient b p i) z| ≤ B * amnrWeight S H v)
    (hGb : ∀ p v, v.Sublist w →
      |amnrWord b v (amnrOp b (some p) f) z| ≤ G * amnrWeight S H v) :
    |amnrWord b w (amnrOp b none (amnrOp b (some i) f)) z| ≤
      F + (2 : ℝ) ^ (w.length + 1) * B * G * amnrWeight S H w
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_7d7d82fda59cf1c1e6a3_TransportedGradientInduction ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Strong material induction for spatial derivatives of transported scalars. -/
@[expose] public section
noncomputable section
open Homogenization MeasureTheory Set
namespace AVenhance.Infra.Section4
/-- A scalar's material/spatial jets control its differentiated material jets
using only strictly lower material orders of the actual velocity gradient.
This conditional calculus lemma does not assert the source primitive bounds. -/
theorem amnr_material_gradient_mixed_abs_le_of_lower_gradient_bounds
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {N cut : ℕ} {S H F Cb : ℝ} (hS : 0 ≤ S) (hH : 0 ≤ H)
    (hF : 0 ≤ F) (hCb : 0 ≤ Cb) (z : AmnrSpace)
    (hfb : ∀ η r, η.length + 2 * r ≤ N →
      |amnrWord b (amnrMixedWord η r) f z| ≤ F * S ^ η.length * H ^ r)
    (hBb : ∀ p i η r, r < cut → η.length + 2 * r + 2 ≤ N →
      |amnrWord b (amnrMixedWord η r) (amnrVelocityGradient b p i) z| ≤
        Cb * H * S ^ η.length * H ^ r)
    (n : ℕ) (hn : n ≤ cut) (α : List (Fin 2)) (j : ℕ)
    (hbudget : α.length + 1 + 2 * (n + j) ≤ N) (i : Fin 2) :
    |amnrWord b (amnrMixedWord α n)
      (amnrOp b (some i) (amnrWord b (List.replicate j none) f)) z| ≤
      (1 + (2 : ℝ) ^ (N + 1) * Cb) ^ n * F * S ^ (α.length + 1) * H ^ (n + j) := by
  let R := 1 + (2 : ℝ) ^ (N + 1) * Cb
  have hR : 1 ≤ R := by
    have hh : 0 ≤ (2 : ℝ) ^ (N + 1) * Cb := by positivity
    dsimp [R]
    linarith only [hh]
  have hbound : ∀ n : ℕ, n ≤ cut → ∀ α : List (Fin 2), ∀ j : ℕ,
      α.length + 1 + 2 * (n + j) ≤ N → ∀ i : Fin 2,
      |amnrWord b (amnrMixedWord α n)
        (amnrOp b (some i) (amnrWord b (List.replicate j none) f)) z| ≤
        R ^ n * F * S ^ (α.length + 1) * H ^ (n + j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn α j hbudget i
      cases n with
      | zero =>
        have hh := hfb (α ++ [i]) j (by simp only [List.length_append, List.length_singleton]; omega)
        simp only [amnrMixedWord, List.replicate_zero, List.append_nil]
        change |amnrWord b (α.map some)
          (amnrWord b [some i] (amnrWord b (List.replicate j none) f)) z| ≤ _
        rw [← amnrWord_append, ← amnrWord_append]
        simp only [amnrMixedWord, List.map_append, List.map_singleton, List.length_append,
          List.length_singleton] at hh
        simpa only [List.append_assoc, pow_zero, one_mul, Nat.zero_add] using hh
      | succ n =>
        let w := amnrMixedWord α n
        let g := amnrWord b (List.replicate j none) f
        have hg : ContDiff ℝ (⊤ : ℕ∞) g := contDiffOn_univ.mp
          (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn hf.contDiffOn (List.replicate j none))
        have hshift : amnrOp b none g = amnrWord b (List.replicate (j + 1) none) f := by
          simp only [List.replicate_succ, amnrWord, g]
        have hfirst : |amnrWord b (w ++ [some i, none]) g z| ≤
            R ^ n * F * S ^ (α.length + 1) * H ^ (n + j + 1) := by
          rw [amnrWord_append]
          change |amnrWord b w (amnrOp b (some i) (amnrOp b none g)) z| ≤ _
          rw [hshift]
          simpa only [Nat.add_assoc] using ih n (by omega) (by omega) α (j + 1) (by omega) i
        have hBsub : ∀ p v, v.Sublist w →
            |amnrWord b v (amnrVelocityGradient b p i) z| ≤ (Cb * H) * amnrWeight S H v := by
          intro p v hv
          obtain ⟨η, r, heq, hr, hη⟩ := amnrMixedWord_subword_normalForm hv
          rw [heq, amnrMixedWord_weight]
          have hh := hBb p i η r (by omega) (by omega)
          convert hh using 1
          ring
        have hGsub : ∀ p v, v.Sublist w →
            |amnrWord b v (amnrOp b (some p) g) z| ≤
              (R ^ n * F * S * H ^ j) * amnrWeight S H v := by
          intro p v hv
          obtain ⟨η, r, heq, hr, hη⟩ := amnrMixedWord_subword_normalForm hv
          rw [heq, amnrMixedWord_weight]
          have hh := ih r (by omega) (by omega) η j (by omega) p
          have hp := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR hr)
            (show 0 ≤ F * S ^ (η.length + 1) * H ^ (r + j) by positivity)
          refine hh.trans ?_
          calc
            _ = R ^ r * (F * S ^ (η.length + 1) * H ^ (r + j)) := by ring
            _ ≤ R ^ n * (F * S ^ (η.length + 1) * H ^ (r + j)) := hp
            _ = _ := by rw [pow_succ, pow_add]; ring
        have hh := amnr_word_material_spatial_abs_le_of_bounds hb hg w i z hS hH
          (show 0 ≤ Cb * H by positivity)
          (show 0 ≤ R ^ n * F * S * H ^ j by have := hR.trans' (by norm_num : (0 : ℝ) ≤ 1); positivity)
          hfirst hBsub hGsub
        have heq : amnrWord b (amnrMixedWord α (n + 1)) (amnrOp b (some i) g) =
            amnrWord b w (amnrOp b none (amnrOp b (some i) g)) := by
          unfold amnrMixedWord
          rw [List.replicate_succ', ← List.append_assoc, amnrWord_append]
          rfl
        rw [heq]
        refine hh.trans ?_
        have hlen : w.length ≤ N := by
          have hh := amnrBudget_length_le w
          have he : amnrBudget w = α.length + 2 * n := amnrMixedWord_budget α n
          omega
        have hp : (2 : ℝ) ^ (w.length + 1) ≤ (2 : ℝ) ^ (N + 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hd := mul_le_mul_of_nonneg_right hp
          (show 0 ≤ (Cb * H) * (R ^ n * F * S * H ^ j) * amnrWeight S H w by
            have := amnrWeight_nonneg hS hH w
            have := hR.trans' (by norm_num : (0 : ℝ) ≤ 1)
            positivity)
        calc
          _ = R ^ n * F * S ^ (α.length + 1) * H ^ (n + j + 1) +
              (2 : ℝ) ^ (w.length + 1) *
                ((Cb * H) * (R ^ n * F * S * H ^ j) * amnrWeight S H w) := by ring
          _ ≤ R ^ n * F * S ^ (α.length + 1) * H ^ (n + j + 1) +
              (2 : ℝ) ^ (N + 1) *
                ((Cb * H) * (R ^ n * F * S * H ^ j) * amnrWeight S H w) := add_le_add le_rfl hd
          _ = _ := by
            rw [amnrMixedWord_weight]
            dsimp [R]
            rw [pow_succ, pow_add, pow_add, pow_succ]
            ring
  exact hbound n hn α j hbudget i
end AVenhance.Infra.Section4
