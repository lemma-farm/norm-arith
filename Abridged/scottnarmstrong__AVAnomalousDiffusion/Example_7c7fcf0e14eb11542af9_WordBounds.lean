module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Algebra.Field.Periodic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.Homogenization.Ambient.Basic ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.Homogenization.Sobolev.WeakDerivatives ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Statements.Roots.SpaceGrad ====
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

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Section4.CoarseCoeff.Form ====
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
/-! # Structural coarse-coefficient interface for 

The polynomial family is linear in K and κ and quadratic in F. Its two
scalar coefficients are bounded by one. Both the left-Jacobian coefficient and its
Infra candidate belong to this family; no analytic estimate is assumed.
-/
@[expose] public section
noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance
abbrev CoarseMatrix := Matrix (Fin 2) (Fin 2) ℝ
def coarseCoeffPolynomial (a b κ : ℝ) (K F : CoarseMatrix) : CoarseMatrix :=
  a • (K * (F - 1)) + b • ((F.transpose - 1) * (K - κ • (1 : CoarseMatrix)) * F)

namespace LeftJacobian
end LeftJacobian
end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Section4.CoarseCoeff.Regularity ====
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
@[expose] public section
noncomputable section
open Homogenization Filter Topology
open scoped Matrix.Norms.Elementwise ContDiff
namespace AVenhance.Infra.Section4
open AVenhance
/-- Entrywise proof avoids any choice of a matrix operator norm. -/
axiom coarseCoeff_matrix_mul_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞ω} {K F : E → CoarseMatrix} (hK : ContDiff ℝ n K) (hF : ContDiff ℝ n F) :
    ContDiff ℝ n (fun x => K x * F x)

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Section4.IteratesWordDiffusion ====
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
/-! Ordered spatial words and exact diffusion commutation for l.V. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance
/-- Ordered coordinate derivatives, with the outermost derivative first. -/
def iterateSpatialWord : List (Fin 2) → (Vec 2 → ℝ) → Vec 2 → ℝ
  | [], f => f
  | i :: w, f => fun x => spaceGrad (iterateSpatialWord w f) x i

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Section4.IteratesWordLeibniz ====
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
/-! Exact ordered spatial Leibniz expansions for coefficient-gradient products. -/
@[expose] public section
noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open AVenhance
/-- Each ordered derivative is assigned to exactly one of the two factors. -/
def iterateSpatialSplits : List (Fin 2) → List (List (Fin 2) × List (Fin 2))
  | [] => [([], [])]
  | i :: w => (iterateSpatialSplits w).flatMap (fun p => [(i :: p.1, p.2), (p.1, i :: p.2)])

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Section4.IteratesWordCoefficientSplit ====
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
/-! The literal time-only K coefficient and the spatial flow correction
remain separate in every differentiated forcing. -/
@[expose] public section
noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance
/-- Positive-order spatial words annihilate a spatial constant. -/
axiom iterateSpatialWord_const (c : ℝ) (w : List (Fin 2)) :
    iterateSpatialWord w (fun _ : Vec 2 => c) =
      fun _ => if w = [] then c else 0

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.va020beca40d2.AVenhance.Infra.Section4.CoarseCoeff.SpatialWords ====
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
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance
/-- A spatially constant factor commutes with every ordered derivative. -/
axiom iterateSpatialWord_const_mul {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ) (w : List (Fin 2)) :
    iterateSpatialWord w (fun x => c * f x) = fun x => c * iterateSpatialWord w f x
axiom coarseCoeff_word_add {f g : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (w : List (Fin 2)) :
    iterateSpatialWord w (fun x => f x + g x) =
      fun x => iterateSpatialWord w f x + iterateSpatialWord w g x

end AVenhance.Infra.Section4

end
end
end

-- ==== Examples.scottnarmstrong__AVAnomalousDiffusion.Examples.Example_7c7fcf0e14eb11542af9_WordBounds ====
-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance
/-- Every ordered split is retained, including repetitions. The only added
factor is the undifferentiated identity in the right Jacobian F = (F-I)+I. -/
def coarseCoeffWordBudget (K κ : ℝ) (F : ℕ → ℝ) (w : List (Fin 2)) : ℝ :=
  2 * K * F w.length + 4 * (K + |κ|) *
    ((iterateSpatialSplits w).map (fun p =>
      F p.1.length * (F p.2.length + if p.2 = [] then 1 else 0))).sum
axiom WordBounds.list_abs_sum_bound {α : Type*} (L : List α) (f g : α → ℝ)
    (h : ∀ a ∈ L, |f a| ≤ g a) : |(L.map f).sum| ≤ (L.map g).sum
axiom coarseCoeff_constant_matrix_word {D : Vec 2 → CoarseMatrix}
    (hD : ContDiff ℝ (⊤ : ℕ∞) D) (K : CoarseMatrix) (w : List (Fin 2))
    (x : Vec 2) (i j : Fin 2) :
    iterateSpatialWord w (fun y => (K * D y) i j) x =
      ∑ p : Fin 2, K i p * iterateSpatialWord w (fun y => D y p j) x
/-- The quadratic term is an explicit Leibniz expansion of two flow factors. -/
axiom coarseCoeff_quadratic_word {D F : Vec 2 → CoarseMatrix}
    (hD : ContDiff ℝ (⊤ : ℕ∞) D) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (C : CoarseMatrix) (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    iterateSpatialWord w (fun y => ((D y).transpose * C * F y) i j) x =
      ∑ q : Fin 2, ∑ p : Fin 2, C p q *
        ((iterateSpatialSplits w).map (fun r =>
          iterateSpatialWord r.1 (fun y => D y p i) x *
          iterateSpatialWord r.2 (fun y => F y q j) x)).sum
/-- Quantitative jets of the polynomial use only actual flow jets, at all
suborders in the ordered Leibniz rule. No coefficient jet is assumed. -/
theorem coarseCoeffPolynomial_word_entry_bound {F : Vec 2 → CoarseMatrix}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {K : CoarseMatrix} {k a b κ : ℝ} {B : ℕ → ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hB : ∀ n, 0 ≤ B n)
    (hK : ∀ i j, |K i j| ≤ k)
    (hjets : ∀ w : List (Fin 2), ∀ x i j,
      |iterateSpatialWord w (fun y => (F y - 1) i j) x| ≤ B w.length)
    (w : List (Fin 2)) (x : Vec 2) (i j : Fin 2) :
    |iterateSpatialWord w (fun y => coarseCoeffPolynomial a b κ K (F y) i j) x| ≤
      coarseCoeffWordBudget k κ B w := by
  let D : Vec 2 → CoarseMatrix := fun y => F y - 1
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := hF.sub contDiff_const
  have hk : 0 ≤ k := (abs_nonneg _).trans (hK 0 0)
  have hjfull (v : List (Fin 2)) (p q : Fin 2) :
      |iterateSpatialWord v (fun y => F y p q) x| ≤ B v.length + if v = [] then 1 else 0 := by
    have he : (fun y => F y p q) = fun y => D y p q + (1 : CoarseMatrix) p q := by
      funext y
      simp only [D, Matrix.sub_apply, sub_add_cancel]
    rw [he, coarseCoeff_word_add (contDiff_pi.1 (contDiff_pi.1 hD p) q) contDiff_const,
      iterateSpatialWord_const]
    have ht := abs_add_le (iterateSpatialWord v (fun y => D y p q) x)
      (if v = [] then (1 : CoarseMatrix) p q else 0)
    apply ht.trans
    apply add_le_add (hjets v x p q)
    classical
    by_cases hv : v = [] <;> by_cases hpq : p = q <;> simp [hv, hpq, Matrix.one_apply]
  let Q := ((iterateSpatialSplits w).map (fun r =>
    B r.1.length * (B r.2.length + if r.2 = [] then 1 else 0))).sum
  have hprod (p q : Fin 2) :
      |((iterateSpatialSplits w).map (fun r =>
        iterateSpatialWord r.1 (fun y => D y p i) x *
        iterateSpatialWord r.2 (fun y => F y q j) x)).sum| ≤ Q := by
    apply WordBounds.list_abs_sum_bound
    intro r _
    rw [abs_mul]
    exact mul_le_mul (hjets r.1 x p i) (hjfull r.2 q j) (abs_nonneg _) (hB _)
  have hμ (p q : Fin 2) : |(κ • (1 : CoarseMatrix)) p q| ≤ |κ| := by
    classical
    by_cases hpq : p = q <;> simp [Matrix.smul_apply, hpq]
  have hKm (p q : Fin 2) : |(K - κ • (1 : CoarseMatrix)) p q| ≤ k + |κ| := by
    have ht := abs_sub_le (K p q) 0 ((κ • (1 : CoarseMatrix)) p q)
    simp only [sub_zero, zero_sub, abs_neg] at ht
    exact ht.trans (add_le_add (hK p q) (hμ p q))
  have hlin : |iterateSpatialWord w (fun y => (K * D y) i j) x| ≤ 2 * k * B w.length := by
    rw [coarseCoeff_constant_matrix_word hD]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _p : Fin 2, k * B w.length := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hK i p) (hjets w x p j) (abs_nonneg _) hk
      _ = _ := by simp; ring
  have hquad : |iterateSpatialWord w (fun y =>
      ((D y).transpose * (K - κ • (1 : CoarseMatrix)) * F y) i j) x| ≤ 4 * (k + |κ|) * Q := by
    rw [coarseCoeff_quadratic_word hD hF]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _q : Fin 2, ∑ _p : Fin 2, (k + |κ|) * Q := by
        apply Finset.sum_le_sum
        intro q _
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        exact mul_le_mul (hKm p q) (hprod p q) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have hls : ContDiff ℝ (⊤ : ℕ∞) (fun y => (K * D y) i j) :=
    contDiff_pi.1 (contDiff_pi.1 (coarseCoeff_matrix_mul_contDiff contDiff_const hD) i) j
  have hqs : ContDiff ℝ (⊤ : ℕ∞) (fun y => ((D y).transpose * (K - κ • (1 : CoarseMatrix)) * F y) i j) := by
    have hDt : ContDiff ℝ (⊤ : ℕ∞) (fun y => (D y).transpose) :=
      contDiff_pi.2 fun p => contDiff_pi.2 fun q => contDiff_pi.1 (contDiff_pi.1 hD q) p
    exact contDiff_pi.1 (contDiff_pi.1 (coarseCoeff_matrix_mul_contDiff
      (coarseCoeff_matrix_mul_contDiff hDt contDiff_const) hF) i) j
  have htranspose (y : Vec 2) : (F y).transpose - 1 = (D y).transpose := by
    ext p q
    simp [D, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply, eq_comm]
  simp only [coarseCoeffPolynomial, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, htranspose]
  change |iterateSpatialWord w (fun y => a * (K * D y) i j +
    b * ((D y).transpose * (K - κ • (1 : CoarseMatrix)) * F y) i j) x| ≤ _
  rw [coarseCoeff_word_add (contDiff_const.mul hls) (contDiff_const.mul hqs),
    iterateSpatialWord_const_mul hls, iterateSpatialWord_const_mul hqs]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add
      (by simpa only [one_mul] using mul_le_mul ha hlin (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))
      (by simpa only [one_mul] using mul_le_mul hb hquad (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)))
end AVenhance.Infra.Section4
