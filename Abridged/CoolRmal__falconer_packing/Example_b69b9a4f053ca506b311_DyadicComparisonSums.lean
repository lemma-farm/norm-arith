module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Data.Finset.Pi
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.WithDensityFinite
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous
public import Mathlib.Probability.Kernel.Composition.Lemmas
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
public import Mathlib.Probability.Kernel.RadonNikodym
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Analysis.MeanInequalities

-- ==== Examples.CoolRmal__falconer_packing.Dependencies.vf40134ef9295.FalconerPacking.Dyadic ====
public section
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-!
# Dyadic cubes in the plane

Module 4 of the implementation ledger, first half: the geometric cube hierarchy used by the
conditional measures of the manuscript.  A dyadic square of generation `n` is a product of
half-open coordinate intervals of side `2⁻ⁿ`, indexed by integers.

* `mem_dyadicCube_iff` — membership is exactly the statement that the index is the floor index,
  so the generation-`n` cubes partition the plane;
* `dyadicCube_disjoint` — distinct cubes of one generation are disjoint;
* `dyadicCube_succ_subset` — each cube is contained in its parent, whose index is `k / 2`;
* `dist_le_of_mem_dyadicCube` — a generation-`n` cube has diameter at most `√2 / 2ⁿ`;
* `measurableSet_dyadicCube` — cubes are Borel.

This is the geometric hierarchy, not `Data.Dyadic`, which is an arithmetic number type.
-/
@[expose] public section
noncomputable section
open Set
namespace FalconerPacking
/-- The dyadic square of generation `n` with integer index `k`, half-open in each coordinate. -/
def dyadicCube (n : ℕ) (k : Fin 2 → ℤ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | ∀ i, (k i : ℝ) ≤ 2 ^ n * x i ∧ 2 ^ n * x i < (k i : ℝ) + 1}

section Counting

end Counting
section Ancestors

end Ancestors
end FalconerPacking

end
end
end

-- ==== Examples.CoolRmal__falconer_packing.Examples.Example_b69b9a4f053ca506b311_DyadicComparisonSums ====
/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
set_option autoImplicit false
/-!
# Summing comparisons over children of dyadic cubes

Disjointness bounds the total child mass in a parent. Regrouping then controls the parent
moment terms, while Hölder bounds the sum of square roots of the child masses.
-/
@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace FalconerPacking


set_option linter.unusedVariables false in
/-- Square-root masses of a finite subfamily are bounded by the square root of its size. -/
theorem sum_sqrt_dyadic_mass_le
    (μ : Measure (EuclideanSpace ℝ (Fin 2))) [IsProbabilityMeasure μ]
    (n : ℕ) (I : Finset (Fin 2 → ℤ)) 
    (h_FalconerPacking_measurableSet_dyadicCube : ∀ (n : ℕ) (k : Fin 2 → ℤ), MeasurableSet (FalconerPacking.dyadicCube n k))
    (h_FalconerPacking_dyadicCube_disjoint : ∀ {n : ℕ} {k k' : Fin 2 → ℤ},
      k ≠ k' → Disjoint (FalconerPacking.dyadicCube n k) (FalconerPacking.dyadicCube n k'))
    :
    ∑ k ∈ I, μ (dyadicCube n k) ^ (1 / 2 : ℝ) ≤
      (I.card : ℝ≥0∞) ^ (1 / 2 : ℝ) := by
  have hmass : ∑ k ∈ I, μ (dyadicCube n k) ≤ 1 := by
    simpa using sum_measure_le_measure_univ
      (fun k _ ↦ (h_FalconerPacking_measurableSet_dyadicCube n k).nullMeasurableSet)
      (fun _ _ _ _ hne ↦ (h_FalconerPacking_dyadicCube_disjoint hne).aedisjoint (μ := μ))
  have h := ENNReal.inner_le_Lp_mul_Lq I
    (fun k ↦ μ (dyadicCube n k) ^ (1 / 2 : ℝ)) (fun _ ↦ 1)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
  simp only [mul_one, ← ENNReal.rpow_mul,
    show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  apply h.trans
  have hp := ENNReal.rpow_le_rpow hmass (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [ENNReal.one_rpow, one_mul] using
    mul_le_mul_left hp ((I.card : ℝ≥0∞) ^ (1 / 2 : ℝ))
end FalconerPacking
