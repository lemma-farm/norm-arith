module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Tactic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Int.Interval
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Analysis.SpecificLimits.Basic

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Site ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The integer lattice and its nearest-neighbour averaging operator

Sites in dimension `d` are functions `Fin d → ℤ`; the walk operator averages over
the `2d` signed coordinate directions. -/
@[expose] public section
namespace LatticeProb
/-- A site of the lattice `ℤ^d`. -/
abbrev Site (d : ℕ) : Type := Fin d → ℤ
/-- The unit vector in direction `i`. -/
def unit {d : ℕ} (i : Fin d) : Site d := Pi.single i 1
/-- The sum of `u` over the neighbours of `x`, direction by direction. -/
def nbrSum {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  ∑ i : Fin d, (u (x + unit i) + u (x - unit i))
/-- The simple random walk operator `(P u)(x) = (1/2d) ∑_{y ∼ x} u(y)`. -/
noncomputable def walkOp {d : ℕ} (u : Site d → ℝ) (x : Site d) : ℝ :=
  nbrSum u x / (2 * d)
end LatticeProb
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.SRW ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # The simple random walk kernel and its parity constraint

Iterating the nearest-neighbour averaging operator from the unit atom at the origin
gives a kernel supported inside the graph-distance ball and on the parity class of time. -/
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace LatticeProb
open Finset
variable {d : ℕ}
/-! ### The `ℓ¹` norm of a site -/
/-- The graph distance from the origin: the `ℓ¹` norm of a site. -/
def graphNorm {d : ℕ} (x : Site d) : ℕ := ∑ i, (x i).natAbs
noncomputable def srwHeat (d : ℕ) : ℕ → Site d → ℝ
  | 0 => fun x => if x = 0 then 1 else 0
  | j + 1 => fun x => walkOp (srwHeat d j) x
end LatticeProb
namespace LatticeProb
open Finset
/-! ### The one-dimensional nearest-neighbour recursion -/
end LatticeProb
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.veeda06194843.Critical2DKPZ.RandomWalk.Port.Walk.GaussianFourier ====
public section
/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Gaussian Fourier integrals

The complex Gaussian integral along any horizontal line equals the Gaussian density
at the integer frequency times `2π`. -/
@[expose] public section
open MeasureTheory
noncomputable section
namespace LatticeProb.ContinuousTime
/-- The Gaussian kernel of variance `s` at an integer, `(2πs)^{-1/2} e^{-k²/(2s)}`. -/
def lineGauss (s : ℝ) (k : ℤ) : ℝ :=
  (Real.sqrt (2 * Real.pi * s))⁻¹ * Real.exp (-(k : ℝ) ^ 2 / (2 * s))
def ctGauss (d : ℕ) (t : ℝ) (x : Site d) : ℝ := ∏ i, lineGauss (t / d) (x i)
end LatticeProb.ContinuousTime
end

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_fd3760b35d9d4aafb145_PairBlockIncrementProfile ====
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
/-! # Local central limit estimates for pair-block increments -/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter
set_option linter.unusedVariables false in
private theorem srwHeat_one_return_scaled_error (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ n : ℕ, 1 ≤ n → ∀ x : LatticeProb.Site 1,
      ((LatticeProb.graphNorm x : ℕ) : ZMod 2) = ((n : ℕ) : ZMod 2) →
        |Real.sqrt (n : ℝ) * LatticeProb.srwHeat 1 n x -
          Real.sqrt (n : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1 (n : ℝ) x|
          ≤ C / (n : ℝ))
    (m : ℕ) (hm : 1 ≤ m) 
    (h_LatticeProb_graphNorm_one : ∀ (a : ℤ), LatticeProb.graphNorm ![a] = a.natAbs)
    :
    |Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] -
      Real.sqrt (m : ℝ) * 2 *
        LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![(0 : ℤ)]| ≤ C / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hroot2 : Real.sqrt (2 * (m : ℝ)) = Real.sqrt 2 * Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hroot2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hq : (Real.sqrt 2)⁻¹ ≤ 1 := by
    have hroot2ge : 1 ≤ Real.sqrt 2 := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by norm_num)
    exact (inv_le_one₀ hroot2pos).2 hroot2ge
  have h0par :
      ((LatticeProb.graphNorm (![0] : LatticeProb.Site 1) : ℕ) : ZMod 2) =
        (((2 * m : ℕ) : ℕ) : ZMod 2) := by
    rw [h_LatticeProb_graphNorm_one]
    simp only [Int.natAbs_zero, Nat.cast_zero]
    rw [Nat.cast_mul]
    have hcast2 : (↑(2 : ℕ) : ZMod 2) = 0 := by decide
    rw [hcast2]
    simp
  have hlarge := hlocal (2 * m) (by omega) ![0] h0par
  have hscaleWalk :
      Real.sqrt (m : ℝ) * LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] =
        (Real.sqrt 2)⁻¹ *
          (Real.sqrt (2 * (m : ℝ)) * LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)]) := by
    rw [hroot2]
    field_simp [hroot2pos.ne']
  have hscaleGauss :
      Real.sqrt (m : ℝ) * 2 * LatticeProb.ContinuousTime.ctGauss 1
          (2 * (m : ℝ)) ![(0 : ℤ)] =
        (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * (m : ℝ)) * 2 *
          LatticeProb.ContinuousTime.ctGauss 1
            (2 * (m : ℝ)) ![(0 : ℤ)]) := by
    rw [hroot2]
    field_simp [hroot2pos.ne']
  rw [hscaleWalk, hscaleGauss]
  have habs :
      |(Real.sqrt 2)⁻¹ * (Real.sqrt (2 * (m : ℝ)) *
            LatticeProb.srwHeat 1 (2 * m) ![0]) -
        (Real.sqrt 2)⁻¹ * (Real.sqrt (2 * (m : ℝ)) * 2 *
            LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0])| =
        (Real.sqrt 2)⁻¹ * |Real.sqrt (2 * (m : ℝ)) *
            LatticeProb.srwHeat 1 (2 * m) ![0] -
          Real.sqrt (2 * (m : ℝ)) * 2 *
            LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0]| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [habs]
  calc
    _ ≤ 1 * |Real.sqrt (2 * (m : ℝ)) * LatticeProb.srwHeat 1 (2 * m) ![0] -
        Real.sqrt (2 * (m : ℝ)) * 2 *
          LatticeProb.ContinuousTime.ctGauss 1 (2 * (m : ℝ)) ![0]| :=
      mul_le_mul_of_nonneg_right hq (abs_nonneg _)
    _ ≤ C / ((2 * m : ℕ) : ℝ) := by
      simpa only [one_mul, Nat.cast_mul, Nat.cast_ofNat] using hlarge
    _ ≤ C / (m : ℝ) := by
      have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
      rw [hcast]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (m : ℝ)) hmR]
      nlinarith [hC, hmR]
end Critical2DKPZ.SHF.Moments
end
