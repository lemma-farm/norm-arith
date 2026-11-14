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
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Bochner.Set

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.Plane ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The plane `ℝ²`, with its Euclidean structure. -/
@[reducible] def Plane := EuclideanSpace ℝ (Fin 2)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.Site ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The square lattice `ℤ²`. -/
@[reducible] def Site := Fin 2 → ℤ
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.NearestEven ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- A nearest point `[x]` of the even lattice `{z : z₁ + z₂ ∈ 2ℤ}` (§1.1). Writing
`x = (u + v, u − v)`, the even lattice is `{(a + b, a − b) : a, b ∈ ℤ}` and
`|x − (a + b, a − b)|² = 2 ((u − a)² + (v − b)²)`; we take `a = round u`, `b = round v`
(ties broken towards `+∞`, the fixed tie-breaking rule required by the source). -/
def nearestEven (x : Plane) : Site :=
  let a := round ((x 0 + x 1) / 2)
  let b := round ((x 0 - x 1) / 2)
  ![a + b, a - b]
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.LatticePoint ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The lattice point `[√(N/2) x]` representing `x` at scale `N` (§1.1). -/
def latticePoint (N : ℕ) (x : Plane) : Site :=
  nearestEven (Real.sqrt (N / 2) • x)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.Cell ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The cell `C_N(z) = {x ∈ ℝ² : [√(N/2) x] = z}` (§1.1). -/
def cell (N : ℕ) (z : Site) : Set Plane :=
  latticePoint N ⁻¹' {z}
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.SrwStep ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- The four steps `± e₁, ± e₂` of the simple symmetric random walk on `ℤ²`. -/
def srwStep : Fin 4 → Site :=
  ![![1, 0], ![-1, 0], ![0, 1], ![0, -1]]
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.WalkPosition ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Position after `j` steps of the walk started at `w` with step sequence `s`
(for `j ≥ n` this is the endpoint). -/
def walkPosition (w : Site) {n : ℕ} (s : Fin n → Fin 4) (j : ℕ) : Site :=
  w + ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), srwStep (s i)
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.SrwKernel ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Transition probability `q_n(z) = P₀(S_n = z)` of the simple random walk. -/
def srwKernel (n : ℕ) (z : Site) : ℝ :=
  ∑ s : Fin n → Fin 4, (4 : ℝ)⁻¹ ^ n * if walkPosition 0 s n = z then 1 else 0
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.MomentBounds.CSZ25Green ====
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
/-! # Green energies and localisation in CSZ25 Section 5 -/
@[expose] public noncomputable section
namespace Critical2DKPZ.MomentBounds
/-- The truncated Green function sums the even-time transition kernel up to the given horizon. -/
def truncatedGreen (L : ℕ) (z : Site) : ℝ :=
  ∑ n ∈ Finset.Icc 1 L, srwKernel (2 * n) z
/-- The Green energy `R_L(φ, φ)`, including both parity classes. -/
def greenEnergy (L : ℕ) (φ : Site → ℝ) : ℝ :=
  ∑' z, ∑' w, φ z * truncatedGreen L (z - w) * φ w
end Critical2DKPZ.MomentBounds

end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Polymer.Endpoints ====
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
/-! At a fixed walk horizon, only finitely many endpoints contribute to the polymer kernel and its smoothed averages. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace Critical2DKPZ.Polymer
/-- The finite set of sites reachable in a given number of steps. -/
def endpoints (w : Site) (n : ℕ) : Finset Site :=
  Finset.univ.image (fun s : Fin n → Fin 4 => walkPosition w s n)

end Critical2DKPZ.Polymer

end
end
end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Dependencies.vd4a7c65e94b5.Critical2DKPZ.Definitions.HeatKernel ====
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
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped CompactlySupported Distributions BoundedContinuousFunction ENNReal Pointwise
namespace Critical2DKPZ
/-- Heat kernel `g_u(z) = (2πu)⁻¹ exp(−|z|²/(2u))` (§1.1, §1.2). -/
def heatKernel (u : ℝ) (z : Plane) : ℝ :=
  (2 * Real.pi * u)⁻¹ * Real.exp (-‖z‖ ^ 2 / (2 * u))
end Critical2DKPZ
end
end

end

-- ==== Examples.scottnarmstrong__Critical2DKPZ.Examples.Example_29604b22e3e64457c980_HeatCellProfileBounds ====
/-
Copyright 2026 Scott Armstrong. All rights reserved.
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
/-! # Mass and size of the heat-start lattice profile -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ.SHF.Positivity

set_option linter.unusedVariables false in
/-- The Green energy of a heat-cell profile is at most `L` times the cell-volume bound
`(4/N)(2πδ)⁻¹` on each cell mass. The double series is summable by
`MomentBounds.summable_greenEnergy_terms`, using `heatCellProfile_bounds`. -/
theorem greenEnergy_heatCell_le (L : ℕ) {N : ℕ} (hN : 1 ≤ N) {δ : ℝ}
    (hδ : 0 < δ) (x : Plane) 
    (h_Critical2DKPZ_SHF_Positivity_heatCellProfile_bounds : ∀ {N : ℕ},
      1 ≤ N →
        ∀ {δ : ℝ},
          0 < δ →
            ∀ (x : Critical2DKPZ.Plane),
              (∀ (w : Critical2DKPZ.Site),
                  0 ≤
                    ∫ (y : Critical2DKPZ.Plane) in Critical2DKPZ.cell N w,
                      Critical2DKPZ.heatKernel δ (y - x)) ∧
                (Summable fun (w : Critical2DKPZ.Site) ↦
                    ∫ (y : Critical2DKPZ.Plane) in Critical2DKPZ.cell N w,
                      Critical2DKPZ.heatKernel δ (y - x)) ∧
                  ∑' (w : Critical2DKPZ.Site),
                        ∫ (y : Critical2DKPZ.Plane) in Critical2DKPZ.cell N w,
                          Critical2DKPZ.heatKernel δ (y - x) =
                      1 ∧
                    ∀ (w : Critical2DKPZ.Site),
                      ∫ (y : Critical2DKPZ.Plane) in Critical2DKPZ.cell N w,
                          Critical2DKPZ.heatKernel δ (y - x) ≤
                        4 / (↑N : ℝ) * (2 * Real.pi * δ)⁻¹)
    (h_Critical2DKPZ_Polymer_srwKernel_sub_swap : ∀ (n : ℕ) (w z : Critical2DKPZ.Site),
      Critical2DKPZ.srwKernel n (w - z) = Critical2DKPZ.srwKernel n (z - w))
    (h_Critical2DKPZ_Polymer_srwKernel_eq_zero_of_not_mem : ∀ (n : ℕ) (w z : Critical2DKPZ.Site),
      z ∉ Critical2DKPZ.Polymer.endpoints w n → Critical2DKPZ.srwKernel n (z - w) = 0)
    (h_Critical2DKPZ_MomentBounds_truncatedGreen_nonneg : ∀ (L : ℕ) (z : Critical2DKPZ.Site), 0 ≤ Critical2DKPZ.MomentBounds.truncatedGreen L z)
    (h_Critical2DKPZ_Polymer_tsum_srwKernel : ∀ (n : ℕ) (w : Critical2DKPZ.Site),
      ∑' (z : Critical2DKPZ.Site), Critical2DKPZ.srwKernel n (z - w) = 1)
    :
    MomentBounds.greenEnergy L (fun w => ∫ y in cell N w, heatKernel δ (y - x)) ≤
      (L : ℝ) * ((4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) := by
  obtain ⟨hν0, hνsum, hν1, hνbound⟩ := h_Critical2DKPZ_SHF_Positivity_heatCellProfile_bounds hN hδ x
  let ν : Site → ℝ := fun w => ∫ y in cell N w, heatKernel δ (y - x)
  let C : ℝ := (4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hkernelTermSummable (z : Site) (n : ℕ) (hn : n ∈ Finset.Icc 1 L) :
      Summable (fun w : Site => srwKernel (2 * n) (z - w)) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints z (2 * n))
    intro w hw
    rw [h_Critical2DKPZ_Polymer_srwKernel_sub_swap (2 * n) z w]
    exact h_Critical2DKPZ_Polymer_srwKernel_eq_zero_of_not_mem (2 * n) z w hw
  have hkernelTerm (z : Site) (n : ℕ) :
      (∑' w : Site, srwKernel (2 * n) (z - w)) = 1 := by
      have heq : (fun w : Site => srwKernel (2 * n) (z - w)) =
          fun w => srwKernel (2 * n) (w - z) := by
        funext w
        exact h_Critical2DKPZ_Polymer_srwKernel_sub_swap (2 * n) z w
      rw [heq]
      exact h_Critical2DKPZ_Polymer_tsum_srwKernel (2 * n) z
  have hkernelSummable (z : Site) :
      Summable (fun w : Site => MomentBounds.truncatedGreen L (z - w)) := by
    apply summable_of_ne_finset_zero
      (s := (Finset.Icc 1 L).biUnion fun n => Polymer.endpoints z (2 * n))
    intro w hw
    simp only [Finset.mem_biUnion, not_exists, not_and] at hw
    simp only [MomentBounds.truncatedGreen]
    apply Finset.sum_eq_zero
    intro n hn
    have hnot : w ∉ Polymer.endpoints z (2 * n) := hw n hn
    rw [h_Critical2DKPZ_Polymer_srwKernel_sub_swap (2 * n) z w]
    exact h_Critical2DKPZ_Polymer_srwKernel_eq_zero_of_not_mem (2 * n) z w hnot
  have hkernel (z : Site) :
      (∑' w : Site, MomentBounds.truncatedGreen L (z - w)) = L := by
    have hfinite := Summable.tsum_finsetSum (fun n hn => hkernelTermSummable z n hn)
    change (∑' w : Site, ∑ n ∈ Finset.Icc 1 L, srwKernel (2 * n) (z - w)) = L
    rw [hfinite]
    simp_rw [hkernelTerm]
    simp
  have hkernel0 (z w : Site) : 0 ≤ MomentBounds.truncatedGreen L (z - w) :=
    h_Critical2DKPZ_MomentBounds_truncatedGreen_nonneg L (z - w)
  have hinner (z : Site) :
      ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w ≤ ν z * C * L := by
    have hk := hkernel z
    have hweightedNonneg (w : Site) :
        0 ≤ MomentBounds.truncatedGreen L (z - w) * ν w :=
      mul_nonneg (hkernel0 z w) (hν0 w)
    have hweightedLe (w : Site) :
        MomentBounds.truncatedGreen L (z - w) * ν w ≤
          C * MomentBounds.truncatedGreen L (z - w) := by
      calc
        MomentBounds.truncatedGreen L (z - w) * ν w ≤
            MomentBounds.truncatedGreen L (z - w) *
              ((4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) :=
          mul_le_mul_of_nonneg_left (hνbound w) (hkernel0 z w)
        _ = C * MomentBounds.truncatedGreen L (z - w) := by
          dsimp [C]
          ring
    have hweight : Summable (fun w : Site => C * MomentBounds.truncatedGreen L (z - w)) := by
      simpa only [mul_comm] using (hkernelSummable z).mul_left C
    have hweighted : Summable (fun w : Site =>
        MomentBounds.truncatedGreen L (z - w) * ν w) :=
      Summable.of_nonneg_of_le hweightedNonneg hweightedLe hweight
    have hsum : (∑' w : Site,
        MomentBounds.truncatedGreen L (z - w) * ν w) ≤ C * L := by
      have h := hweighted.tsum_le_tsum hweightedLe hweight
      have hright : (∑' w : Site,
          C * MomentBounds.truncatedGreen L (z - w)) = C * L := by
        rw [tsum_mul_left, hk]
      rw [hright] at h
      exact h
    calc
      _ = ∑' w : Site, ν z *
          (MomentBounds.truncatedGreen L (z - w) * ν w) := by
        congr 1
        funext w
        ring
      _ = ν z * ∑' w : Site,
          MomentBounds.truncatedGreen L (z - w) * ν w := by
        rw [tsum_mul_left]
      _ ≤ ν z * (C * L) := mul_le_mul_of_nonneg_left hsum (hν0 z)
      _ = ν z * C * L := by ring
  have houterNonneg (z : Site) :
      0 ≤ ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w :=
    tsum_nonneg fun w => mul_nonneg (mul_nonneg (hν0 z) (hkernel0 z w)) (hν0 w)
  have houterLe (z : Site) :
      (∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w) ≤
        ν z * (C * L) := by
    simpa only [mul_assoc] using hinner z
  have hmajorSummable : Summable (fun z : Site => ν z * (C * L)) :=
    hνsum.mul_right (C * L)
  have houterSummable : Summable (fun z : Site =>
      ∑' w : Site, ν z * MomentBounds.truncatedGreen L (z - w) * ν w) :=
    Summable.of_nonneg_of_le houterNonneg houterLe hmajorSummable
  unfold MomentBounds.greenEnergy
  calc
    _ ≤ ∑' z : Site, ν z * (C * L) := houterSummable.tsum_le_tsum houterLe hmajorSummable
    _ = C * L := by rw [tsum_mul_right, hν1, one_mul]
    _ = (L : ℝ) * ((4 / (N : ℝ)) * (2 * Real.pi * δ)⁻¹) := by
          simp only [C]
          ring
end Critical2DKPZ.SHF.Positivity
end
