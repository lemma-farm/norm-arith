module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.vedea67ee6f55.Planarwave.Analysis.HolomorphicTimeExtension ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Gluing holomorphic time extensions

Holomorphic extensions from disks centered on the real axis agree on overlaps when
their real restrictions agree. The identity principle then glues the local Taylor
extensions into one holomorphic function on a neighborhood of the positive time axis.
-/
open Filter Set Topology
namespace Planarwave
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
def positiveTimeNeighborhood (η : ℝ) : Set ℂ :=
  ⋃ t : {t : ℝ // 0 < t}, Metric.ball (t.val : ℂ) (η * min t.val 1)

end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Dependencies.vedea67ee6f55.Planarwave.Analysis.ComplexTimeSector ====
public section
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-! # Geometry and uniqueness for complex time sectors -/
open Filter Set Topology
namespace Planarwave
noncomputable section
/-- An open sector about the positive real axis, described without choosing arguments. -/
def complexTimeSector (η : ℝ) : Set ℂ := {z | 0 < z.re ∧ |z.im| < η * z.re}

end
end Planarwave

end
end

-- ==== Examples.jvanwinden__PlanarFrontStability.Examples.Example_e3b9ad9d5aac97ce0cbd_SemigroupSector ====
/-
Copyright (c) 2026 Joris van Winden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris van Winden, OpenAI
-/
@[expose] public section
/-!
# Extending a holomorphic semigroup to a full time sector

Time subdivision gives local extensions on increasingly long truncated sectors.
Their real restrictions are the original semigroup, so the identity principle makes
them agree on overlaps. This supplies the full-sector continuation needed in the
analytic-semigroup part of the paper's Section 2.
-/
open Filter Set Topology Planarwave
namespace C0Semigroup
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E] in
set_option linter.unusedVariables false in
/-- A bound on the initial time neighborhood becomes an exponential bound on the
whole sector. The constants depend only on the initial bound, not on time. -/
theorem norm_holomorphicSectorExtension_le {η M : ℝ} (hM : 0 ≤ M)
    {g G : ℂ → (E →L[ℂ] E)}
    (hbound : ∀ z ∈ positiveTimeNeighborhood η, ‖g z‖ ≤ M)
    (hdivide : ∀ z ∈ complexTimeSector η, ∀ n : ℕ, 0 < n → z.re < n →
      G z = (g (z / (n : ℂ))) ^ n)
    {z : ℂ} (hz : z ∈ complexTimeSector η) 
    (h_Planarwave_div_real_mem_complexTimeSector : ∀ {η r : ℝ} {z : ℂ},
      z ∈ Planarwave.complexTimeSector η → 0 < r → z / (↑r : ℂ) ∈ Planarwave.complexTimeSector η)
    (h_Planarwave_mem_positiveTimeNeighborhood_of_sector : ∀ {η : ℝ} {z : ℂ},
      z ∈ Planarwave.complexTimeSector η → z.re ≤ 1 → z ∈ Planarwave.positiveTimeNeighborhood η)
    :
    ‖G z‖ ≤ Real.exp M * Real.exp (M * z.re) := by
  let n : ℕ := ⌊z.re⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hzn : z.re < n := by simpa only [n, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one z.re
  have hnle : (n : ℝ) ≤ z.re + 1 := by
    dsimp only [n]
    push_cast
    linarith [Nat.floor_le hz.1.le]
  have hzdiv : z / (n : ℂ) ∈ positiveTimeNeighborhood η := by
    apply h_Planarwave_mem_positiveTimeNeighborhood_of_sector
      (by simpa only [Complex.ofReal_natCast] using h_Planarwave_div_real_mem_complexTimeSector hz hnreal)
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re]
    exact ((div_lt_one hnreal).mpr hzn).le
  rw [hdivide z hz n hn hzn]
  calc
    ‖g (z / (n : ℂ)) ^ n‖ ≤ ‖g (z / (n : ℂ))‖ ^ n := norm_pow_le' _ hn
    _ ≤ M ^ n := pow_le_pow_left₀ (norm_nonneg _) (hbound _ hzdiv) n
    _ ≤ (Real.exp M) ^ n := pow_le_pow_left₀ hM (by linarith [Real.add_one_le_exp M]) n
    _ = Real.exp (M * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (M * (z.re + 1)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnle hM)
    _ = Real.exp M * Real.exp (M * z.re) := by rw [mul_add, Real.exp_add, mul_one, mul_comm]
omit [CompleteSpace E] in
end
end C0Semigroup
