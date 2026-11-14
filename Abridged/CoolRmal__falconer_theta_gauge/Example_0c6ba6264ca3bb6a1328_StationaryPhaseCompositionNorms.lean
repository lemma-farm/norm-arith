module

public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7522a8ccdfa5.FalconerThetaGauge.StationaryPartitionCycles ====
public section
set_option autoImplicit false
/-! # The exact factorial sum of cyclic weights of the Faà di Bruno partitions -/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge
def stationaryPartitionCycleWeight {n : ℕ} (c : OrderedFinpartition n) : ℕ :=
  ∏ i, (c.partSize i - 1).factorial

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7522a8ccdfa5.FalconerThetaGauge.StationaryMorseAngle ====
public section
set_option autoImplicit false
/-!
# The literal Morse coordinate for circular stationary phase
-/
@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace FalconerThetaGauge
def stationaryMorseAngle (s : ℝ) : ℝ := 2 * Real.arcsin (s / 2)

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Dependencies.v7522a8ccdfa5.FalconerThetaGauge.StationaryPhaseOperators ====
public section
/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
set_option autoImplicit false
/-!
# Exact constant coefficients for the circular Morse coordinate

The coefficients are finite sums of the actual derivatives of the literal Morse angle and
Jacobian. Ordered finite partitions supply the composition coefficients; Leibniz supplies
the Jacobian factor. They are independent of the amplitude and the stationary point.
-/
@[expose] public section
noncomputable section
open Finset Set
open scoped ContDiff Topology
namespace FalconerThetaGauge
/-- The coefficient of the `k`th derivative in the `m`th derivative of a composition. -/
def stationaryCompositionCoefficient (m k : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition m,
    if c.length = k then ∏ r, iteratedDeriv (c.partSize r) stationaryMorseAngle 0 else 0

end FalconerThetaGauge

end
end
end

-- ==== Examples.CoolRmal__falconer_theta_gauge.Examples.Example_0c6ba6264ca3bb6a1328_StationaryPhaseCompositionNorms ====
set_option autoImplicit false
/-! # Actual weighted coefficient sums for the circular Morse composition -/
@[expose] public section
noncomputable section
open Finset
namespace FalconerThetaGauge

def stationaryCompositionWeightedNorm (m n : ℕ) (M : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), ‖stationaryCompositionCoefficient m k‖ * M ^ k
set_option linter.unusedVariables false in
/-- The literal real composition coefficients have an analytic factorial bound. -/
theorem stationaryCompositionWeightedNorm_le {m n : ℕ} (hmn : m ≤ n)
    {M : ℝ} (hM : 1 ≤ M) 
    (h_FalconerThetaGauge_sum_stationaryPartitionCycleWeight_eq : ∀ (n : ℕ),
      ∑ c : OrderedFinpartition n, FalconerThetaGauge.stationaryPartitionCycleWeight c = n.factorial)
    (h_FalconerThetaGauge_norm_iteratedDeriv_stationaryMorseAngle_cycle_le : ∀ (m : ℕ),
      0 < m →
        ∀ {s : ℝ},
          |s| ≤ 1 →
            ‖iteratedDeriv m FalconerThetaGauge.stationaryMorseAngle s‖ ≤
              2 ^ m * (↑(m - 1).factorial : ℝ))
    (h_FalconerThetaGauge_orderedFinpartition_sum_partSize : ∀ {n : ℕ} (c : OrderedFinpartition n), ∑ i : Fin c.length, c.partSize i = n)
    :
    stationaryCompositionWeightedNorm m n M ≤ (2 * M) ^ m * (m.factorial : ℝ) := by
  classical
  have hM0 : 0 ≤ M := by linarith
  have hterm (c : OrderedFinpartition m) :
      (∏ r, ‖iteratedDeriv (c.partSize r) stationaryMorseAngle 0‖) * M ^ c.length ≤
        (2 * M) ^ m * (stationaryPartitionCycleWeight c : ℝ) := by
    have hp : (∏ r, ‖iteratedDeriv (c.partSize r) stationaryMorseAngle 0‖) ≤
        2 ^ m * ∏ r, ((c.partSize r - 1).factorial : ℝ) := by
      calc
        _ ≤ ∏ r, 2 ^ c.partSize r * ((c.partSize r - 1).factorial : ℝ) := by
          apply prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
          intro r _
          exact h_FalconerThetaGauge_norm_iteratedDeriv_stationaryMorseAngle_cycle_le _ (c.partSize_pos r)
            (by norm_num)
        _ = _ := by
          rw [prod_mul_distrib, prod_pow_eq_pow_sum, h_FalconerThetaGauge_orderedFinpartition_sum_partSize]
    calc
      _ ≤ (2 ^ m * ∏ r, ((c.partSize r - 1).factorial : ℝ)) * M ^ c.length :=
        mul_le_mul_of_nonneg_right hp (pow_nonneg hM0 _)
      _ ≤ (2 ^ m * ∏ r, ((c.partSize r - 1).factorial : ℝ)) * M ^ m := by
        gcongr
        exact c.length_le
      _ = _ := by simp only [stationaryPartitionCycleWeight, Nat.cast_prod, mul_pow]; ring
  unfold stationaryCompositionWeightedNorm
  calc
    _ ≤ ∑ k ∈ range (n + 1),
        (∑ c : OrderedFinpartition m,
          ‖if c.length = k then ∏ r, iteratedDeriv (c.partSize r) stationaryMorseAngle 0
            else 0‖) * M ^ k := by
      apply sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hM0 _)
    _ = ∑ c : OrderedFinpartition m,
        (∏ r, ‖iteratedDeriv (c.partSize r) stationaryMorseAngle 0‖) * M ^ c.length := by
      simp_rw [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro c _
      have hc : c.length ∈ range (n + 1) := mem_range.mpr (by have := c.length_le; omega)
      rw [sum_eq_single_of_mem c.length hc]
      · simp only [ite_true, norm_prod]
      · intro b _ hb
        simp [Ne.symm hb]
    _ ≤ ∑ c : OrderedFinpartition m,
        (2 * M) ^ m * (stationaryPartitionCycleWeight c : ℝ) :=
      sum_le_sum (fun c _ ↦ hterm c)
    _ = _ := by
      rw [← mul_sum, ← Nat.cast_sum, h_FalconerThetaGauge_sum_stationaryPartitionCycleWeight_eq]
end FalconerThetaGauge
