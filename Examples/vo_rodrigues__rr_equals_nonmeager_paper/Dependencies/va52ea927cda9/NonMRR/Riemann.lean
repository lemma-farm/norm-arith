/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic
set_option autoImplicit false
set_option warningAsError true
open Filter Finset Set Topology
open scoped BigOperators Classical
namespace NonMRR
/-- A real family with bounded sums on all finite subsets is absolutely summable. -/
theorem summable_abs_of_bounded_finite_sums (a : ℕ → ℝ) (c : ℝ)
    (h : ∀ s : Finset ℕ, |∑ i ∈ s, a i| ≤ c) : Summable (fun i => |a i|) := by
  have hpos (b : ℕ → ℝ) (hb : ∀ s : Finset ℕ, |∑ i ∈ s, b i| ≤ c) :
      Summable (fun i => max (b i) 0) := by
    apply summable_of_sum_le (fun _ => le_max_right _ _) (c := c)
    intro s
    have heq : ∑ i ∈ s, max (b i) 0 = ∑ i ∈ s.filter (fun i => 0 ≤ b i), b i := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i _hi
      split_ifs with hi
      · exact max_eq_left hi
      · exact max_eq_right (le_of_not_ge hi)
    change (∑ i ∈ s, max (b i) 0) ≤ c
    rw [heq]
    exact (le_abs_self _).trans (hb _)
  have hp := hpos a h
  have hn := hpos (fun i => -a i) (fun s => by simpa using h s)
  convert hp.add hn using 1
  ext i
  by_cases hi : 0 ≤ a i
  · simp [abs_of_nonneg hi, max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]
  · have hi' : a i ≤ 0 := le_of_not_ge hi
    simp [abs_of_nonpos hi', max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]
end NonMRR
