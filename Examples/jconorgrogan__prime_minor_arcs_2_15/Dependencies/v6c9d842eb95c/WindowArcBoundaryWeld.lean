import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.v6c9d842eb95c.HarmonicInterfaces
/-!
# Exact translated-window and rational-arc boundary welds

This module normalizes the public real-centered translated window all the way to
literal real inequalities.  It also records that the public major arcs are a
closed set of rational neighborhoods and that their complement is the exact
minor-arc region, so equality boundary points are assigned to the major arcs.
-/
open MeasureTheory Metric Set
namespace PrimePairEndpoints
/-- Membership in the public `ceil`/`floor` translated window is exactly the
pair of literal real inequalities.  Both inequalities are non-strict. -/
theorem mem_translatedWindow_iff_real_bounds
    {H h₀ : ℝ} {h : ℤ} :
    h ∈ translatedWindow H h₀ ↔
      h₀ - H ≤ (h : ℝ) ∧ (h : ℝ) ≤ h₀ + H := by
  simp only [translatedWindow, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
example : (-1 : ℤ) ∈ translatedWindow (1 : ℝ) 0 := by
  rw [mem_translatedWindow_iff_real_bounds]
  norm_num
example : (1 : ℤ) ∈ translatedWindow (1 : ℝ) 0 := by
  rw [mem_translatedWindow_iff_real_bounds]
  norm_num
/-- A left-open replacement loses the left endpoint. -/
example : (-1 : ℤ) ∉ Finset.Ioc (-1 : ℤ) 1 := by decide
/-- An open replacement loses both endpoints. -/
example : (-1 : ℤ) ∉ Finset.Ioo (-1 : ℤ) 1 ∧
    (1 : ℤ) ∉ Finset.Ioo (-1 : ℤ) 1 := by decide
/-- With `h₀ = 1`, `H = 1/2`, the public window contains exactly the
single integer `1` among the nearby candidates. -/
example :
    (0 : ℤ) ∉ translatedWindow ((1 : ℝ) / 2) 1 ∧
    (1 : ℤ) ∈ translatedWindow ((1 : ℝ) / 2) 1 ∧
    (2 : ℤ) ∉ translatedWindow ((1 : ℝ) / 2) 1 := by
  simp only [mem_translatedWindow_iff_real_bounds]
  norm_num
/-- Reversing the rounding directions for the same real interval would use
`Icc 0 2` and spuriously insert both outside atoms. -/
example : (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 2 ∧
    (2 : ℤ) ∈ Finset.Icc (0 : ℤ) 2 := by decide
/-- A narrow interval may contain no integer at all.  Here the correct public
window is empty at every candidate, while reversed rounding would insert two. -/
example :
    (0 : ℤ) ∉ translatedWindow ((1 : ℝ) / 4) ((1 : ℝ) / 2) ∧
    (1 : ℤ) ∉ translatedWindow ((1 : ℝ) / 4) ((1 : ℝ) / 2) ∧
    (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 1 ∧
    (1 : ℤ) ∈ Finset.Icc (0 : ℤ) 1 := by
  simp only [mem_translatedWindow_iff_real_bounds]
  norm_num
end PrimePairEndpoints
namespace RationalArcPartition
open PrimePairEndpoints
end RationalArcPartition
