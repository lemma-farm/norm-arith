module
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.ChenExplicit.Statements
/-!
AI-written Lean code, Claude, 2026-10-16, run 20261016T1803Z-2621.
Proved links between the explicit Chen statements. Nothing here proves Chen's theorem itself:
the analytic inputs `Yamada`, `BJS3`, `BJS4` stay hypotheses.
-/
@[expose] public section
open Finset
open scoped ArithmeticFunction.Omega ArithmeticFunction.omega
noncomputable section
namespace LeanLab.ChenExplicit
/-- `1 / (n - 1)²` is summable over `ℕ`. -/
lemma summable_inv_sub_one_sq : Summable (fun n : ℕ => 1 / ((n : ℝ) - 1) ^ 2) := by
  rw [← summable_nat_add_iff 2]
  have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine this.congr fun n => ?_
  push_cast; ring_nf
theorem twinC_multipliable :
    Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => 1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hs : Summable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => -(1 / ((p : ℝ) - 1) ^ 2)) :=
    (summable_inv_sub_one_sq.subtype _).neg
  exact (Real.multipliable_one_add_of_summable hs).congr fun p => by ring
end LeanLab.ChenExplicit
