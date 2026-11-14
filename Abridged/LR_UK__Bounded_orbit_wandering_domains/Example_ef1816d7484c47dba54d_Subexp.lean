module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Real.Sqrt

-- ==== Examples.LR_UK__Bounded_orbit_wandering_domains.Examples.Example_ef1816d7484c47dba54d_Subexp ====
/-!
## Sequences that grow subexponentially

These are common in power series, so we write some `fun_prop` support for fun.
-/
open Asymptotics
open Filter (atTop)
/-!
### Definition
-/
variable {X : Type} [Norm X]
variable {E : Type} [NormedAddCommGroup E]
variable {R : Type} [NormedRing R]
/-- A function `ℕ → X` is subexponential if it is `O(a ^ n)` for all `1 < a` -/
@[fun_prop] public structure Subexp (f : ℕ → X) : Prop where
  subexp : ∀ {a : ℝ}, 1 < a → f =O[atTop] fun n ↦ a ^ n

/-!
### For now, we only prove that polynomials are subexponential
-/

set_option linter.unusedVariables false in
axiom _root_.Subexp.norm : ∀ {E : Type} [inst : NormedAddCommGroup E] {f : ℕ → E}, Subexp f → Subexp fun (n : ℕ) ↦ ‖f n‖

/-!
### Summability involving subexponential sequences
-/
/-- A subexponential times a decreasing exponential is bounded by a decreasing exponential -/
public lemma Subexp.le_exp {f : ℕ → E} (fs : Subexp f) (a : ℝ) (a0 : 0 ≤ a) (a1 : a < 1) :
    ∃ C, ∃ b, 0 < b ∧ b < 1 ∧ ∀ n, ‖f n‖ * a ^ n ≤ C * b ^ n := by
  by_cases az : a = 0
  · refine ⟨‖f 0‖, 1 / 2, by norm_num, by norm_num, ?_⟩
    intro n
    match n with
    | 0 => simp
    | n + 1 => simp [az]
  replace a0 : 0 < a := by positivity
  have s0 : 0 < Real.sqrt a := by positivity
  have s1 : Real.sqrt a < 1 := by rwa [Real.sqrt_lt a0.le (by norm_num), one_pow]
  set b := (Real.sqrt a)⁻¹
  have b1 : 1 < b := by simpa only [b, one_lt_inv₀ s0]
  have b0 : 0 < b := by positivity
  have o := (fs.norm.subexp b1).mul (isBigO_refl (fun n : ℕ ↦ a ^ n) atTop)
  rw [Asymptotics.isBigO_nat_atTop_iff] at o
  · obtain ⟨C,le⟩ := o
    refine ⟨C, b * a, by bound, ?_, ?_⟩
    · rw [← Real.sq_sqrt a0.le]
      simpa only [b, pow_two, ← mul_assoc, inv_mul_cancel₀ s0.ne', one_mul]
    · intro n
      simpa [abs_of_pos a0, abs_of_pos b0, ← mul_pow] using le n
  · intro n z
    contrapose z
    positivity

