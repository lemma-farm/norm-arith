/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.BPHZ.GaussianWickMonomial
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Low-order Wick monomials

`wickMonomial C [i] x = x i`, `wickMonomial C [i, i] x = x i ^ 2 - C i i` and
`wickMonomial C [i, i, i] x = x i ^ 3 - 3 * C i i * x i`.
-/
public section
namespace RegularityStructures
theorem involutions_fin_two : involutions (Fin 2) = {id, ![1, 0]} := by
  decide +kernel
theorem wickMonomial_pair_self {n : ℕ} (C : Fin n → Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    wickMonomial C [i, i] x = x i ^ 2 - C i i := by
  show ∑ π ∈ involutions (Fin 2), (-1) ^ (pairSet π).card *
    (matchingWeight (fun a b => C ([i, i].get a) ([i, i].get b)) π *
      ∏ c ∈ fixedSet π, x ([i, i].get c)) = x i ^ 2 - C i i
  rw [involutions_fin_two, Finset.sum_pair (by decide)]
  have h1 : pairSet (id : Fin 2 → Fin 2) = ∅ := by
    ext c; simp [pairSet]
  have h2 : pairSet (![1, 0] : Fin 2 → Fin 2) = {0} := by
    ext c; fin_cases c <;> simp [pairSet]
  have h3 : fixedSet (id : Fin 2 → Fin 2) = Finset.univ := by
    ext c; simp [fixedSet]
  have h4 : fixedSet (![1, 0] : Fin 2 → Fin 2) = ∅ := by
    ext c; fin_cases c <;> simp [fixedSet]
  simp [h1, h2, h3, h4, matchingWeight_eq_prod_pairSet, Fin.prod_univ_two, sq]
  ring
end RegularityStructures
end
