/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.Basic.Inner
public import Examples.shaikidris__kkp_localized_spectral_bound.Dependencies.v18aabc3b06ea.BN.CP.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Order.Compact
@[expose] public section
/-!
# Motzkin–Straus

The Motzkin–Straus theorem bounds the adjacency quadratic form on the
nonnegative orthant by the Turán factor `1 - 1/ω(G)`, and the same bound
passes to the Frobenius pairing against a completely positive matrix.
-/
namespace BN
open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
/-! ### MS05 — Cauchy–Schwarz on a block of size `k` -/
variable {G : SimpleGraph V} [DecidableRel G.Adj]
/-! ### MS01 — quadratic form as an edge sum -/
lemma inner_sum {ι : Type*} (s : Finset ι) (B : Matrix V V ℝ)
    (C : ι → Matrix V V ℝ) :
    inner B (∑ a ∈ s, C a) = ∑ a ∈ s, inner B (C a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inner]
  | insert a s ha ih => simp [Finset.sum_insert ha, inner_add_right, ih]
omit [DecidableEq V] in
lemma inner_one_vecMulVec (p : V → ℝ) :
    inner (of fun _ _ => (1 : ℝ)) (vecMulVec p p) = (∑ i, p i) ^ 2 := by
  rw [inner_eq_sum]
  simp only [of_apply, vecMulVec_apply]
  simp_rw [one_mul]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, pow_two]
end BN
