/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedTerminal
public import Examples.jtraverso__typed_triangle_absorption.Dependencies.v61054f52694a.PartitionedTriangleAbsorption.BlowupB.StructuralF3General.PrivateFamily
/-! # The terminal placement step in an extendible host

Vertices of ledger degree above T form the external exclusion set.  The
handshake bound gives at most a/2 such vertices when 4|L| <= T*a.  A bounded
template is therefore embeddable whenever S+S*D < a/2.  Roots remain fixed
even when their ledger degree exceeds T.
-/
@[expose] public section
namespace PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
open Finset AntiEdgeSelection TypedTransformer
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem sum_incidentLoad_le (E : Finset (Sym2 V)) : ∑ v, incidentLoad E v ≤ 2 * E.card := by
  have hswap : ∑ v, incidentLoad E v = ∑ e ∈ E, (univ.filter fun v => v ∈ e).card := by
    simp only [incidentLoad, card_filter]
    exact sum_comm
  rw [hswap]
  calc ∑ e ∈ E, (univ.filter fun v => v ∈ e).card ≤ ∑ _e ∈ E, 2 := by
        refine sum_le_sum fun e _ => ?_
        induction e using Sym2.ind with
        | _ a b =>
          calc (univ.filter fun v => v ∈ s(a, b)).card ≤ ({a, b} : Finset V).card :=
                card_le_card fun v hv => by simpa using hv
            _ ≤ 2 := card_le_two
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]
theorem card_highLoad_le (E : Finset (Sym2 V)) (T : ℝ) :
    ((univ.filter fun v => T < incidentLoad E v).card : ℝ) * T ≤ 2 * E.card := by
  set H := univ.filter fun v => T < (incidentLoad E v : ℝ)
  have h1 : (H.card : ℝ) * T ≤ ∑ v ∈ H, (incidentLoad E v : ℝ) := by
    rw [← nsmul_eq_mul]
    exact card_nsmul_le_sum H _ T fun v hv => (mem_filter.mp hv).2.le
  have h2 : ∑ v ∈ H, (incidentLoad E v : ℝ) ≤ ∑ v, (incidentLoad E v : ℝ) :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => Nat.cast_nonneg _
  have h3 : ∑ v, (incidentLoad E v : ℝ) ≤ 2 * E.card := by
    exact_mod_cast sum_incidentLoad_le E
  linarith
end PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily
