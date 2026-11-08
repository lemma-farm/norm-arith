import Examples.ProofFleet__prooffleet.Dependencies.v08927546f6f6.MoltResearch.Discrepancy.Reindex
/-!
# Discrepancy: bounded vs unbounded (quantifier normal forms)

This file packages the common “unbounded discrepancy” statement

`∀ C, HasDiscrepancyAtLeast f C`

as the negation of a single boundedness predicate.

These lemmas are logically elementary, but they are high‑leverage glue for composing
conjecture stubs (e.g. routing a paper theorem stated as “not bounded” into our nucleus
predicate `HasDiscrepancyAtLeast`).
-/
namespace MoltResearch
/-- `f` has *bounded discrepancy* if there is a uniform bound on all homogeneous AP partial sums.

This is the natural negation‑normal form of the Erdős discrepancy statement.
-/
def BoundedDiscrepancy (f : ℕ → ℤ) : Prop :=
  ∃ B : ℕ, ∀ d n : ℕ, d > 0 → Int.natAbs (apSum f d n) ≤ B
theorem BoundedDiscrepancy.map_mul {f : ℕ → ℤ} (hb : BoundedDiscrepancy f) {k : ℕ} (hk : k > 0) :
    BoundedDiscrepancy (fun n => f (n * k)) := by
  rcases hb with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  intro d n hd
  -- `apSum (fun n => f (n*k)) d n = apSum f (d*k) n`.
  simpa [apSum_map_mul] using hB (d * k) n (Nat.mul_pos hd hk)
end MoltResearch
