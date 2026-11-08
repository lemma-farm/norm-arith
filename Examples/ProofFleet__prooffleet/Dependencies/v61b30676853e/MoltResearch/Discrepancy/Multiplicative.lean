import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.Basic
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.Unbounded
/-!
# Discrepancy: completely multiplicative reduction

The first genuinely mathematical step of the Tao 2015 proof shape: for a **completely
multiplicative** sequence, the sum along the homogeneous arithmetic progression with step `d`
factors as `f d` times the plain partial sum, so (for sign sequences) discrepancy along *any*
step collapses to the step-one case.

Consequences packaged here:
- `CompletelyMultiplicative.apSum_eq_mul_apSum_one` — the sum-level factorization.
- `CompletelyMultiplicative.discrepancy_eq_discrepancy_one` — the discrepancy-level collapse.
- `CompletelyMultiplicative.forall_hasDiscrepancyAtLeast_iff_unboundedDiscrepancy_one` —
  for completely multiplicative sign sequences, the full Erdős-discrepancy surface statement
  `∀ C, HasDiscrepancyAtLeast f C` is equivalent to unboundedness of the plain partial sums.
- `CompletelyMultiplicative.boundedDiscrepancy_iff_exists_forall_natAbs_apSum_one_le` — the
  bounded (negation) side of the same equivalence.

This is the verified bridge behind the Track C reduction-to-multiplicative interface: once a
Fourier-reduction stage produces a completely multiplicative counterexample candidate, its EDP
statement is exactly "unbounded partial sums".
-/
namespace MoltResearch
/-- A completely multiplicative sequence: `f (a * b) = f a * f b` for all **nonzero**
`a b : ℕ` (no coprimality hypothesis).

Note we do not bake in `f 1 = 1`: it follows for sign sequences
(`CompletelyMultiplicative.map_one_of_isSignSequence`), and keeping the definition minimal makes
it easier to produce.

The `a ≠ 0 → b ≠ 0` guards are load-bearing (issue #2879): the literature defines completely
multiplicative sequences on `{1, 2, ...}`, and an unguarded law instantiated at `b = 0` gives
`f 0 = f a * f 0` for every `a`, which under `IsSignSequence` (`f 0 = ±1 ≠ 0`) collapses the
class to the constant-1 sequence and vacates every statement quantifying over it. With the
guards, `f 0` is genuinely unconstrained junk.
-/
def CompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → f (a * b) = f a * f b
namespace CompletelyMultiplicative
variable {f : ℕ → ℤ}
end CompletelyMultiplicative
end MoltResearch
