import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.MultiplicativeC
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
/-!
# Discrepancy: log-uniform weights and finitary affine invariance

Track C, Elliott campaign (`Problems/tao2015_derivation_c.md`, issue #2946, E3): the
toolbox for the logarithmically averaged random variable `𝐧` of arXiv:1509.05422 §2 —
`P(𝐧 = n) ∝ 1/n` on a window `a < n ≤ b`. The log-averaging buys *approximate affine
invariance* (the paper's Lemma `linear`): restricting to a residue class `n ≡ r (q)` and
substituting `n = q·n' + r` reproduces the log-uniform weights at scale `n' = n/q`, at
the cost `1/n − 1/(q·(n/q)) = O(r/(q·(n/q))²)` per term — summable to `O(r/q²)`.

* `sum_one_div_sq_le_two` — `∑_{n ∈ S} 1/n² ≤ 2` for any finite `S ⊆ ℕ` (public
  telescoping util).
* `sum_filter_residue_eq_sum_image` — the **exact** reindexing of a residue-class sum
  along `n ↦ n/q` (zero error; the affine range bookkeeping stays with the consumer).
* `norm_sum_div_residue_sub_le` — the **weight comparison**: replacing `1/n` by
  `(1/q)·(1/(n/q))` on the residue class costs at most `2r/q²` in total, uniformly over
  `1`-bounded numerators.
-/
namespace MoltResearch
open Finset
variable {q r : ℕ}
end MoltResearch
