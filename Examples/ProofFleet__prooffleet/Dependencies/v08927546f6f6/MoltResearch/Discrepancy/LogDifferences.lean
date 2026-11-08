import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Examples.ProofFleet__prooffleet.Dependencies.v08927546f6f6.MoltResearch.Discrepancy.ExpSums
import Mathlib.Analysis.Real.Pi.Bounds
/-!
# The unit-difference calculus and iterated differences of `log` (Track L of #3020)

The quantitative core of the van der Corput cascade: two-sided bounds on
iterated unit differences of the logarithm, with the factorially exact
constants the `k`-th derivative tests consume.

* `dOp`, `dIter` — the forward unit difference and its iterates;
* `diff_shift_eq_sum` — a multi-step difference decomposes into shifted
  unit differences (how arbitrary-step Weyl data reduces to unit-step data);
* `dIter_inv_shift` — **the exact shifted-reciprocal identity**
  `Δᵏ(1/(m+x)) = (−1)^k k! / ((n+x)(n+1+x)⋯(n+k+x))` — pure telescoping
  algebra, no analysis;
* `dIter_log_eq_integral` — iterated log differences in closed integral
  form: `Δ^{k+1} log(n) = ∫₀¹ (−1)^k k!/∏(n+i+x) dx` (the integral is an
  exact summation device — no derivatives, no mean value theorem);
* `dIter_log_sandwich` — **the two-sided sandwich**
  `k!/(n+k+1)^{k+1} ≤ (−1)^k·Δ^{k+1} log(n) ≤ k!/n^{k+1}`.

Downstream, the log-phase `−(t/2π)·log n` inherits `k`-th difference
control at every scale, powering the cascade of derivative tests behind
the Weyl-strength zeta bound.

The cascade transfer layer: `dIter_neg` and `norm_sum_e_neg` (sign flips
are free), `dIter_diff_comm`/`dIter_diff_eq_sum` (differences of the
`g`-differenced phase are `g`-fold sums of one-deeper differences — how
each Weyl step hands its sandwich to the next level), and
`dIter_diff_sandwich` (the two-sided bounds transfer with `[μ, gν]`).

The cascade itself: `cascadeBound` (the recursive bound — base the
second-derivative test at separation `√μ/2`, step one Weyl differencing
with the crude power-mean split) and **`vdck_pow`**, the abstract `k`-th
derivative test in power form: a phase whose `(j+2)`-nd unit differences
lie in `[μ, ν]` over the window (with budget `j·H` beyond) satisfies
`‖∑ e(ψ(n))‖^{2^j} ≤ cascadeBound j L H μ ν` — natural-number powers
throughout, no `rpow`.

The instantiation: `log_phase_block_bound` — the cascade applied to the
zeta phase `−(t/2π)·log n` on a near-dyadic window, with the sandwich
supplied by `dIter_log_sandwich` at `μ = (t/2π)(j+1)!/(4M)^{j+2}`,
`ν = (t/2π)(j+1)!/M^{j+2}`, and the alternating sign of `Δ^{j+2}log`
absorbed by parity (`j` even: the phase itself is positive-form; `j` odd:
conjugate via `norm_sum_e_neg`).
-/
namespace MoltResearch
namespace ExpSums
open Finset
def schedJ (d i : ℕ) : ℕ := (d - 2) / i - 1
/-- The slack budget of a block. -/
def schedU (d i : ℕ) : ℕ :=
  (i * (schedJ d i + 2) - (d + 1 + (schedJ d i + 1) ^ 2)) / 2
/-- The differencing log-length of a block. -/
def schedH (d i : ℕ) : ℕ :=
  (schedU d i - (schedJ d i + 2)) / (schedJ d i + 2)
def goodBlock (d i : ℕ) : Prop :=
  1 ≤ i ∧ i * (schedJ d i + 1) + 2 ≤ d
  ∧ d + 1 + (schedJ d i + 1) ^ 2 + 2 * (schedJ d i + 2) + 2
      ≤ i * (schedJ d i + 2)
  ∧ 4 * 2 ^ schedJ d i + 1 + 2 ^ schedJ d i ≤ 2 * schedH d i
  ∧ schedJ d i * 4 ^ schedH d i + schedJ d i + 2 ≤ 2 ^ (i + 1)
instance (d i : ℕ) : Decidable (goodBlock d i) := by
  unfold goodBlock
  infer_instance
end ExpSums
end MoltResearch
