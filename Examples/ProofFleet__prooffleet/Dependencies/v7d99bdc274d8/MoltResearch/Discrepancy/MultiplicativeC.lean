import Examples.ProofFleet__prooffleet.Dependencies.v7d99bdc274d8.MoltResearch.Discrepancy.Multiplicative
/-!
# Discrepancy: ℂ-valued completely multiplicative language layer

First language-layer module for the Tao 2015 analytic core
(`Problems/tao2015_analytic_core.md`): the ℂ-valued predicates the Fourier-reduction and
log-Elliott interfaces are stated over, plus the coercion bridge from the existing ℤ-valued
substrate.

Definitions:
- `CompletelyMultiplicativeC g` — `g (a * b) = g a * g b` for **all** `a b : ℕ` (no coprimality
  hypothesis, mirroring the ℤ-valued `CompletelyMultiplicative`).
- `Unimodular g` — `‖g n‖ = 1` for all `n` (the "valued in the unit circle `S¹`" hypothesis of
  Tao's interfaces, arXiv:1509.05363 §2).

Bridges (the ℤ-valued substrate embeds in the ℂ-valued language):
- `CompletelyMultiplicative.toC` — a ℤ-valued completely multiplicative sequence is completely
  multiplicative after coercion to ℂ.
- `IsSignSequence.unimodularC` — sign sequences are unimodular after coercion to ℂ.

Partial sums:
- `apSumC g d n` — ℂ-valued homogeneous AP partial sum, mirroring `apSum`.
- `CompletelyMultiplicativeC.apSumC_eq_mul_apSumC_one` — the multiplicative collapse
  `apSumC g d n = g d * apSumC g 1 n` (port of `CompletelyMultiplicative.apSum_eq_mul_apSum_one`).
- `CompletelyMultiplicativeC.norm_apSumC_eq_norm_apSumC_one` — its norm-level corollary for
  unimodular `g`: partial-sum growth along any step `d` is the step-one growth.

Design note (from the card's decision record): interfaces for the analytic core must be stated
over ℂ-valued unimodular functions — the ±1 subclass loses the character-modulated cases. The
ℤ-valued bridge below is the hand-off *into* that subclass once a reduction produces candidates,
not a substitute for it.
-/
namespace MoltResearch
/-- A ℂ-valued completely multiplicative sequence: `g (a * b) = g a * g b` for all **nonzero**
`a b : ℕ` (no coprimality hypothesis).

ℂ-valued analogue of `CompletelyMultiplicative`. As there, we do not bake in `g 1 = 1`: it
follows for unimodular sequences (`CompletelyMultiplicativeC.map_one_of_unimodular`), and keeping
the definition minimal makes it easier to produce.

The `a ≠ 0 → b ≠ 0` guards are load-bearing (issue #2879): the literature defines completely
multiplicative functions on `{1, 2, ...}`, and an unguarded law instantiated at `b = 0` gives
`g 0 = g a * g 0` for every `a`, which under any nonvanishing-at-`0` condition (`Unimodular`)
collapses the class to the constant-1 function and vacates every theorem quantifying over it.
With the guards, `g 0` is genuinely unconstrained junk.
-/
def CompletelyMultiplicativeC (g : ℕ → ℂ) : Prop :=
  ∀ a b : ℕ, a ≠ 0 → b ≠ 0 → g (a * b) = g a * g b
/-- A unimodular sequence: every value lies on the complex unit circle.

This is the "valued in `S¹`" hypothesis in Tao's Fourier-reduction and log-Elliott interfaces.
-/
def Unimodular (g : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, ‖g n‖ = 1
namespace Unimodular
variable {g : ℕ → ℂ}
theorem ne_zero (hg : Unimodular g) (n : ℕ) : g n ≠ 0 := by
  intro h
  have h1 := hg n
  rw [h] at h1
  norm_num at h1
end Unimodular
namespace CompletelyMultiplicativeC
variable {g : ℕ → ℂ}
end CompletelyMultiplicativeC
namespace CompletelyMultiplicative
variable {f : ℕ → ℤ}
end CompletelyMultiplicative
namespace IsSignSequence
variable {f : ℕ → ℤ}
end IsSignSequence
end MoltResearch
