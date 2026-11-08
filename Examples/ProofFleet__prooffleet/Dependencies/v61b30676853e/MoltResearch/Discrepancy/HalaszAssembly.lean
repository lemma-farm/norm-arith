/-
# Discrepancy: the cheap Halász assembly

The composition layer of the Track R cheap-Halász build (Tao 2015,
Part E): the two class band-energy instances feeding the band/tail
Hölder split, and the pairing theorem `cheap_halasz_pairing` — the
Cesàro mean of a 1-bounded completely multiplicative function under a
band-uniform pretentious-distance floor, bounded by the three-scale
error counts, the Perron edge, the band term, and the window tail,
with every constant explicit and all parameters free for tuning.

The chain: `norm_cesaro_sub_main_le` (the three-scale split) →
`perron_sandwich` (the window sandwich, applied to the main-term
indicator) → `sum_main_eq_sum_box` (the box bridge) →
`norm_sum_translates_le_integral_char` (the Plancherel pairing at the
triple index) → `sum_triple_char_eq_mul` (the box factorization) →
`pairing_band_tail_split` (the band/tail Hölder split) with the
`Bband`-instance `norm_smooth_poly_band_le`, the class band energies
below, the trivial harmonic sups, `MV ≤ 1`, and `fourier_tail_le`.

The tuning tail of the file: `cheap_halasz_tuned` (the pairing at
`y₁ = y₂^B`, `t = 1`, `δ = 1/2`), the threshold lemmas
(`one_add_log_div_le`, `exp_neg_half_kill`, `log_pow_le_self`), the
term-by-term collapses (`rankin_tail_collapse`, `energy_sum_le`,
`head_exp_le`, `tail_energy_le`, `window_tail_le`) assembled by
`cheap_halasz_collapse`, and finally `cheap_halasz_eps` — **the cheap
Halász theorem** in ε-form: `‖∑_{n≤x} f‖/x ≤ ε + e^{W loglog x + W − M}`
at the cut `y₂ = ⌊log x⌋₊`, `B = ⌈16e¹²/ε⌉₊ + 1`, `ρ = ε/8`,
`L = (log x)⁴`.
-/
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.ThreeScale
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.PlancherelHarness
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.HalaszEuler
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.ParsevalBridge
import Examples.ProofFleet__prooffleet.Dependencies.v61b30676853e.MoltResearch.Discrepancy.PretentiousFactorization
namespace MoltResearch
open Finset ExpSums MeasureTheory Real
open scoped FourierTransform ContDiff
end MoltResearch
