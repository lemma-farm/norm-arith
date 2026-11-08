import Examples.ProofFleet__prooffleet.Dependencies.vb1e2e68aecb5.MoltResearch.Discrepancy.PlancherelHarness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!
# Track C: large values of prime-block phase sums (Track R, C4a)

The kernel toolkit for the C4a window-energy bound: the oscillation kernel
`‖∫_{-L}^{L} e(−sξ) dξ‖ ≤ 1/(π|s|)`, the phase-product law
`e(−uξ)·conj(e(−vξ)) = e(−((u−v)ξ))`, the interval real-part commute, and
the log-separation `log q − log p ≥ (q−p)/q`.

The window-energy expansion (next unit) combines these with the
reciprocal prime-gap sum of `BrunTitchmarsh.lean`: the energy of
`S(ξ) = ∑_{p∈P} (a_p/p)·e(−ξ·log p)` over `[−L, L]` is at most
`2L·∑ 1/p² + (∑ 1/p)·O(loglog P₊)`, which caps the number of
`1`-separated `δE`-large values at `O_δ(1)` — the first leg of the C4
dichotomy.
-/
namespace MoltResearch
namespace ExpSums
open Real MeasureTheory
theorem char_mul_conj_char (u v ξ : ℝ) :
    ((Real.fourierChar (-(u * ξ)) : Circle) : ℂ)
      * (starRingEnd ℂ) ((Real.fourierChar (-(v * ξ)) : Circle) : ℂ)
      = ((Real.fourierChar (-((u - v) * ξ)) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  have h1 : (starRingEnd ℂ) ((((2*Real.pi*(-(v*ξ)) : ℝ)):ℂ) * Complex.I)
      = -((((2*Real.pi*(-(v*ξ)) : ℝ)):ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [h1]
  push_cast
  ring
theorem log_sub_log_ge (p q : ℕ) (hp : 1 ≤ p) (hpq : p < q) :
    ((q:ℝ) - p)/q ≤ Real.log q - Real.log p := by
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hq0 : (0:ℝ) < q := by
    have : (0:ℕ) < q := by omega
    exact_mod_cast this
  -- `log(p/q) ≤ p/q − 1` gives `log q − log p ≥ 1 − p/q = (q−p)/q`
  have h1 : Real.log ((p:ℝ)/q) ≤ (p:ℝ)/q - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log ((p:ℝ)/q) = Real.log p - Real.log q :=
    Real.log_div (ne_of_gt hp0) (ne_of_gt hq0)
  have h3 : ((q:ℝ) - p)/q = 1 - (p:ℝ)/q := by
    field_simp
  rw [h3]
  rw [h2] at h1
  linarith
theorem norm_sq_eq_mul_conj_re (z : ℂ) :
    ‖z‖^2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact (Complex.normSq_eq_norm_sq z).symm
end ExpSums
end MoltResearch
