module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.DivMoments
public import Examples.sthubbar__goldbach_lean.Dependencies.va8d8f04859e6.LeanLab.HeathBrown1985.Theorem2
/-!
P0096 Heath-Brown 1985, the bound 2.5: `Λ_Q(n) ≪ d(n) (log Q)²`, as on pages 48 to 49,
with `q/φ(q) ≪ log Q` for `q ≤ Q` taken from Elementary.lean.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
open scoped ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
theorem divisors_gcd_eq (n q : ℕ) (hn : 1 ≤ n) (hq : 1 ≤ q) :
    (n.gcd q).divisors = n.divisors.filter (· ∣ q) := by
  ext d
  simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left q (by omega)).ne'⟩
/-- `1/φ(q) ≤ e (1 + log Q / log 2) / q` for `1 ≤ q ≤ Q`. -/
theorem inv_totient_le (Q : ℝ) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q) :
    (Nat.totient q : ℝ)⁻¹ ≤ Real.exp 1 * (1 + Real.log Q / Real.log 2) / q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hl2 := Real.log_pos one_lt_two
  have h1 := div_totient_le q hq
  have hω : (q.primeFactors.card : ℝ) ≤ Real.log Q / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    exact (card_primeFactors_mul_log_two_le q hq).trans (Real.log_le_log hqR hqQ)
  have h2 : (q : ℝ) / Nat.totient q ≤ Real.exp 1 * (1 + Real.log Q / Real.log 2) :=
    h1.trans (mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le)
  rw [le_div_iff₀ hqR]
  calc (Nat.totient q : ℝ)⁻¹ * q = q / Nat.totient q := by field_simp
    _ ≤ _ := h2
end LeanLab.HeathBrown1985
