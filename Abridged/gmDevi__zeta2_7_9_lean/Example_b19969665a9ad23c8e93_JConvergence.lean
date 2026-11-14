import Mathlib

-- ==== Examples.gmDevi__zeta2_7_9_lean.Examples.Example_b19969665a9ad23c8e93_JConvergence ====
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
/-!
# Convergence of the Riemann sums of `(x + 1/2)^{-s}` (proof.md P1, P2)

**Theorem.** `Stmt_JConv : ∀ s, HasVolkenborn (halfPow s) (J s)`.  No hypotheses.

**Proof (as formalised).**  Put `w x := (2x+1)⁻¹ ∈ ℚ_[2]` (`jcW`), a 2-adic unit, so that
`halfPow s x = 2^s · w x ^ s` (`jc_halfPow`).  It suffices to show that the Riemann sums
`R_N := volkenbornSum (w ^ s) N` form a Cauchy sequence (`jc_cauchy`): completeness of `ℚ_[2]`
gives a limit `L`, `HasVolkenborn.const_mul` gives `HasVolkenborn (halfPow s) (2^s L)`, and
`HasVolkenborn.volkenborn_eq` identifies `2^s L` with `J s`.

1. `jc_pow_sub_pow`: `‖a‖, ‖b‖ ≤ 1 ⇒ ‖a^m - b^m‖ ≤ ‖a - b‖` (induction, ultrametric).
2. `jc_oddsum` (odd power sums): `‖∑_{x<2^N} w(x)^k‖ ≤ 2^{-N}` for every `k ≥ 0`.  Induction on
   `N`: split `range (2^{N+1})` into two halves and reflect the upper half (`x ↦ 2^{N+1}-1-x`,
   i.e. `u = 2x+1 ↦ 2^{N+2} - u`); then `w(y) ≡ -w(x) (mod 2^{N+2})`, so the sum is
   `(1 + (-1)^k) · ∑_{x<2^N} w(x)^k + O(2^{-N-2})`, and `‖1 + (-1)^k‖ ≤ 1/2`.
3. `jc_shift`: `w(2^N+x) - w(x) = -2^{N+1} w(2^N+x) w(x)`.
4. `jc_mixed`: `‖∑_{x<2^N} w(2^N+x)^i w(x)^l‖ ≤ 2^{-N}` (compare with `∑ w(x)^{i+l}` using 1, 3).
5. `jc_step`: `R_{N+1} - R_N = 2^{-N-1} ∑_{x<2^N} (a_x^s - b_x^s)` with `a_x = w(2^N+x)`,
   `b_x = w(x)`; by `geom_sum₂_mul` and 3 this is `-∑_{j<s} ∑_x a_x^{j+1} b_x^{s-j}` (the factor
   `2^{N+1}` cancels), so `‖R_{N+1} - R_N‖ ≤ 2^{-N}` by 4.  Then `cauchySeq_of_le_geometric`.
-/
open Filter Topology Finset
noncomputable section
namespace Zeta2


/-- `‖a‖, ‖b‖ ≤ 1 ⇒ ‖a^m - b^m‖ ≤ ‖a - b‖` in `ℚ_[2]`. -/
private lemma jc_pow_sub_pow {a b : ℚ_[2]} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (m : ℕ) :
    ‖a ^ m - b ^ m‖ ≤ ‖a - b‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : a ^ (m + 1) - b ^ (m + 1) = a ^ m * (a - b) + (a ^ m - b ^ m) * b := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow]
      calc ‖a‖ ^ m * ‖a - b‖ ≤ 1 * ‖a - b‖ :=
            mul_le_mul (pow_le_one₀ (norm_nonneg _) ha) le_rfl (norm_nonneg _) zero_le_one
        _ = ‖a - b‖ := one_mul _
    · rw [norm_mul]
      calc ‖a ^ m - b ^ m‖ * ‖b‖ ≤ ‖a - b‖ * 1 :=
            mul_le_mul ih hb (norm_nonneg _) (norm_nonneg _)
        _ = ‖a - b‖ := mul_one _

end Zeta2
end
