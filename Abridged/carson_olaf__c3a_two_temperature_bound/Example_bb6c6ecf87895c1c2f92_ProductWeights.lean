module

public import Mathlib

-- ==== Examples.carson_olaf__c3a_two_temperature_bound.Examples.Example_bb6c6ecf87895c1c2f92_ProductWeights ====
/-
Copyright (c) 2026 Logan Kleinwaks. All rights reserved.
Released under Apache 2.0 license; see LICENSE-Kleinwaks.
Reused from kleinwaks/masked-digit-sum-difference-bound,
commit 352ab86effecb7efce415507a8c781ec158b86e0.
-/
/- Modified by Carson Olafson with GPT-6 Astra: ported module visibility
for Lean 4.35.0-rc2; mathematical declarations and proofs are unchanged. -/
@[expose] public section
/-!
# Product weights on words and a Chebyshev estimate

This file develops the elementary discrete probability needed for the construction proofs of
`masked_digit_bound.tex`.  In the source the counting is carried out with the method of types
and the multinomial estimate (5) (`eq:multinomial-estimate`); here the equivalent
concentration input is packaged as a second-moment (Chebyshev) estimate for the product
measure `w ↦ ∏ⱼ p (w j)` on words, which is the same Gibbs measure `p` of equation (7)
(`eq:gibbs`) of the source.

The main results are:

* `ProductWeights.sum_wt`: the product weights sum to one;
* `ProductWeights.sum_wt_sq_of_centered`: the exact second moment of a centred additive
  statistic;
* `ProductWeights.mass_deviation_le`: the Chebyshev bound for such a statistic.
-/
open scoped BigOperators
namespace MaskedDigit
namespace ProductWeights
variable {A : Type*} [Fintype A]
/-- The product weight `∏ⱼ p (w j)` of a word `w`, i.e. the Gibbs product measure used in the
construction proofs of `masked_digit_bound.tex`. -/
def wt (p : A → ℝ) {l : ℕ} (w : Fin l → A) : ℝ := ∏ j, p (w j)


set_option linter.unusedVariables false in
/-- **Chebyshev's inequality for the product weights.**  The total weight of the words on
which a centred additive statistic deviates by at least `t` is at most `l V / t²`.  This is
the concentration input for the constructions of Propositions 2 and 4 of
`masked_digit_bound.tex`. -/
theorem mass_deviation_le (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1) (g : A → ℝ)
    (hg : ∑ a, p a * g a = 0) (l : ℕ) {t : ℝ} (ht : 0 < t) 
    (h_MaskedDigit_ProductWeights_sum_wt_sq_of_centered : ∀ {A : Type u_1} [inst : Fintype A] (p : A → ℝ),
      ∑ a : A, p a = 1 →
        ∀ (g : A → ℝ),
          ∑ a : A, p a * g a = 0 →
            ∀ (l : ℕ),
              ∑ w : Fin l → A, MaskedDigit.ProductWeights.wt p w * (∑ j : Fin l, g (w j)) ^ 2 =
                (↑l : ℝ) * ∑ a : A, p a * g a ^ 2)
    (h_MaskedDigit_ProductWeights_wt_nonneg : ∀ {A : Type u_1} {p : A → ℝ},
      (∀ (a : A), 0 ≤ p a) → ∀ {l : ℕ} (w : Fin l → A), 0 ≤ MaskedDigit.ProductWeights.wt p w)
    :
    ∑ w ∈ Finset.univ.filter (fun w : Fin l → A => t ≤ |∑ j, g (w j)|), wt p w ≤
      (l * ∑ a, p a * g a ^ 2) / t ^ 2 := by
  classical
  set Bad := Finset.univ.filter (fun w : Fin l → A => t ≤ |∑ j, g (w j)|) with hBad
  have key : t ^ 2 * ∑ w ∈ Bad, wt p w ≤ ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2 := by
    rw [Finset.mul_sum]
    calc ∑ w ∈ Bad, t ^ 2 * wt p w
        ≤ ∑ w ∈ Bad, wt p w * (∑ j, g (w j)) ^ 2 := by
          refine Finset.sum_le_sum fun w hw => ?_
          have hw' : t ≤ |∑ j, g (w j)| := by
            simpa [hBad] using (Finset.mem_filter.1 hw).2
          have hnn := h_MaskedDigit_ProductWeights_wt_nonneg hp w
          have hsq : t ^ 2 ≤ (∑ j, g (w j)) ^ 2 := by
            nlinarith [sq_abs (∑ j, g (w j)), abs_nonneg (∑ j, g (w j))]
          rw [mul_comm (wt p w)]
          exact mul_le_mul_of_nonneg_right hsq hnn
      _ ≤ ∑ w : Fin l → A, wt p w * (∑ j, g (w j)) ^ 2 := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro w _ _
          exact mul_nonneg (h_MaskedDigit_ProductWeights_wt_nonneg hp w) (sq_nonneg _)
  rw [h_MaskedDigit_ProductWeights_sum_wt_sq_of_centered p hsum g hg l] at key
  rw [le_div_iff₀ (by positivity)]
  linarith [key]
/-! ## The Gibbs weights -/
section Gibbs
variable [Nonempty A]

end Gibbs
end ProductWeights
end MaskedDigit
