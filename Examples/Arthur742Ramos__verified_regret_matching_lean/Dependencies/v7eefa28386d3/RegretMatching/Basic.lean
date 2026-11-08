import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
/-! # Regret-matching updates over ordered fields

The uniform fallback makes the strategy total even when all scores are nonpositive.
Payoffs are maximized. Both real analysis and exact rational execution share this code.
-/
namespace RegretMatching
open scoped BigOperators
variable {A K : Type*} [Fintype A] [Nonempty A]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
def positive (x : K) : K := max x 0
def mass (r : A → K) : K := ∑ a, positive (r a)
def strategy (r : A → K) (a : A) : K :=
  if mass r = 0 then 1 / (Fintype.card A : K) else positive (r a) / mass r
def IsDistribution (p : A → K) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1
def payoff (p u : A → K) : K := ∑ a, p a * u a
def gain (r u : A → K) (a : A) : K := u a - payoff (strategy r) u
def update (r u : A → K) (a : A) : K := r a + gain r u a
def updatePlus (r u : A → K) (a : A) : K := positive (update r u a)
def potential (r : A → K) : K := ∑ a, positive (r a) ^ 2
omit [IsStrictOrderedRing K] in
theorem positive_nonneg (x : K) : 0 ≤ positive x := le_max_right _ _
omit [Nonempty A] in
theorem mass_nonneg (r : A → K) : 0 ≤ mass r :=
  Finset.sum_nonneg fun _ _ => positive_nonneg _
theorem strategy_valid (r : A → K) : IsDistribution (strategy r) := by
  have hc : (0 : K) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · intro a
    unfold strategy
    split_ifs
    · positivity
    · exact div_nonneg (positive_nonneg _) (mass_nonneg _)
  · by_cases h : mass r = 0
    · simp [strategy, h, ne_of_gt hc]
    · simp only [strategy, h, ↓reduceIte, ← Finset.sum_div]
      change mass r / mass r = 1
      exact div_self h
omit [Nonempty A] in
theorem positive_eq_zero_of_mass_zero {r : A → K} (h : mass r = 0) (a : A) :
    positive (r a) = 0 := by
  have ha : positive (r a) ≤ mass r :=
    Finset.single_le_sum (fun b _ => positive_nonneg (r b)) (Finset.mem_univ a)
  exact le_antisymm (h ▸ ha) (positive_nonneg _)
omit [Nonempty A] in
theorem weighted_gain_zero (r u : A → K) : ∑ a, positive (r a) * gain r u a = 0 := by
  by_cases h : mass r = 0
  · simp [positive_eq_zero_of_mass_zero h]
  · have hp : payoff (strategy r) u = (∑ a, positive (r a) * u a) / mass r := by
      simp only [payoff, strategy, h, ↓reduceIte, div_mul_eq_mul_div, Finset.sum_div]
    simp only [gain, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp]
    change _ - mass r * (_ / mass r) = 0
    field_simp
    ring
theorem positive_square_step (x y : K) :
    positive (x + y) ^ 2 ≤ positive x ^ 2 + 2 * positive x * y + y ^ 2 := by
  unfold positive
  by_cases hx : 0 ≤ x <;> by_cases hxy : 0 ≤ x + y
  · rw [max_eq_left hx, max_eq_left hxy]; nlinarith
  · rw [max_eq_left hx, max_eq_right (le_of_not_ge hxy)]; nlinarith [sq_nonneg (x+y)]
  · rw [max_eq_right (le_of_not_ge hx), max_eq_left hxy]
    have : 0 ≤ y := by linarith
    nlinarith [mul_nonneg (neg_nonneg.mpr (le_of_not_ge hx)) hxy]
  · rw [max_eq_right (le_of_not_ge hx), max_eq_right (le_of_not_ge hxy)]
    nlinarith [sq_nonneg y]
omit [Nonempty A] in
theorem potential_update (r u : A → K) :
    potential (update r u) ≤ potential r + ∑ a, gain r u a ^ 2 := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun a (_ : a ∈ Finset.univ) => positive_square_step (r a) (gain r u a))
  have hz := weighted_gain_zero r u
  simp only [potential, update]
  calc
    _ ≤ ∑ a, (positive (r a)^2 + 2 * positive (r a) * gain r u a + gain r u a^2) := h
    _ = _ := by simp only [Finset.sum_add_distrib]; rw [show (∑ a, 2 * positive (r a) * gain r u a) = 0 by simpa [mul_assoc, ← Finset.mul_sum] using congrArg (fun x : K => 2*x) hz]; ring
omit [Nonempty A] in
theorem potential_updatePlus (r u : A → K) :
    potential (updatePlus r u) ≤ potential r + ∑ a, gain r u a ^ 2 := by
  simpa [potential, updatePlus, positive, max_assoc] using potential_update r u
end RegretMatching
