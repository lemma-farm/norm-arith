import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- ==== Examples.Arthur742Ramos__verified_regret_matching_lean.Dependencies.v7eefa28386d3.RegretMatching.Basic ====
section
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

def payoff (p u : A → K) : K := ∑ a, p a * u a
def gain (r u : A → K) (a : A) : K := u a - payoff (strategy r) u
def update (r u : A → K) (a : A) : K := r a + gain r u a
def updatePlus (r u : A → K) (a : A) : K := positive (update r u a)
def potential (r : A → K) : K := ∑ a, positive (r a) ^ 2

end RegretMatching

end

-- ==== Examples.Arthur742Ramos__verified_regret_matching_lean.Examples.Example_26516ecb0a1c7d111efb_Bounds ====
set_option autoImplicit false
namespace RegretMatching
open scoped BigOperators
variable {A K : Type*} [Fintype A] [Nonempty A]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
inductive Mode where
  | ordinary
  | plus
  deriving DecidableEq, Repr
def step (m : Mode) (r u : A → K) : A → K :=
  match m with
  | .ordinary => update r u
  | .plus => updatePlus r u
def scores (m : Mode) (u : ℕ → A → K) : ℕ → A → K :=
  Nat.rec (motive := fun _ => A → K) (fun _ => 0)
    (fun t r => step m r (u t))


set_option linter.unusedVariables false in
theorem potential_scores_bound (m : Mode) (u : ℕ → A → K) (T : ℕ)
    (hu : ∀ t < T, ∀ a, 0 ≤ u t a ∧ u t a ≤ 1) 
    (h_RegretMatching_gain_square_le_one : ∀ {A : Type u_1} {K : Type u_2} [inst : Fintype A] [Nonempty A] [inst_2 : Field K]
      [inst_3 : LinearOrder K] [IsStrictOrderedRing K] (r u : A → K),
      (∀ (a : A), 0 ≤ u a ∧ u a ≤ 1) → ∀ (a : A), RegretMatching.gain r u a ^ 2 ≤ 1)
    (h_RegretMatching_potential_step : ∀ {A : Type u_1} {K : Type u_2} [inst : Fintype A] [inst_1 : Field K] [inst_2 : LinearOrder K]
      [IsStrictOrderedRing K] (m : RegretMatching.Mode) (r u : A → K),
      RegretMatching.potential (RegretMatching.step m r u) ≤
        RegretMatching.potential r + ∑ a : A, RegretMatching.gain r u a ^ 2)
    :
    potential (scores m u T) ≤ (Fintype.card A : K) * T := by
  induction T with
  | zero => simp [scores, potential, positive]
  | succ t ih =>
    have hi := ih (fun s hs => hu s (Nat.lt_succ_of_lt hs))
    have hs := h_RegretMatching_potential_step m (scores m u t) (u t)
    have hg : (∑ a, gain (scores m u t) (u t) a ^ 2) ≤ (Fintype.card A : K) := by
      calc
        _ ≤ ∑ _a : A, (1 : K) := Finset.sum_le_sum fun a _ => h_RegretMatching_gain_square_le_one _ _ (hu t (Nat.lt_succ_self t)) a
        _ = _ := by simp
    change potential (step m (scores m u t) (u t)) ≤ _
    push_cast
    nlinarith

end RegretMatching
