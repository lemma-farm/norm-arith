import Examples.Arthur742Ramos__verified_regret_matching_lean.Dependencies.v7eefa28386d3.RegretMatching.Basic
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
omit [Nonempty A] [IsStrictOrderedRing K] in
theorem scores_succ (m : Mode) (u : ℕ → A → K) (t : ℕ) :
    scores m u (t + 1) = step m (scores m u t) (u t) := rfl
def play (m : Mode) (u : ℕ → A → K) (t : ℕ) : A → K := strategy (scores m u t)
def cumulative (m : Mode) (u : ℕ → A → K) (T : ℕ) (a : A) : K :=
  ∑ t ∈ Finset.range T, gain (scores m u t) (u t) a
theorem play_valid (m : Mode) (u : ℕ → A → K) (t : ℕ) : IsDistribution (play m u t) :=
  strategy_valid _
omit [Nonempty A] in
theorem payoff_unit_interval {p u : A → K} (hp : IsDistribution p)
    (hu : ∀ a, 0 ≤ u a ∧ u a ≤ 1) : 0 ≤ payoff p u ∧ payoff p u ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (hp.1 a) (hu a).1
  · calc
      _ ≤ ∑ a, p a * 1 := Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hu a).2 (hp.1 a)
      _ = 1 := by simpa using hp.2
theorem gain_square_le_one (r u : A → K) (hu : ∀ a, 0 ≤ u a ∧ u a ≤ 1) (a : A) :
    gain r u a ^ 2 ≤ 1 := by
  have hp := payoff_unit_interval (strategy_valid r) hu
  have ha := hu a
  unfold gain
  nlinarith [mul_nonneg (show 0 ≤ 1 - (u a - payoff (strategy r) u) by linarith)
    (show 0 ≤ 1 + (u a - payoff (strategy r) u) by linarith)]
omit [Nonempty A] in
theorem potential_step (m : Mode) (r u : A → K) :
    potential (step m r u) ≤ potential r + ∑ a, gain r u a ^ 2 := by
  cases m
  · exact potential_update r u
  · exact potential_updatePlus r u
omit [Nonempty A] in
theorem cumulative_le_scores (m : Mode) (u : ℕ → A → K) (T : ℕ) (a : A) :
    cumulative m u T a ≤ scores m u T a := by
  induction T with
  | zero => simp [cumulative, scores]
  | succ t ih =>
    rw [cumulative, Finset.sum_range_succ]
    change cumulative m u t a + gain (scores m u t) (u t) a ≤ _
    cases m
    · exact add_le_add ih le_rfl
    · exact (add_le_add ih (le_refl (gain (scores .plus u t) (u t) a))).trans (le_max_left _ _)
omit [Nonempty A] [IsStrictOrderedRing K] in
theorem ordinary_scores_eq_cumulative (u : ℕ → A → K) (T : ℕ) :
    scores .ordinary u T = cumulative .ordinary u T := by
  induction T with
  | zero => funext a; simp [scores, cumulative]
  | succ t ih =>
    funext a
    simp only [scores, step, update, cumulative, Finset.sum_range_succ]
    congr 1
    exact congrFun ih a
theorem potential_scores_bound (m : Mode) (u : ℕ → A → K) (T : ℕ)
    (hu : ∀ t < T, ∀ a, 0 ≤ u t a ∧ u t a ≤ 1) :
    potential (scores m u T) ≤ (Fintype.card A : K) * T := by
  induction T with
  | zero => simp [scores, potential, positive]
  | succ t ih =>
    have hi := ih (fun s hs => hu s (Nat.lt_succ_of_lt hs))
    have hs := potential_step m (scores m u t) (u t)
    have hg : (∑ a, gain (scores m u t) (u t) a ^ 2) ≤ (Fintype.card A : K) := by
      calc
        _ ≤ ∑ _a : A, (1 : K) := Finset.sum_le_sum fun a _ => gain_square_le_one _ _ (hu t (Nat.lt_succ_self t)) a
        _ = _ := by simp
    change potential (step m (scores m u t) (u t)) ≤ _
    push_cast
    nlinarith
theorem positive_score_square_bound (m : Mode) (u : ℕ → A → K) (T : ℕ)
    (hu : ∀ t < T, ∀ a, 0 ≤ u t a ∧ u t a ≤ 1) (a : A) :
    positive (scores m u T a)^2 ≤ (Fintype.card A : K) * T := by
  exact (Finset.single_le_sum (fun b _ => sq_nonneg (positive (scores m u T b)))
    (Finset.mem_univ a)).trans (potential_scores_bound m u T hu)
/-- Square-root-free certificate, usable over the rationals as well as the reals. -/
theorem average_regret_certificate (m : Mode) (u : ℕ → A → K) (T : ℕ)
    (hT : 0 < T) (hu : ∀ t < T, ∀ a, 0 ≤ u t a ∧ u t a ≤ 1)
    (ε : K) (hε : 0 ≤ ε) (hbudget : (Fintype.card A : K) * T ≤ (T * ε)^2) (a : A) :
    cumulative m u T a / T ≤ ε := by
  have ht : (0 : K) < T := Nat.cast_pos.mpr hT
  have hs := positive_score_square_bound m u T hu a
  have hr := (cumulative_le_scores m u T a).trans (le_max_left _ _ : scores m u T a ≤ positive (scores m u T a))
  change cumulative m u T a ≤ positive (scores m u T a) at hr
  have hp := positive_nonneg (scores m u T a)
  have he : 0 ≤ (T : K) * ε := mul_nonneg ht.le hε
  apply (div_le_iff₀ ht).mpr
  nlinarith
theorem external_regret_bound (m : Mode) (u : ℕ → A → ℝ) (T : ℕ)
    (hu : ∀ t < T, ∀ a, 0 ≤ u t a ∧ u t a ≤ 1) (a : A) :
    cumulative m u T a ≤ Real.sqrt ((Fintype.card A : ℝ) * T) := by
  have hs := positive_score_square_bound m u T hu a
  have hr := (cumulative_le_scores m u T a).trans (le_max_left _ _ : scores m u T a ≤ positive (scores m u T a))
  change cumulative m u T a ≤ positive (scores m u T a) at hr
  have hroot := Real.sq_sqrt (show 0 ≤ (Fintype.card A : ℝ) * T by positivity)
  have hn := Real.sqrt_nonneg ((Fintype.card A : ℝ) * T)
  have hp := positive_nonneg (scores m u T a)
  nlinarith
/-- The same bound holds for every fixed mixed comparator chosen in hindsight. -/
theorem mixed_external_regret_bound (m : Mode) (u : ℕ → A → ℝ) (T : ℕ)
    (hu : ∀ t < T, ∀ a, 0 ≤ u t a ∧ u t a ≤ 1)
    (q : A → ℝ) (hq : IsDistribution q) :
    (∑ a, q a * cumulative m u T a) ≤ Real.sqrt ((Fintype.card A : ℝ) * T) := by
  calc
    _ ≤ ∑ a, q a * Real.sqrt ((Fintype.card A : ℝ) * T) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (external_regret_bound m u T hu a) (hq.1 a)
    _ = _ := by rw [← Finset.sum_mul, hq.2, one_mul]
end RegretMatching
