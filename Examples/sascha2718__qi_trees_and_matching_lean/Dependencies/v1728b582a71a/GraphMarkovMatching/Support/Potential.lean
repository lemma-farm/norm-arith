module
/-
The countable probability space `(X, μ)` with a symmetric reflexive relation
`R`, the bad and good degrees `q` and `r`, and the potential `Φ(R,μ)`.

Design:

* `μ : PMF X`. Note this needs **no** `[Countable X]` hypothesis: a `PMF`
  sums to `1`, which forces its support to be countable automatically, so
  the standing countability assumption is encoded rather than assumed.
* No finiteness. Sums are `tsum`, and working in `ℝ≥0∞` makes them
  unconditionally summable by Fubini's theorem.
* `Φ` lands in `ℝ≥0∞`: the value `Φ = ∞` is meaningful and allowed.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v1728b582a71a.GraphMarkovMatching.Support.Phi
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
@[expose] public section
namespace GraphMarkovMatching.Support
open scoped ENNReal Classical
variable {X : Type*} {μ : PMF X} {R : X → X → Prop} {x y : X}
/-! ### The two degrees -/
/-- The good degree `r(x) = μ{y : x R y}` of Section 11.3. -/
noncomputable def rE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then μ y else 0
/-- The bad degree `q(x) = μ{y : ¬ x R y}` of Section 11.3. -/
noncomputable def qE (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ≥0∞ :=
  ∑' y, if R x y then 0 else μ y
/-- `r(x) + q(x) = 1`: the two degrees partition the total mass. -/
lemma rE_add_qE (μ : PMF X) (R : X → X → Prop) (x : X) : rE μ R x + qE μ R x = 1 := by
  rw [rE, qE, ← ENNReal.tsum_add, ← μ.tsum_coe]
  exact tsum_congr fun y => by split_ifs <;> simp
lemma qE_le_one : qE μ R x ≤ 1 := by
  rw [← rE_add_qE μ R x]; exact le_add_self
lemma rE_le_one : rE μ R x ≤ 1 := by
  rw [← rE_add_qE μ R x]; exact le_self_add
lemma qE_ne_top : qE μ R x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top qE_le_one
lemma rE_ne_top : rE μ R x ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top rE_le_one
noncomputable def q (μ : PMF X) (R : X → X → Prop) (x : X) : ℝ := (qE μ R x).toReal
/-- The real form of `r + q = 1`, available because both degrees are finite. -/
lemma toReal_rE_add_toReal_qE (μ : PMF X) (R : X → X → Prop) (x : X) :
    (rE μ R x).toReal + (qE μ R x).toReal = 1 := by
  rw [← ENNReal.toReal_add rE_ne_top qE_ne_top, rE_add_qE, ENNReal.toReal_one]
lemma q_nonneg : 0 ≤ q μ R x := ENNReal.toReal_nonneg
lemma q_le_one : q μ R x ≤ 1 := by
  have h := toReal_rE_add_toReal_qE μ R x
  have : (0 : ℝ) ≤ (rE μ R x).toReal := ENNReal.toReal_nonneg
  rw [q]; linarith
lemma tsum_not_rel_eq_qE (hsymm : ∀ a b, R a b → R b a) (μ : PMF X) (y : X) :
    (∑' x, if R x y then 0 else μ x) = qE μ R y := by
  rw [qE]
  exact tsum_congr fun x => by
    by_cases h : R x y
    · rw [ite_eq_left h, ite_eq_left (hsymm x y h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (hsymm y x hc))]
end GraphMarkovMatching.Support
