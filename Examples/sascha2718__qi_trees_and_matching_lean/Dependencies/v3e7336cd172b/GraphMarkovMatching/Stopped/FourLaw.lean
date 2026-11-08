module
/-
The four-law contraction of `arbitrary_offspring_matching.tex`
(`thm:four-law-contraction`): for two source laws
`ρ₁, ρ₂` and two target laws `τ₁, τ₂` whose eight restricted directed potentials are
at most `M`, whose eight zero masses are at most `z`, and whose four weighted zero
integrals are at most `e`,

    P(ρ₁ × ρ₂, τ₁ × τ₂; R^□) ≤ a M + b M² + (γ + 4αM) z + 4 (1 + αM) e

with `a = 2 (L + K)`, `b = C_α(u)` and `γ = 2 + 2β`. The bound parameters `z` and `e`
are the paper's `δ₁` and `δ₂`, respectively. The proof integrates over the
doubly-positive set with the cancellation of the mean bad degrees between the source-row
terms and the target-overlap terms (`eq:four-law-rows`, `eq:four-law-overlaps`), and
handles the source pairs with a zero child degree by the resolved normalisation.

The scalar parameters `L`, `K`, `L0` enter as hypotheses, so that the exact maxima
`Lfun`, `Kfun` and rational surrogates are both admissible.

Organisation of the proof:

* `row_real`, `row_pt_gen`: the pointwise row estimate with the `s ≤ u` / `s > u`
  split (`eq:four-law-denominators`, the chord `chord_gen`, `eq:four-law-weight`);
* `main_pt`: the pointwise bound on a doubly-positive source pair
  (`eq:four-law-numerator` divided by `(r^□)^α`);
* `resPsi_pt`, `tsum_resPsi_le`: the product bound `eq:four-law-product` integrated
  over the positive set, carrying the mean bad degrees;
* `tsum_qE_sq_le`, `overlap_two_le`: the overlap estimate with the reversed potentials,
  `eq:four-law-square` and the `(1-β) z` term;
* `failureD_symm`, `failureD_le_resQ`: the identity behind the cancellation of `Q`;
* `PhiDres_square_split`: the pairs with a zero child degree, by the resolved
  normalisation;
* `fourLaw_contraction`: the assembly.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Stopped.Scalar
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v3e7336cd172b.GraphMarkovMatching.Potential.Restricted
@[expose] public section
namespace GraphMarkovMatching.Stopped
open GraphMarkovMatching GraphMarkovMatching.Support
open scoped ENNReal Classical
lemma qE_eq_ofReal_q {X : Type} (τ : PMF X) (R : X → X → Prop) (x : X) :
    qE τ R x = ENNReal.ofReal (q τ R x) := by
  rw [q, ENNReal.ofReal_toReal qE_ne_top]
lemma K_nonneg_of_hK {α β K : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) : 0 ≤ K := by
  have h := hK β hβ0 hβ1
  simpa using h
/-! ### The pointwise row estimate -/
private lemma tsum_qE_sq_le {X : Type} {α β K : ℝ} (hα : 0 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) (τ ρ : PMF X)
    (R : X → X → Prop) :
    ∑' y, τ y * qE ρ R y ^ 2
      ≤ ENNReal.ofReal K * PhiDres α τ ρ R + ENNReal.ofReal β * failureD τ ρ R
        + ENNReal.ofReal (1 - β) * zMass τ ρ R := by
  have hK0 : 0 ≤ K := K_nonneg_of_hK hβ0 hβ1 hK
  rw [PhiDres, failureD, zMass, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  by_cases h : rE ρ R y = 0
  · have hq1 : qE ρ R y = 1 := by
      have := rE_add_qE ρ R y
      rwa [h, zero_add] at this
    rw [ite_eq_left h, ite_eq_left h, hq1]
    simp only [mul_zero, mul_one, zero_add, one_pow]
    rw [← add_mul, ← ENNReal.ofReal_add hβ0 (by linarith),
      show β + (1 - β) = (1 : ℝ) from by ring, ENNReal.ofReal_one, one_mul]
  · rw [ite_eq_right h, ite_eq_right h, mul_zero, mul_zero, add_zero]
    have hq : q ρ R y < 1 := q_lt_one_of_rE_ne_zero h
    have hn : 0 ≤ q ρ R y := q_nonneg
    have hφ : 0 ≤ phi α (q ρ R y) := phi_nonneg hn hq
    have hreal := sq_le_K_phi_add hα hK hn hq
    rw [qE_eq_ofReal_q, phiE_of_lt hq, ← ENNReal.ofReal_pow hn]
    calc τ y * ENNReal.ofReal (q ρ R y ^ 2)
        ≤ τ y * ENNReal.ofReal (K * phi α (q ρ R y) + β * q ρ R y) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hreal) _
      _ = ENNReal.ofReal K * (τ y * ENNReal.ofReal (phi α (q ρ R y)))
          + ENNReal.ofReal β * (τ y * ENNReal.ofReal (q ρ R y)) := by
          rw [ENNReal.ofReal_add (mul_nonneg hK0 hφ) (mul_nonneg hβ0 hn),
            ENNReal.ofReal_mul hK0, ENNReal.ofReal_mul hβ0]
          ring
/-- **One overlap integral** (`eq:four-law-overlaps`, one target law): with
`H_i ≤ q_{ρ_i} + αM`, the reversed potentials and `eq:four-law-square`,
`2 ∫ H₁ H₂ dτ ≤ 2KM + β (∫ q_{ρ₁} dτ + ∫ q_{ρ₂} dτ) + 2(1-β) z + 4αM² + 4αMz + 2α²M²`. -/
private lemma overlap_two_le {X : Type} {α β K : ℝ} (hα : 1 ≤ α) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hK : ∀ q, 0 ≤ q → q ≤ 1 → (q - β) * (1 - q) ^ α ≤ K) (τ ρ₁ ρ₂ τa τb : PMF X)
    (R : X → X → Prop) (hsymm : ∀ a b, R a b → R b a) (M z : ℝ≥0∞)
    (h1 : PhiDres α ρ₁ τa R ≤ M) (h2 : PhiDres α ρ₂ τb R ≤ M)
    (hr1 : PhiDres α τ ρ₁ R ≤ M) (hr2 : PhiDres α τ ρ₂ R ≤ M)
    (hz1 : zMass τ ρ₁ R ≤ z) (hz2 : zMass τ ρ₂ R ≤ z) :
    2 * ∑' y, τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)
      ≤ 2 * ENNReal.ofReal K * M
        + ENNReal.ofReal β * (failureD τ ρ₁ R + failureD τ ρ₂ R)
        + 2 * ENNReal.ofReal (1 - β) * z
        + 4 * ENNReal.ofReal α * M ^ 2 + 4 * ENNReal.ofReal α * M * z
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
  have hα0 : (0 : ℝ) ≤ α := by linarith
  have hH1 : ∀ y, HresD α ρ₁ τa R y ≤ qE ρ₁ R y + ENNReal.ofReal α * M := fun y =>
    (HresD_le hα ρ₁ τa R hsymm y).trans
      (add_le_add le_rfl (mul_le_mul_right ((KresD_le_PhiDres α ρ₁ τa R y).trans h1) _))
  have hH2 : ∀ y, HresD α ρ₂ τb R y ≤ qE ρ₂ R y + ENNReal.ofReal α * M := fun y =>
    (HresD_le hα ρ₂ τb R hsymm y).trans
      (add_le_add le_rfl (mul_le_mul_right ((KresD_le_PhiDres α ρ₂ τb R y).trans h2) _))
  have hpt : ∀ y, 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y))
      ≤ τ y * qE ρ₁ R y ^ 2 + τ y * qE ρ₂ R y ^ 2
        + 2 * ENNReal.ofReal α * M * (τ y * qE ρ₁ R y + τ y * qE ρ₂ R y)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 * τ y := by
    intro y
    calc 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y))
        = τ y * (2 * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)) := by ring
      _ ≤ τ y * (HresD α ρ₁ τa R y ^ 2 + HresD α ρ₂ τb R y ^ 2) :=
          mul_le_mul_right (ennreal_two_mul_le_add_sq _ _) _
      _ ≤ τ y * ((qE ρ₁ R y + ENNReal.ofReal α * M) ^ 2
          + (qE ρ₂ R y + ENNReal.ofReal α * M) ^ 2) := by
          gcongr
          · exact hH1 y
          · exact hH2 y
      _ = _ := by ring
  have hsq1 := tsum_qE_sq_le hα0 hβ0 hβ1 hK τ ρ₁ R
  have hsq2 := tsum_qE_sq_le hα0 hβ0 hβ1 hK τ ρ₂ R
  have hF1 : failureD τ ρ₁ R ≤ M + z :=
    (failureD_le_PhiDres_add_zMass α hα0 τ ρ₁ R).trans (add_le_add hr1 hz1)
  have hF2 : failureD τ ρ₂ R ≤ M + z :=
    (failureD_le_PhiDres_add_zMass α hα0 τ ρ₂ R).trans (add_le_add hr2 hz2)
  calc 2 * ∑' y, τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)
      = ∑' y, 2 * (τ y * (HresD α ρ₁ τa R y * HresD α ρ₂ τb R y)) :=
        ENNReal.tsum_mul_left.symm
    _ ≤ ∑' y, (τ y * qE ρ₁ R y ^ 2 + τ y * qE ρ₂ R y ^ 2
        + 2 * ENNReal.ofReal α * M * (τ y * qE ρ₁ R y + τ y * qE ρ₂ R y)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 * τ y) := ENNReal.tsum_le_tsum hpt
    _ = (∑' y, τ y * qE ρ₁ R y ^ 2) + (∑' y, τ y * qE ρ₂ R y ^ 2)
        + 2 * ENNReal.ofReal α * M * (failureD τ ρ₁ R + failureD τ ρ₂ R)
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left,
          ENNReal.tsum_mul_left, ENNReal.tsum_add, PMF.tsum_coe, mul_one, failureD, failureD]
    _ ≤ (ENNReal.ofReal K * M + ENNReal.ofReal β * failureD τ ρ₁ R
          + ENNReal.ofReal (1 - β) * z)
        + (ENNReal.ofReal K * M + ENNReal.ofReal β * failureD τ ρ₂ R
          + ENNReal.ofReal (1 - β) * z)
        + 2 * ENNReal.ofReal α * M * ((M + z) + (M + z))
        + 2 * ENNReal.ofReal α ^ 2 * M ^ 2 := by
        gcongr
        · exact hsq1.trans (add_le_add (add_le_add (mul_le_mul_right hr1 _) le_rfl)
            (mul_le_mul_right hz1 _))
        · exact hsq2.trans (add_le_add (add_le_add (mul_le_mul_right hr2 _) le_rfl)
            (mul_le_mul_right hz2 _))
    _ = _ := by ring
/-! ### The pairs with a zero child degree -/
end GraphMarkovMatching.Stopped
