module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_41dc78ce56addd1ebc86_GoldbachSW2 ====
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
set_option maxHeartbeats 4000000
/-! ### ================= SiegelTheorem.lean (verbatim, deduplicated) ================= -/
set_option maxHeartbeats 2000000
/-!
# Siegel's theorem for Dirichlet L-functions — brick-by-brick (Goldfeld's route)

Target: `siegel_zero_free`: ∀ ε > 0, ∃ c(ε) > 0, every real zero β of every L(·,χ)
(χ real nontrivial mod q) satisfies β ≤ 1 − c(ε)/q^ε. Ineffective (the dichotomy
case-split is classical); the last missing zero-free input for Siegel–Walfisz and
hence for almost-all binary Goldbach (see the approved roadmap plan).

Phase A of the roadmap; every lemma verified 0-error + `#print axioms`-clean
([propext, Classical.choice, Quot.sound]) before banking.
-/
open PowerSeries ArithmeticFunction Finset Filter

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/


/-- **The generalized Dirichlet test** (Siegel brick A5-a): `q`-bounded partial sums
    against ANY nonneg antitone weight: `|Σ_{y<d≤z} g(d)w(d)| ≤ 2q·w(y+1)` — the
    uniform-in-`s` engine for the `L(1,χ)` identifications. -/
lemma abel_tail_general (g : ℕ → ℝ) (q : ℝ) (w : ℕ → ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q)
    (hw0 : ∀ d, 0 ≤ w d) (hwa : ∀ d, w (d + 1) ≤ w d)
    (y : ℕ) : ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, g d * w d| ≤ 2 * q * w (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  -- the general Abel window identity
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, g d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, g n) * w (z + 1) - (∑ n ∈ Icc 1 y, g n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      interval_cases y
      simp
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        have hempty : Icc (m + 1 + 1) (m + 1) = (∅ : Finset ℕ) :=
          Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty, Finset.sum_empty]
        ring
      · have hins : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        have hnotmem : (m + 1) ∉ Icc (y + 1) m := by
          simp only [Finset.mem_Icc]
          omega
        rw [hins, Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, ih hge]
        have hS : ∑ n ∈ Icc 1 (m + 1), g n = g (m + 1) + ∑ n ∈ Icc 1 m, g n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- the weight telescope
  have htel : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, (w d - w (d + 1)) = w (y + 1) - w (z + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      interval_cases y
      simp
    | succ m ih =>
      intro hym
      rcases Nat.lt_or_ge m y with hlt | hge
      · have hy' : y = m + 1 := by omega
        subst hy'
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        ring
      · rw [show Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) from by
          ext d
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega, Finset.sum_insert (by
            simp only [Finset.mem_Icc]
            omega), ih hge]
        ring
  intro z hz
  rw [hwindow z hz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))| ≤ q * (w d - w (d + 1)) := by
    intro d _
    rw [abs_mul, abs_of_nonneg (show (0:ℝ) ≤ w d - w (d + 1) from by linarith [hwa d])]
    apply mul_le_mul_of_nonneg_right (hG d)
    linarith [hwa d]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, g n) * w (z + 1) - (∑ n ∈ Icc 1 y, g n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, g n) * w (y + 1)| := by
        have h1 := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, g n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, g n) * w (y + 1)))
        have h2 := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, g n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at h1
        linarith
    _ ≤ q * (w (y + 1) - w (z + 1)) + q * w (z + 1) + q * w (y + 1) := by
        have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
            ≤ q * (w (y + 1) - w (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * (w d - w (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * (w d - w (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ∑ d ∈ Icc (y + 1) z, (w d - w (d + 1)) := by
                rw [Finset.mul_sum]
            _ = q * (w (y + 1) - w (z + 1)) := by rw [htel z hz]
        have h2 : |(∑ n ∈ Icc 1 z, g n) * w (z + 1)| ≤ q * w (z + 1) := by
          rw [abs_mul, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_right (hG z) (hw0 _)
        have h3 : |(∑ n ∈ Icc 1 y, g n) * w (y + 1)| ≤ q * w (y + 1) := by
          rw [abs_mul, abs_of_nonneg (hw0 _)]
          exact mul_le_mul_of_nonneg_right (hG y) (hw0 _)
        linarith
    _ ≤ 2 * q * w (y + 1) := by
        have := hw0 (z + 1)
        linarith

