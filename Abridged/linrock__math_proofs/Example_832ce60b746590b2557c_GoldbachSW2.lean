module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_832ce60b746590b2557c_GoldbachSW2 ====
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


set_option linter.unusedVariables false in
/-- **The Euler–Maclaurin tail series is differentiable on `Re s > 9/10`**
    (Siegel brick A2h-ii-γ): `Wtail_x(s) := Σ'_n [n≥x]·((s−1)n^{−s} − (n^{1−s}−(n+1)^{1−s}))`
    is differentiable at every point of the half-plane — the continuation vehicle of the
    ζ-truncation. M-test on windows, head split off as a finite entire sum. -/
theorem wtail_differentiableAt (x : ℕ) (hx : 1 ≤ x) (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) 
    (h_euler_maclaurin_kernel : ∀ (s : ℂ) (n : ℕ),
      2 ≤ n →
        ∀ (W : ℝ),
          ‖1 - s‖ ≤ W →
            W * (1 / (↑n : ℝ)) ≤ 1 →
              ‖(s - 1) * (↑n : ℂ) ^ (-s) - ((↑n : ℂ) ^ (1 - s) - (↑(n + 1) : ℂ) ^ (1 - s))‖ ≤
                4 * (W + 1) ^ 2 * (1 / (↑n : ℝ)) ^ 2 * (↑n : ℝ) ^ (1 - s.re))
    :
    DifferentiableAt ℂ (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) s₀ := by
  set σ₀ : ℝ := (9/10 + s₀.re) / 2 with hσ₀
  have hσ₀1 : 9/10 < σ₀ := by rw [hσ₀]; linarith
  have hσ₀2 : σ₀ < s₀.re := by rw [hσ₀]; linarith
  set R : ℝ := ‖s₀‖ + 1 with hR
  have hR0 : 0 < R := by
    rw [hR]
    have := norm_nonneg s₀
    linarith
  set U : Set ℂ := {s : ℂ | σ₀ < s.re} ∩ Metric.ball 0 R with hU
  have hUopen : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const Complex.continuous_re
    · exact Metric.isOpen_ball
  have hs₀U : s₀ ∈ U := by
    rw [hU]
    constructor
    · exact hσ₀2
    · rw [Metric.mem_ball, dist_zero_right, hR]
      linarith
  set W : ℝ := R + 2 with hW
  set N₀ : ℕ := max x (Nat.ceil R + 4) with hN₀
  have hN₀x : x ≤ N₀ := le_max_left _ _
  have hN₀2 : 2 ≤ N₀ := le_trans (by omega) (le_max_right x (Nat.ceil R + 4))
  have hN₀W : ∀ n : ℕ, N₀ ≤ n → W ≤ (n:ℝ) := by
    intro n hn
    have h1 : Nat.ceil R + 4 ≤ n := le_trans (le_max_right x _) hn
    have h2 : ((Nat.ceil R + 4 : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
    have h3 : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
    push_cast at h2
    rw [hW]
    linarith
  -- the pointwise kernel bound on U, for n ≥ N₀
  have hVbound : ∀ n : ℕ, N₀ ≤ n → ∀ w : ℂ, w ∈ U →
      ‖(w - 1) * ((n:ℂ)) ^ (-w)
        - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) := by
    intro n hn w hwU
    obtain ⟨hwre, hwball⟩ := hwU
    have hwre' : σ₀ < w.re := hwre
    have hwnorm : ‖w‖ < R := by
      rw [Metric.mem_ball, dist_zero_right] at hwball
      exact hwball
    have hn2 : 2 ≤ n := le_trans hN₀2 hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hWb : ‖1 - w‖ ≤ W := by
      calc ‖1 - w‖ ≤ ‖(1:ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ = 1 + ‖w‖ := by rw [norm_one]
        _ ≤ W := by rw [hW]; linarith
    have hWn : W * (1 / (n:ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one hn0]
      exact hN₀W n hn
    have hker := h_euler_maclaurin_kernel w n hn2 W hWb hWn
    have hexp : ((n:ℝ)) ^ (1 - w.re) ≤ ((n:ℝ)) ^ (1 - σ₀) := by
      apply Real.rpow_le_rpow_of_exponent_le hn1r
      linarith
    calc ‖(w - 1) * ((n:ℂ)) ^ (-w)
          - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w))‖
        ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - w.re) := hker
      _ ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
  -- the majorant is summable
  have husum : Summable (fun n : ℕ => if n < N₀ then (0:ℝ) else
      4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) := by
    have hmajsum : Summable (fun n : ℕ => (4 * (W + 1) ^ 2) * (1 / ((n:ℝ)) ^ (σ₀ + 1))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le _ _ hmajsum
    · intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h]
      · rw [if_neg (not_lt.mpr h)]
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have h1 : (1:ℕ) ≤ n := le_trans (le_trans hx hN₀x) h
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
          linarith
        positivity
    · intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h]
        positivity
      · rw [if_neg (not_lt.mpr h)]
        have hn0 : (0:ℝ) < (n:ℝ) := by
          have h1 : (1:ℕ) ≤ n := le_trans (le_trans hx hN₀x) h
          have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast h1
          linarith
        have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
          rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
            ← Real.rpow_neg hn0.le]
        have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀) = 1 / ((n:ℝ)) ^ (σ₀ + 1) := by
          rw [hpow2, ← Real.rpow_add hn0,
            show -((2:ℕ):ℝ) + (1 - σ₀) = -(σ₀ + 1) by push_cast; ring,
            Real.rpow_neg hn0.le, one_div]
        apply le_of_eq
        rw [← hcollect]
        ring
  -- entire terms
  have hterm : ∀ n : ℕ, 1 ≤ n → Differentiable ℂ (fun s : ℂ =>
      (s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) := by
    intro n hn
    have hn0 : ((n:ℂ)) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    have hn10 : (((n + 1 : ℕ):ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    apply Differentiable.sub
    · apply Differentiable.mul
      · exact differentiable_id.sub (differentiable_const 1)
      · exact (Differentiable.neg differentiable_id).const_cpow (Or.inl hn0)
    · apply Differentiable.sub
      · exact ((differentiable_const 1).sub differentiable_id).const_cpow (Or.inl hn0)
      · exact ((differentiable_const 1).sub differentiable_id).const_cpow (Or.inl hn10)
  -- the tail: M-test on U
  have hgdiff : ∀ n : ℕ, DifferentiableOn ℂ (fun s : ℂ => if n < N₀ then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))) U := by
    intro n
    rcases Nat.lt_or_ge n N₀ with h | h
    · simp only [if_pos h]
      exact differentiableOn_const 0
    · simp only [if_neg (not_lt.mpr h)]
      exact (hterm n (le_trans (le_trans hx hN₀x) h)).differentiableOn
  have hgbound : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖if n < N₀ then 0 else
        ((w - 1) * ((n:ℂ)) ^ (-w)
          - (((n:ℂ)) ^ ((1:ℂ) - w) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - w)))‖
      ≤ (if n < N₀ then (0:ℝ) else
          4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) := by
    intro n w hwU
    rcases Nat.lt_or_ge n N₀ with h | h
    · rw [if_pos h, if_pos h, norm_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h)]
      exact hVbound n h w hwU
  have hTail : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, (if n < N₀ then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U :=
    Complex.differentiableOn_tsum_of_summable_norm husum hgdiff hUopen hgbound
  -- the head: a finite sum of entire functions
  have hHead : DifferentiableOn ℂ (fun s : ℂ => ∑ n ∈ range N₀, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U := by
    have hsum : DifferentiableOn ℂ (∑ n ∈ range N₀, fun s : ℂ => (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U := by
      apply DifferentiableOn.sum
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · simp only [if_pos h]
        exact differentiableOn_const 0
      · simp only [if_neg (not_lt.mpr h)]
        exact (hterm n (le_trans hx h)).differentiableOn
    have hfn : (fun s : ℂ => ∑ n ∈ range N₀, (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        = (∑ n ∈ range N₀, fun s : ℂ => (if n < x then 0 else
        ((s - 1) * ((n:ℂ)) ^ (-s)
          - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
      funext s
      rw [Finset.sum_apply]
    rw [hfn]
    exact hsum
  -- on U the full series splits as head + tail
  have hEqOn : ∀ s ∈ U, (∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
      = (∑ n ∈ range N₀, (if n < x then 0 else
          ((s - 1) * ((n:ℂ)) ^ (-s)
            - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
        + (∑' n : ℕ, (if n < N₀ then 0 else
          ((s - 1) * ((n:ℂ)) ^ (-s)
            - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) := by
    intro s hsU
    set V : ℕ → ℂ := fun n => (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)) with hV
    have hgsum : Summable (fun n : ℕ => if n < N₀ then 0 else V n) := by
      apply Summable.of_norm_bounded (g := fun n : ℕ => if n < N₀ then (0:ℝ) else
        4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - σ₀)) husum
      intro n
      exact hgbound n s hsU
    have hhsum : Summable (fun n : ℕ => if n < N₀ then (if n < x then 0 else V n) else 0) :=
      summable_of_ne_finset_zero (s := range N₀) (by
        intro n hn
        rw [Finset.mem_range] at hn
        rw [if_neg hn])
    have hsplit : ∀ n : ℕ, (if n < x then 0 else V n)
        = (if n < N₀ then (if n < x then 0 else V n) else 0)
          + (if n < N₀ then 0 else V n) := by
      intro n
      rcases Nat.lt_or_ge n N₀ with h | h
      · rw [if_pos h, if_pos h, add_zero]
      · have hnx : ¬ n < x := not_lt.mpr (le_trans hN₀x h)
        have hnN : ¬ n < N₀ := not_lt.mpr h
        rw [if_neg hnx, if_neg hnN, if_neg hnN, zero_add]
    calc ∑' n : ℕ, (if n < x then 0 else V n)
        = ∑' n : ℕ, ((if n < N₀ then (if n < x then 0 else V n) else 0)
            + (if n < N₀ then 0 else V n)) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < N₀ then (if n < x then 0 else V n) else 0))
            + (∑' n : ℕ, (if n < N₀ then 0 else V n)) := hhsum.tsum_add hgsum
      _ = (∑ n ∈ range N₀, (if n < x then 0 else V n))
            + (∑' n : ℕ, (if n < N₀ then 0 else V n)) := by
          congr 1
          rw [tsum_eq_sum (s := range N₀) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  -- assemble
  have hSum : DifferentiableOn ℂ (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else
      ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))) U :=
    DifferentiableOn.congr (hHead.add hTail) hEqOn
  exact hSum.differentiableAt (hUopen.mem_nhds hs₀U)

