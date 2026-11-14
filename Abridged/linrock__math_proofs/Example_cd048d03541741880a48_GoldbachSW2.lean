module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_cd048d03541741880a48_GoldbachSW2 ====
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
/-- **The E-series is differentiable on `Re s > 9/10`** (Siegel brick A2g-a2): with
    `|E(n)| ≤ C·n^{3/4}(1+log n)` and `E(0) = 0`, the series
    `s ↦ Σ' E(n)(n^{−s} − (n+1)^{−s})` is differentiable at every point of the
    half-plane — the analytic error part of the continuation `G`, via Mathlib's
    Weierstrass M-test `differentiableOn_tsum_of_summable_norm` on windows. -/
theorem eseries_differentiableAt (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) 
    (h_rpow_diff_le : ∀ (n : ℕ),
      1 ≤ n → ∀ (σ : ℝ), 0 ≤ σ → (↑n : ℝ) ^ (-σ) - (↑(n + 1) : ℝ) ^ (-σ) ≤ σ * (↑n : ℝ) ^ (-σ - 1))
    (h_cpow_diff_kernel_bound : ∀ (n : ℕ),
      1 ≤ n →
        ∀ (s : ℂ),
          0 < s.re →
            ‖(↑n : ℂ) ^ (-s) - (↑(n + 1) : ℂ) ^ (-s)‖ ≤
              ‖s‖ / s.re * ((↑n : ℝ) ^ (-s.re) - (↑(n + 1) : ℝ) ^ (-s.re)))
    :
    DifferentiableAt ℂ (fun s => ∑' n : ℕ,
      ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) s₀ := by
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
  -- the majorant
  set u : ℕ → ℝ := fun n => if n = 0 then 0 else
    C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) with hu
  have hmajsum : Summable (fun n : ℕ => (9 * C * R) * (1 / ((n:ℝ)) ^ (σ₀ + 1/8))) :=
    Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
  have husum : Summable u := by
    apply Summable.of_nonneg_of_le _ _ hmajsum
    · intro n
      rw [hu]
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp only [if_neg hn]
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          exact_mod_cast this
        have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1
          linarith
        positivity
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [hu]
        simp only [if_pos rfl]
        positivity
      · rw [hu]
        simp only [if_neg hn]
        have hn1 : (1:ℝ) ≤ (n:ℝ) := by
          have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
          exact_mod_cast this
        have hn0 : (0:ℝ) < (n:ℝ) := by linarith
        -- (1 + log n) ≤ 9 n^{1/8}
        have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
          have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
            Real.log_le_rpow_div hn0.le (by norm_num)
          have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
          have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
            Real.one_le_rpow hn1 (by norm_num)
          linarith [h1, h2.le, h2.ge, h3]
        -- collect exponents: 3/4 + 1/8 − σ₀ − 1 = −(σ₀ + 1/8)
        have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-σ₀ - 1)
            = ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
          ring_nf
        have hfinal : C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
            ≤ (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by
          calc C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
              ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8))) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) := by
                apply mul_le_mul_of_nonneg_right _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ hC0
                apply mul_le_mul_of_nonneg_left hlogbound (by positivity)
            _ = (9 * C * R) * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-σ₀ - 1)) := by
                ring
            _ = (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := by rw [hcollect]
        calc C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1))
            ≤ (9 * C * R) * ((n:ℝ)) ^ (-(σ₀ + 1/8)) := hfinal
          _ = (9 * C * R) * (1 / ((n:ℝ)) ^ (σ₀ + 1/8)) := by
              rw [Real.rpow_neg hn0.le]
              ring
  -- pointwise bounds on U
  have hbound : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w))‖ ≤ u n := by
    intro n w hw
    obtain ⟨hwre, hwball⟩ := hw
    have hwre' : σ₀ < w.re := hwre
    have hwσ : (0:ℝ) < w.re := by linarith
    have hwnorm : ‖w‖ ≤ R := by
      rw [Metric.mem_ball, dist_zero_right] at hwball
      linarith
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero, hu, if_pos rfl]
      exact le_refl 0
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
      have hn0 : (0:ℝ) < (n:ℝ) := by linarith
      rw [hu]
      simp only [if_neg hn]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 := hE n hn1
      have h2 := h_cpow_diff_kernel_bound n hn1 w hwσ
      have h3 := h_rpow_diff_le n hn1 w.re hwσ.le
      have hker : ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖ ≤ R * ((n:ℝ)) ^ (-σ₀ - 1) := by
        have hstep : (‖w‖ / w.re) * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re))
            ≤ (‖w‖ / w.re) * (w.re * (n : ℝ) ^ (-w.re - 1)) := by
          apply mul_le_mul_of_nonneg_left h3 (by positivity)
        have hsimp : (‖w‖ / w.re) * (w.re * (n : ℝ) ^ (-w.re - 1))
            = ‖w‖ * (n : ℝ) ^ (-w.re - 1) := by
          field_simp
        have hmono : ((n:ℝ)) ^ (-w.re - 1) ≤ ((n:ℝ)) ^ (-σ₀ - 1) := by
          apply Real.rpow_le_rpow_of_exponent_le hn1r
          linarith
        calc ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖
            ≤ (‖w‖ / w.re) * ((n : ℝ) ^ (-w.re) - ((n + 1 : ℕ) : ℝ) ^ (-w.re)) := h2
          _ ≤ ‖w‖ * ((n:ℝ)) ^ (-w.re - 1) := by
              rw [← hsimp]
              exact hstep
          _ ≤ R * ((n:ℝ)) ^ (-σ₀ - 1) := by
              apply mul_le_mul hwnorm hmono (by positivity) hR0.le
      have hEnn : (0:ℝ) ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) := by
        have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
          have := Real.log_nonneg hn1r
          linarith
        positivity
      calc |E n| * ‖((n:ℂ)) ^ (-w) - (((n + 1 : ℕ):ℂ)) ^ (-w)‖
          ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) :=
            mul_le_mul h1 hker (norm_nonneg _) hEnn
        _ = C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)) * (R * ((n:ℝ)) ^ (-σ₀ - 1)) := by
            ring
  -- termwise differentiability on U
  have hdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s => ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) U := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul]
      exact differentiableOn_const 0
    · have hn0 : ((n:ℂ)) ≠ 0 := by exact_mod_cast hn
      have hn10 : (((n + 1 : ℕ):ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      apply DifferentiableOn.const_mul
      apply DifferentiableOn.sub
      · exact ((Differentiable.neg differentiable_id).const_cpow
          (Or.inl hn0)).differentiableOn
      · exact ((Differentiable.neg differentiable_id).const_cpow
          (Or.inl hn10)).differentiableOn
  -- assemble
  have hDon := Complex.differentiableOn_tsum_of_summable_norm husum hdiff hUopen hbound
  exact (hDon.differentiableAt (hUopen.mem_nhds hs₀U))

