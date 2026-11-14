module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_d8392f3a0fcb3d659397_GoldbachSW2 ====
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


set_option linter.unusedVariables false in
/-- **The √-growth Abel tail** (Siegel brick A2e-ii-a): if the partial sums of `k`
    satisfy `|K(t)| ≤ B(√t+1)`, then `|Σ_{y<d≤z} k(d)/d| ≤ 7B/√y` for `1 ≤ y ≤ z` —
    the tail engine for the pole-free convolution side of the Goldfeld product. -/
theorem abel_tail_sqrt (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    (y z : ℕ) (hy1 : 1 ≤ y) (hyz : y ≤ z) 
    (h_abel_window : ∀ (g : ℕ → ℝ) (y z : ℕ),
      y ≤ z →
        ∑ d ∈ Finset.Icc (y + 1) z, g d / (↑d : ℝ) =
          ∑ d ∈ Finset.Icc (y + 1) z,
                (∑ n ∈ Finset.Icc 1 d, g n) * (1 / (↑d : ℝ) - 1 / ((↑d : ℝ) + 1)) +
              (∑ n ∈ Finset.Icc 1 z, g n) / ((↑z : ℝ) + 1) -
            (∑ n ∈ Finset.Icc 1 y, g n) / ((↑y : ℝ) + 1))
    (h_sum_three_half_tail_sharp : ∀ (y : ℕ),
      1 ≤ y →
        ∀ (z : ℕ),
          y ≤ z → ∑ d ∈ Finset.Icc (y + 1) z, 1 / ((↑d : ℝ) * √(↑d : ℝ)) ≤ 2 / √(↑y : ℝ) - 2 / √(↑z : ℝ))
    (h_sqrt_boundary_le : ∀ (t : ℕ), 1 ≤ t → (√(↑t : ℝ) + 1) / ((↑t : ℝ) + 1) ≤ 2 / √(↑t : ℝ))
    (h_telescope_kernel : ∀ (y z : ℕ),
      y ≤ z →
        ∑ d ∈ Finset.Icc (y + 1) z, (1 / (↑d : ℝ) - 1 / ((↑d : ℝ) + 1)) =
          1 / ((↑y : ℝ) + 1) - 1 / ((↑z : ℝ) + 1))
    :
    |∑ d ∈ Icc (y + 1) z, k d / d| ≤ 7 * B / Real.sqrt y := by
  have hB : 0 ≤ B := by
    have h0 := hK 0
    simp at h0
    linarith [abs_nonneg (∑ n ∈ Icc 1 0, k n), h0]
  have hy0 : (0:ℝ) < y := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsyz : Real.sqrt y ≤ Real.sqrt z := Real.sqrt_le_sqrt (by exact_mod_cast hyz)
  have hsz : (0:ℝ) < Real.sqrt z := lt_of_lt_of_le hsy hsyz
  rw [h_abel_window k y z hyz]
  -- termwise: |K(d)|·κ_d ≤ B/(d√d) + B·κ_d
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ B * ((1:ℝ) / (d * Real.sqrt d)) + B * ((1:ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast this
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
    have hsqd : Real.sqrt d * Real.sqrt d = (d : ℝ) := Real.mul_self_sqrt hd0.le
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    have hkerid : (1 : ℝ) / d - 1 / (d + 1) = 1 / ((d : ℝ) * (d + 1)) := by
      field_simp
      ring
    have hsdker : Real.sqrt d * ((1:ℝ) / d - 1 / (d + 1)) ≤ 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [hkerid,
        show Real.sqrt d * ((1:ℝ) / ((d:ℝ) * (d + 1)))
          = Real.sqrt d / ((d:ℝ) * (d + 1)) from by ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hsqd, hd0, hsd]
    rw [abs_mul, abs_of_nonneg hker]
    calc |∑ n ∈ Icc 1 d, k n| * ((1:ℝ) / d - 1 / (d + 1))
        ≤ (B * (Real.sqrt d + 1)) * ((1:ℝ) / d - 1 / (d + 1)) :=
          mul_le_mul_of_nonneg_right (hK d) hker
      _ = B * (Real.sqrt d * ((1:ℝ) / d - 1 / (d + 1)))
          + B * ((1:ℝ) / d - 1 / (d + 1)) := by ring
      _ ≤ B * ((1:ℝ) / (d * Real.sqrt d)) + B * ((1:ℝ) / d - 1 / (d + 1)) := by
          have := mul_le_mul_of_nonneg_left hsdker hB
          linarith
  -- the summed middle piece
  have hmid : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
      ≤ B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)) := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, (B * ((1:ℝ) / (d * Real.sqrt d))
          + B * ((1:ℝ) / d - 1 / (d + 1))) := Finset.sum_le_sum hterm
      _ = B * (∑ d ∈ Icc (y + 1) z, (1:ℝ) / (d * Real.sqrt d))
          + B * (∑ d ∈ Icc (y + 1) z, ((1:ℝ) / d - 1 / (d + 1))) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ B * (2 / Real.sqrt y - 2 / Real.sqrt z)
          + B * (1 / ((y:ℝ) + 1) - 1 / ((z:ℝ) + 1)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (h_sum_three_half_tail_sharp y hy1 z hyz) hB
          · rw [h_telescope_kernel y z hyz]
      _ ≤ B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)) := by
          have h1 : (0:ℝ) ≤ 2 / Real.sqrt z := by positivity
          have h2 : (0:ℝ) ≤ 1 / ((z:ℝ) + 1) := by positivity
          nlinarith [hB, h1, h2]
  -- boundaries
  have hbz : |(∑ n ∈ Icc 1 z, k n) / ((z:ℝ) + 1)| ≤ 2 * B / Real.sqrt y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
    have h1 : |∑ n ∈ Icc 1 z, k n| / ((z:ℝ) + 1) ≤ B * ((Real.sqrt z + 1) / ((z:ℝ) + 1)) := by
      rw [mul_div_assoc'] at *
      apply div_le_div_of_nonneg_right (hK z) (by positivity)
    have h2 : (Real.sqrt z + 1) / ((z:ℝ) + 1) ≤ 2 / Real.sqrt z :=
      h_sqrt_boundary_le z (by omega)
    have h3 : (2:ℝ) / Real.sqrt z ≤ 2 / Real.sqrt y := by
      apply div_le_div_of_nonneg_left (by norm_num) hsy hsyz
    calc |∑ n ∈ Icc 1 z, k n| / ((z:ℝ) + 1)
        ≤ B * ((Real.sqrt z + 1) / ((z:ℝ) + 1)) := h1
      _ ≤ B * (2 / Real.sqrt y) := by
          apply mul_le_mul_of_nonneg_left _ hB
          linarith
      _ = 2 * B / Real.sqrt y := by ring
  have hby : |(∑ n ∈ Icc 1 y, k n) / ((y:ℝ) + 1)| ≤ 2 * B / Real.sqrt y := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
    have h1 : |∑ n ∈ Icc 1 y, k n| / ((y:ℝ) + 1) ≤ B * ((Real.sqrt y + 1) / ((y:ℝ) + 1)) := by
      rw [mul_div_assoc'] at *
      apply div_le_div_of_nonneg_right (hK y) (by positivity)
    have h2 : (Real.sqrt y + 1) / ((y:ℝ) + 1) ≤ 2 / Real.sqrt y :=
      h_sqrt_boundary_le y hy1
    calc |∑ n ∈ Icc 1 y, k n| / ((y:ℝ) + 1)
        ≤ B * ((Real.sqrt y + 1) / ((y:ℝ) + 1)) := h1
      _ ≤ B * (2 / Real.sqrt y) := mul_le_mul_of_nonneg_left h2 hB
      _ = 2 * B / Real.sqrt y := by ring
  -- assemble: mid + boundaries, with 1/(y+1) ≤ 1/√y
  have hy1r : (1:ℝ) / ((y:ℝ) + 1) ≤ 1 / Real.sqrt y := by
    apply div_le_div_of_nonneg_left one_pos.le hsy
    nlinarith [Real.mul_self_sqrt hy0.le,
      Real.one_le_sqrt.mpr (by exact_mod_cast hy1 : (1:ℝ) ≤ (y:ℝ)), hsy]
  set M := ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * ((1 : ℝ) / d - 1 / (d + 1)) with hM
  set Bz := (∑ n ∈ Icc 1 z, k n) / ((z:ℝ) + 1) with hBz
  set By := (∑ n ∈ Icc 1 y, k n) / ((y:ℝ) + 1) with hBy
  have htri : |M + Bz - By| ≤ |M| + |Bz| + |By| := by
    have h1 := abs_add_le M Bz
    have h2 := abs_add_le (M + Bz) (-By)
    rw [abs_neg, ← sub_eq_add_neg] at h2
    linarith
  calc |M + Bz - By| ≤ |M| + |Bz| + |By| := htri
    _ ≤ (B * (2 / Real.sqrt y) + B * (1 / ((y:ℝ) + 1)))
        + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [hmid, hbz, hby]
    _ ≤ 7 * B / Real.sqrt y := by
        have hstep : B * (1 / ((y:ℝ) + 1)) ≤ B * (1 / Real.sqrt y) :=
          mul_le_mul_of_nonneg_left hy1r hB
        have hexp : B * (2 / Real.sqrt y) = 2 * B / Real.sqrt y := by ring
        have hexp2 : B * (1 / Real.sqrt y) = B / Real.sqrt y := by ring
        have hexp3 : 7 * B / Real.sqrt y = 7 * (B / Real.sqrt y) := by ring
        have hexp4 : 2 * B / Real.sqrt y = 2 * (B / Real.sqrt y) := by ring
        linarith [hstep, hexp, hexp2, hexp3, hexp4]

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/

