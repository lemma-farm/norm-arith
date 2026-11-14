module

public import Mathlib

-- ==== Examples.linrock__math_proofs.Examples.Example_0c631e8036569a4a2774_GoldbachSW2 ====
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
/-- A bare function packaged as an arithmetic function (forcing the value 0 at 0). -/
noncomputable def toArith (g : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else g n, by simp⟩

/-- **The Dirichlet hyperbola identity** (Siegel brick A2a): for any split `y ≤ N`,
    `Σ_{n≤N}(f⋆g)(n) = Σ_{d≤y} f(d)·G(N/d) + Σ_{e≤N/(y+1)} g(e)·(F(N/e) − F(y))` —
    the exact identity behind the coefficient asymptotic `A(x) = λx + O(Q^c x^{4/5})`. -/
axiom hyperbola_identity (f g : ArithmeticFunction ℝ) (N y : ℕ) (hy : y ≤ N) :
    ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ d ∈ Icc 1 y, f d * (∑ e ∈ Icc 1 (N / d), g e)
        + ∑ e ∈ Icc 1 (N / (y + 1)),
            g e * ((∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d)

/-- Convolution values are divisor-counted (Siegel brick A2e-iii-a1): for 1-bounded
    inputs, `|(k₁⋆k₂)(n)| ≤ τ(n)` where `τ(n) = #divisorsAntidiagonal(n)`. -/
axiom conv_value_le_tau (k₁ k₂ : ℕ → ℝ) (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (n : ℕ) :
    |(toArith k₁ * toArith k₂) n| ≤ ((n.divisorsAntidiagonal).card : ℝ)

/-- **τ partial sums** (Siegel brick A2e-iii-a3): `Σ_{d≤y} τ(d) ≤ y(1 + log y)`. -/
axiom sum_tau_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) ≤ (y : ℝ) * (1 + Real.log y)
/-- **τ/√ partial sums** (Siegel brick A2e-iii-a4):
    `Σ_{d≤y} τ(d)/√d ≤ 2√y(1 + log y)` — on each antidiagonal `p₁p₂ = d`. -/
axiom sum_tau_div_sqrt_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      ≤ 2 * Real.sqrt y * (1 + Real.log y)
/-- **The Goldfeld coefficient asymptotic** (Siegel brick A2e-iii, the analytic capstone
    of A2): with `h := 1⋆g₁` carrying the mean `L₁` and `k := g₂⋆(g₁g₂)` carrying the
    mean `Lk` (√-bounded partial sums `≤ B(√t+1)`),
    `|Σ_{n≤N} a(n) − L₁·Lk·N| ≤ 30(1+q₁)(1+B)·√N·√√N·(1+log N)` for `N ≥ 4` —
    the `A(x) = λx + O(Q^c x^{3/4+ε})` input of Goldfeld's lemma, with
    `λ = L₁·Lk` and the split at `y = ⌊√N⌋`. -/
theorem quad_coeff_asymptotic (g₁ g₂ : ℕ → ℝ) (q₁ B L₁ Lk : ℝ)
    (h1b : ∀ n, |g₁ n| ≤ 1) (h2b : ∀ n, |g₂ n| ≤ 1)
    (hL₁ : ∀ y : ℕ, |L₁ - ∑ d ∈ Icc 1 y, g₁ d / d| ≤ 2 * q₁ / (y + 1))
    (hq₁ : 0 ≤ q₁)
    (hH : ∀ M : ℕ, 1 ≤ M →
      |∑ n ∈ Icc 1 M, (toArith (fun _ => (1:ℝ)) * toArith g₁) n - L₁ * M|
        ≤ (1 + 4 * q₁) * (Real.sqrt M + 1))
    (hKb : ∀ t : ℕ, |∑ n ∈ Icc 1 t, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) n|
        ≤ B * (Real.sqrt t + 1))
    (hLk : ∀ y : ℕ, 1 ≤ y →
      |Lk - ∑ d ∈ Icc 1 y, (toArith g₂ * toArith (fun m => g₁ m * g₂ m)) d / d|
        ≤ 7 * B / Real.sqrt y)
    (N : ℕ) (hN : 4 ≤ N) :
    |∑ n ∈ Icc 1 N, (toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
        * toArith (fun m => g₁ m * g₂ m)) n - L₁ * Lk * N|
      ≤ 30 * (1 + q₁) * (1 + B)
        * (Real.sqrt N * Real.sqrt (Real.sqrt N) * (1 + Real.log N)) := by
  have hB : 0 ≤ B := by
    have h0 := hKb 0
    rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
      Finset.sum_empty, abs_zero, Nat.cast_zero, Real.sqrt_zero] at h0
    linarith
  have hN1 : 1 ≤ N := by omega
  have hNr : (4:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  -- names
  set h : ArithmeticFunction ℝ := toArith (fun _ => (1:ℝ)) * toArith g₁ with hh
  set k : ArithmeticFunction ℝ := toArith g₂ * toArith (fun m => g₁ m * g₂ m) with hk
  have hregroup : toArith (fun _ => (1:ℝ)) * toArith g₁ * toArith g₂
      * toArith (fun m => g₁ m * g₂ m) = k * h := by
    rw [hh, hk, mul_assoc]
    exact mul_comm _ _
  rw [hregroup]
  set y : ℕ := Nat.sqrt N with hy
  have hy2 : 2 ≤ y := by
    rw [hy]
    exact Nat.le_sqrt.mpr (by omega)
  have hy1 : 1 ≤ y := by omega
  have hyN : y ≤ N := Nat.sqrt_le_self N
  rw [hyperbola_identity k h N y hyN]
  -- ===== √-conversions =====
  have hsN : (0:ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by linarith)
  have hsqN : Real.sqrt N * Real.sqrt N = (N:ℝ) := Real.mul_self_sqrt (by linarith)
  have hssN : (0:ℝ) < Real.sqrt (Real.sqrt N) := Real.sqrt_pos.mpr hsN
  have hsqsN : Real.sqrt (Real.sqrt N) * Real.sqrt (Real.sqrt N) = Real.sqrt N :=
    Real.mul_self_sqrt hsN.le
  have hyle : (y : ℝ) ≤ Real.sqrt N := by
    rw [hy]
    exact Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' N)
  have hsyle : Real.sqrt y ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt hyle
  have hy1r : (1:ℝ) ≤ (y:ℝ) := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr (by linarith)
  -- √N ≤ 2y (from ⌊√N⌋ ≥ √N − 1 ≥ √N/2 for N ≥ 4)
  have h2y : Real.sqrt N ≤ 2 * (y : ℝ) := by
    have hlt := Nat.lt_succ_sqrt' N
    have hcast : (N : ℝ) < ((y : ℝ) + 1) ^ 2 := by
      rw [hy]
      push_cast
      exact_mod_cast hlt
    have hsylt : Real.sqrt N < (y:ℝ) + 1 := by
      nlinarith [hcast, hsqN, hsN]
    linarith [hy1r]
  -- N/√y ≤ √2·√N·√√N — via √y ≥ √√N/√2, i.e. 2y ≥ √N → √(2y) ≥ √√N
  have hNdivsy : (N:ℝ) / Real.sqrt y ≤ 2 * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by
    rw [div_le_iff₀ hsy]
    -- √√N ≤ √(2y) = √2·√y, then N = (√N√√N)·√√N ≤ (√N√√N)·√2√y ≤ 2(√N√√N)√y
    have h1 : Real.sqrt (Real.sqrt N) ≤ Real.sqrt 2 * Real.sqrt y := by
      calc Real.sqrt (Real.sqrt N) ≤ Real.sqrt (2 * y) := Real.sqrt_le_sqrt (by
            push_cast
            linarith [h2y])
        _ = Real.sqrt 2 * Real.sqrt y := Real.sqrt_mul (by norm_num) _
    have hs2le : Real.sqrt 2 ≤ 2 := by
      have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := Real.mul_self_sqrt (by norm_num)
      nlinarith [Real.sqrt_nonneg 2]
    have hss1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt N) := by
      apply Real.one_le_sqrt.mpr
      have h2s : (2:ℝ) ≤ Real.sqrt N := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      linarith
    have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg hsN.le hssN.le)
    nlinarith [hmul, hsqN, hsqsN, hs2le,
      mul_nonneg (mul_nonneg hsN.le hssN.le) hsy.le]
  -- ===== value bounds =====
  have hg12b : ∀ n, |g₁ n * g₂ n| ≤ 1 := by
    intro n
    rw [abs_mul]
    calc |g₁ n| * |g₂ n| ≤ 1 * 1 := mul_le_mul (h1b n) (h2b n) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have honeb : ∀ n : ℕ, |(fun _ : ℕ => (1:ℝ)) n| ≤ 1 := fun n => by norm_num
  have hkτ : ∀ n, |k n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
    intro n
    rw [hk]
    exact conv_value_le_tau g₂ (fun m => g₁ m * g₂ m) h2b hg12b n
  have hhτ : ∀ n, |h n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
    intro n
    rw [hh]
    exact conv_value_le_tau (fun _ => (1:ℝ)) g₁ honeb h1b n
  have hL1b : |L₁| ≤ 1 + q₁ := by
    have h1 := hL₁ 1
    have hS1 : ∑ d ∈ Icc 1 1, g₁ d / d = g₁ 1 := by
      rw [show (Icc 1 1 : Finset ℕ) = {1} from rfl, Finset.sum_singleton]
      norm_num
    rw [hS1] at h1
    have habs := abs_add_le (L₁ - g₁ 1) (g₁ 1)
    simp only [sub_add_cancel] at habs
    have hc : ((1:ℕ):ℝ) + 1 = 2 := by norm_num
    rw [hc] at h1
    have hq2 : 2 * q₁ / 2 = q₁ := by ring
    linarith [habs, h1, h1b 1, hq2.le, hq2.ge]
  -- ===== M' facts =====
  set M' : ℕ := N / (y + 1) with hM'
  have hyy : y * y ≤ N := by
    have h := Nat.sqrt_le' N
    rw [pow_two] at h
    rw [hy]
    exact h
  have hyN2 : y + 1 ≤ N := by nlinarith [hy2, hyy]
  have hM'1 : 1 ≤ M' := by
    rw [hM', Nat.le_div_iff_mul_le (by omega : 0 < y + 1)]
    omega
  have hM'le : (M' : ℝ) ≤ Real.sqrt N := by
    have h1 : ((M' : ℕ) : ℝ) ≤ (N : ℝ) / ((y:ℝ) + 1) := by
      rw [hM']
      have := Nat.cast_div_le (α := ℝ) (m := N) (n := y + 1)
      push_cast at this
      exact this
    have hylt : Real.sqrt N < (y:ℝ) + 1 := by
      have hlt := Nat.lt_succ_sqrt' N
      have hcast : (N : ℝ) < ((y : ℝ) + 1) ^ 2 := by
        rw [hy]
        push_cast
        exact_mod_cast hlt
      nlinarith [hsqN, hsN]
    have h2 : (N : ℝ) / ((y:ℝ) + 1) ≤ Real.sqrt N := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hsqN, hylt, hsN]
    linarith
  have hsM'le : Real.sqrt M' ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_le_sqrt hM'le
  have hlogy : Real.log y ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hy1 : (0:ℝ) < (y:ℝ))
    exact_mod_cast hyN
  have hlogM' : Real.log M' ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hM'1 : (0:ℝ) < (M':ℝ))
    have : M' ≤ N := Nat.div_le_self N (y + 1)
    exact_mod_cast this
  have hlogN0 : (0:ℝ) ≤ Real.log N := Real.log_nonneg (by linarith)
  have hlogy1 : 1 + Real.log y ≤ 1 + Real.log N := by linarith
  have hlogy0 : (0:ℝ) ≤ 1 + Real.log y := by
    have := Real.log_nonneg (by exact_mod_cast hy1 : (1:ℝ) ≤ (y:ℝ))
    linarith
  have hlogM'0 : (0:ℝ) ≤ 1 + Real.log M' := by
    have := Real.log_nonneg (by exact_mod_cast hM'1 : (1:ℝ) ≤ (M':ℝ))
    linarith
  have hlogM'1 : 1 + Real.log M' ≤ 1 + Real.log N := by linarith
  have hsqrtdiv : ∀ d : ℕ, 1 ≤ d → Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt d := by
    intro d hd1
    calc Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt ((N : ℝ) / d) :=
          Real.sqrt_le_sqrt Nat.cast_div_le
      _ = Real.sqrt N / Real.sqrt d := Real.sqrt_div (Nat.cast_nonneg N) d
  -- ===== HEAD =====
  set Sk : ℝ := ∑ d ∈ Icc 1 y, k d / d with hSk
  have hSkLk : |Lk - Sk| ≤ 7 * B / Real.sqrt y := by
    rw [hSk, hk]
    exact hLk y hy1
  have hhead_eq : ∑ d ∈ Icc 1 y, k d * (∑ e ∈ Icc 1 (N / d), h e)
      = L₁ * (∑ d ∈ Icc 1 y, k d * ((N / d : ℕ) : ℝ))
        + ∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    ring
  have hfloor_eq : ∑ d ∈ Icc 1 y, k d * ((N / d : ℕ) : ℝ)
      = (N : ℝ) * Sk - ∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) := by
    rw [hSk, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : ((d:ℝ)) ≠ 0 := by
      have : (0:ℝ) < d := by exact_mod_cast hd1
      linarith
    field_simp
    ring
  have hfrac_le : |∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
      ≤ (y:ℝ) * (1 + Real.log y) := by
    calc |∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
          have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
          rw [abs_mul]
          have hfr0 : (0:ℝ) ≤ (N : ℝ) / d - ((N / d : ℕ) : ℝ) := by
            rw [sub_nonneg]
            exact Nat.cast_div_le
          have hfr1 : (N : ℝ) / d - ((N / d : ℕ) : ℝ) ≤ 1 := by
            have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
              rw [div_lt_iff₀ hd0]
              have hnat : N < (N / d + 1) * d := by
                have hexp : (N / d + 1) * d = d * (N / d) + d := by ring
                rw [hexp]
                have h1 := Nat.div_add_mod N d
                have h2 := Nat.mod_lt N (show 0 < d by omega)
                omega
              exact_mod_cast hnat
            linarith
          rw [abs_of_nonneg hfr0]
          have hτ1 : (1:ℝ) ≤ ((d.divisorsAntidiagonal).card : ℝ) := by
            have hmem : ((1:ℕ), d) ∈ d.divisorsAntidiagonal := by
              rw [Nat.mem_divisorsAntidiagonal]
              exact ⟨one_mul d, by omega⟩
            have hpos : 0 < (d.divisorsAntidiagonal).card := Finset.card_pos.mpr ⟨_, hmem⟩
            exact_mod_cast hpos
          nlinarith [hkτ d, hfr0, hfr1, abs_nonneg (k d), hτ1]
      _ ≤ (y:ℝ) * (1 + Real.log y) := sum_tau_le y hy1
  have hε_le : |∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
      ≤ (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
          + 2 * (y:ℝ) * (1 + Real.log y)) := by
    have hterm : ∀ d ∈ Icc 1 y, |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
        ≤ (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt d)
            + ((d.divisorsAntidiagonal).card : ℝ)) := by
      intro d hd
      obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
      have hNd1 : 1 ≤ N / d := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
        have : d ≤ N := le_trans hdy hyN
        omega
      have hεd := hH (N / d) hNd1
      have hq4 : (0:ℝ) ≤ 1 + 4 * q₁ := by linarith
      rw [show |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
          = |k d| * |(∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)| from abs_mul _ _]
      calc |k d| * |(∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)|
          ≤ ((d.divisorsAntidiagonal).card : ℝ)
            * ((1 + 4 * q₁) * (Real.sqrt ((N / d : ℕ) : ℝ) + 1)) :=
            mul_le_mul (hkτ d) hεd (abs_nonneg _) (Nat.cast_nonneg _)
        _ ≤ ((d.divisorsAntidiagonal).card : ℝ)
            * ((1 + 4 * q₁) * (Real.sqrt N / Real.sqrt d + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hq4
            linarith [hsqrtdiv d hd1]
        _ = (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt d)
            + ((d.divisorsAntidiagonal).card : ℝ)) := by ring
    calc |∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 y, |k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 y, (1 + 4 * q₁) * (((d.divisorsAntidiagonal).card : ℝ)
            * (Real.sqrt N / Real.sqrt d) + ((d.divisorsAntidiagonal).card : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ (1 + 4 * q₁) * (Real.sqrt N * (2 * Real.sqrt y * (1 + Real.log y))
            + (y:ℝ) * (1 + Real.log y)) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hsplit : ∑ d ∈ Icc 1 y, (((d.divisorsAntidiagonal).card : ℝ)
              * (Real.sqrt N / Real.sqrt d) + ((d.divisorsAntidiagonal).card : ℝ))
              = Real.sqrt N * (∑ d ∈ Icc 1 y,
                  ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d)
                + ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro d _
            ring
          rw [hsplit]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_tau_div_sqrt_le y hy1) hsN.le)
            (sum_tau_le y hy1)
      _ ≤ (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hy0' : (0:ℝ) ≤ (y:ℝ) := by positivity
          nlinarith [hlogy0, hy0']
  -- ===== TAIL =====
  have htail_le : |∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
      ≤ 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
          + 2 * (M':ℝ) * (1 + Real.log M')) := by
    have hterm : ∀ e ∈ Icc 1 M', |h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
        ≤ 2 * B * (((e.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt e)
            + ((e.divisorsAntidiagonal).card : ℝ)) := by
      intro e he
      obtain ⟨he1, heM⟩ := Finset.mem_Icc.mp he
      have hyNe : y ≤ N / e := by
        rw [Nat.le_div_iff_mul_le (by omega : 0 < e)]
        have h1 : e * (y + 1) ≤ N := by
          rw [hM'] at heM
          have := (Nat.le_div_iff_mul_le (by omega : 0 < y + 1)).mp heM
          omega
        nlinarith [h1]
      have hKdiff : |(∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d|
          ≤ 2 * B * (Real.sqrt ((N / e : ℕ) : ℝ) + 1) := by
        have h1 := hKb (N / e)
        have h2 := hKb y
        have hsymono : Real.sqrt ((y:ℕ) : ℝ) ≤ Real.sqrt ((N / e : ℕ) : ℝ) := by
          apply Real.sqrt_le_sqrt
          exact_mod_cast hyNe
        have htri := abs_add_le (∑ d ∈ Icc 1 (N / e), k d) (-(∑ d ∈ Icc 1 y, k d))
        rw [abs_neg, ← sub_eq_add_neg] at htri
        have hprod := mul_le_mul_of_nonneg_left hsymono hB
        linarith [htri, h1, h2, hprod]
      rw [abs_mul]
      have hB2 : (0:ℝ) ≤ 2 * B := by linarith
      calc |h e| * |(∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d|
          ≤ ((e.divisorsAntidiagonal).card : ℝ)
            * (2 * B * (Real.sqrt ((N / e : ℕ) : ℝ) + 1)) :=
            mul_le_mul (hhτ e) hKdiff (abs_nonneg _) (Nat.cast_nonneg _)
        _ ≤ ((e.divisorsAntidiagonal).card : ℝ)
            * (2 * B * (Real.sqrt N / Real.sqrt e + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ hB2
            linarith [hsqrtdiv e he1]
        _ = 2 * B * (((e.divisorsAntidiagonal).card : ℝ) * (Real.sqrt N / Real.sqrt e)
            + ((e.divisorsAntidiagonal).card : ℝ)) := by ring
    calc |∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)|
        ≤ ∑ e ∈ Icc 1 M', |h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e ∈ Icc 1 M', 2 * B * (((e.divisorsAntidiagonal).card : ℝ)
            * (Real.sqrt N / Real.sqrt e) + ((e.divisorsAntidiagonal).card : ℝ)) :=
          Finset.sum_le_sum hterm
      _ ≤ 2 * B * (Real.sqrt N * (2 * Real.sqrt M' * (1 + Real.log M'))
            + (M':ℝ) * (1 + Real.log M')) := by
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hsplit : ∑ e ∈ Icc 1 M', (((e.divisorsAntidiagonal).card : ℝ)
              * (Real.sqrt N / Real.sqrt e) + ((e.divisorsAntidiagonal).card : ℝ))
              = Real.sqrt N * (∑ e ∈ Icc 1 M',
                  ((e.divisorsAntidiagonal).card : ℝ) / Real.sqrt e)
                + ∑ e ∈ Icc 1 M', ((e.divisorsAntidiagonal).card : ℝ) := by
            rw [Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro e _
            ring
          rw [hsplit]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (sum_tau_div_sqrt_le M' hM'1) hsN.le)
            (sum_tau_le M' hM'1)
      _ ≤ 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          have hM'0 : (0:ℝ) ≤ (M':ℝ) := by positivity
          nlinarith [hlogM'0, hM'0]
  -- ===== ASSEMBLE =====
  rw [hhead_eq, hfloor_eq]
  set FR := ∑ d ∈ Icc 1 y, k d * ((N : ℝ) / d - ((N / d : ℕ) : ℝ)) with hFRd
  set T2 := ∑ d ∈ Icc 1 y, k d * ((∑ e ∈ Icc 1 (N / d), h e) - L₁ * ((N / d : ℕ) : ℝ)) with hT2d
  set TL := ∑ e ∈ Icc 1 M', h e * ((∑ d ∈ Icc 1 (N / e), k d) - ∑ d ∈ Icc 1 y, k d) with hTLd
  have hrw : L₁ * ((N : ℝ) * Sk - FR) + T2 + TL - L₁ * Lk * N
      = -(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL := by ring
  rw [hrw]
  have hb1 : |L₁ * ((N:ℝ) * (Lk - Sk))|
      ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N))) := by
    rw [abs_mul, abs_mul]
    have hNpos : (0:ℝ) ≤ (N:ℝ) := by positivity
    have h1 : |(N:ℝ)| * |Lk - Sk| ≤ (N:ℝ) * (7 * B / Real.sqrt y) := by
      rw [abs_of_nonneg hNpos]
      exact mul_le_mul_of_nonneg_left hSkLk hNpos
    have h3 : (N:ℝ) * (7 * B / Real.sqrt y)
        ≤ 14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by
      have h2 : (N:ℝ) * (7 * B / Real.sqrt y) = 7 * B * ((N:ℝ) / Real.sqrt y) := by ring
      rw [h2]
      calc 7 * B * ((N:ℝ) / Real.sqrt y)
          ≤ 7 * B * (2 * (Real.sqrt N * Real.sqrt (Real.sqrt N))) :=
            mul_le_mul_of_nonneg_left hNdivsy (by linarith)
        _ = 14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)) := by ring
    calc |L₁| * (|(N:ℝ)| * |Lk - Sk|) ≤ (1 + q₁) * (|(N:ℝ)| * |Lk - Sk|) :=
        mul_le_mul_of_nonneg_right hL1b (by positivity)
      _ ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N))) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith [h1, h3]
  have hb2 : |L₁ * FR| ≤ (1 + q₁) * ((y:ℝ) * (1 + Real.log y)) := by
    rw [abs_mul]
    apply mul_le_mul hL1b hfrac_le (abs_nonneg _) (by linarith)
  have htri4 : |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
      ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := by
    have t1 := abs_add_le (-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) T2
    have t2 := abs_add_le ((-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) + T2) TL
    have t3 := abs_add_le (-(L₁ * ((N:ℝ) * (Lk - Sk)))) (-(L₁ * FR))
    rw [abs_neg, abs_neg, ← sub_eq_add_neg] at t3
    calc |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
        ≤ |(-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR) + T2| + |TL| := t2
      _ ≤ |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR| + |T2| + |TL| := by linarith [t1]
      _ ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := by linarith [t3]
  set U := Real.sqrt N * Real.sqrt (Real.sqrt N) * (1 + Real.log N) with hUd
  have hlogNfac : (1:ℝ) ≤ 1 + Real.log N := by linarith
  have hU0 : (0:ℝ) < U := by
    rw [hUd]
    have : (0:ℝ) < 1 + Real.log N := by linarith
    positivity
  have hss1 : (1:ℝ) ≤ Real.sqrt (Real.sqrt N) := by
    apply Real.one_le_sqrt.mpr
    apply Real.one_le_sqrt.mpr
    linarith
  have hu1 : Real.sqrt N * Real.sqrt (Real.sqrt N) ≤ U := by
    rw [hUd]
    nlinarith [mul_nonneg hsN.le hssN.le, hlogNfac]
  have hu2 : (y:ℝ) * (1 + Real.log y) ≤ U := by
    rw [hUd]
    have h1 : (y:ℝ) * (1 + Real.log y) ≤ Real.sqrt N * (1 + Real.log N) :=
      mul_le_mul hyle hlogy1 hlogy0 hsN.le
    nlinarith [hss1, hsN.le, hlogNfac, h1]
  have hu3 : 2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
      + 2 * (y:ℝ) * (1 + Real.log y) ≤ 4 * U := by
    have h1 : Real.sqrt N * Real.sqrt y * (1 + Real.log y) ≤ U := by
      rw [hUd]
      have h2 : Real.sqrt N * Real.sqrt y ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsyle hsN.le
      apply mul_le_mul h2 hlogy1 hlogy0 (by positivity)
    linarith [hu2]
  have hu4 : 2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
      + 2 * (M':ℝ) * (1 + Real.log M') ≤ 4 * U := by
    have h1 : Real.sqrt N * Real.sqrt M' * (1 + Real.log M') ≤ U := by
      rw [hUd]
      have h2 : Real.sqrt N * Real.sqrt M' ≤ Real.sqrt N * Real.sqrt (Real.sqrt N) :=
        mul_le_mul_of_nonneg_left hsM'le hsN.le
      apply mul_le_mul h2 hlogM'1 hlogM'0 (by positivity)
    have h2 : (M':ℝ) * (1 + Real.log M') ≤ U := by
      rw [hUd]
      have hM'N : (M':ℝ) * (1 + Real.log M') ≤ Real.sqrt N * (1 + Real.log N) :=
        mul_le_mul hM'le hlogM'1 hlogM'0 hsN.le
      nlinarith [hss1, hsN.le, hlogNfac, hM'N]
    linarith
  calc |-(L₁ * ((N:ℝ) * (Lk - Sk))) - L₁ * FR + T2 + TL|
      ≤ |L₁ * ((N:ℝ) * (Lk - Sk))| + |L₁ * FR| + |T2| + |TL| := htri4
    _ ≤ (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)))
        + (1 + q₁) * ((y:ℝ) * (1 + Real.log y))
        + (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y))
        + 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) := by
        linarith [hb1, hb2, hε_le, htail_le]
    _ ≤ (1 + q₁) * (14 * B * U) + (1 + q₁) * U + (1 + 4 * q₁) * (4 * U)
        + 2 * B * (4 * U) := by
        have c1 : (1 + q₁) * (14 * B * (Real.sqrt N * Real.sqrt (Real.sqrt N)))
            ≤ (1 + q₁) * (14 * B * U) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact mul_le_mul_of_nonneg_left hu1 (by linarith)
        have c2 : (1 + q₁) * ((y:ℝ) * (1 + Real.log y)) ≤ (1 + q₁) * U :=
          mul_le_mul_of_nonneg_left hu2 (by linarith)
        have c3 : (1 + 4 * q₁) * (2 * Real.sqrt N * Real.sqrt y * (1 + Real.log y)
            + 2 * (y:ℝ) * (1 + Real.log y)) ≤ (1 + 4 * q₁) * (4 * U) :=
          mul_le_mul_of_nonneg_left hu3 (by linarith)
        have c4 : 2 * B * (2 * Real.sqrt N * Real.sqrt M' * (1 + Real.log M')
            + 2 * (M':ℝ) * (1 + Real.log M')) ≤ 2 * B * (4 * U) :=
          mul_le_mul_of_nonneg_left hu4 (by linarith)
        linarith [c1, c2, c3, c4]
    _ ≤ 30 * (1 + q₁) * (1 + B) * U := by
        nlinarith [hU0.le, hq₁, hB, mul_nonneg hq₁ hB,
          mul_nonneg (mul_nonneg hq₁ hB) hU0.le,
          mul_nonneg hq₁ hU0.le, mul_nonneg hB hU0.le]

/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/

