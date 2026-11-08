module
public import Examples.linrock__math_proofs.Dependencies.v3fbb6fa244fe.GoldbachSW1
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
lemma toArith_apply (g : ℕ → ℝ) (n : ℕ) (hn : n ≠ 0) : toArith g n = g n := by
  simp [toArith, hn]
/-- The lattice-point index set of the hyperbola method: pairs `(d,e)` with
    `1 ≤ d, e` and `d·e ≤ N`. -/
def hypSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N)
/-- **Convolution partial sums are lattice-point sums** (Siegel brick A2a-i). -/
lemma sum_conv_eq_sum_hypSet (f g : ArithmeticFunction ℝ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (f * g) n = ∑ p ∈ hypSet N, f p.1 * g p.2 := by
  have hL : ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ n ∈ Icc 1 N, ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun x => x.1 * x.2 = n),
          f p.1 * g p.2 := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    rw [ArithmeticFunction.mul_apply,
      Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by omega) hnN]
  rw [hL, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  rw [hypSet]
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hp.1.1 hp.2.1).ne'
/-- Row fibers of the hyperbola set: for `1 ≤ d`, the `e` with `d·e ≤ N` form `Icc 1 (N/d)`. -/
lemma row_fiber (N d : ℕ) (hd : 0 < d) :
    (Ioc 0 N).filter (fun e => d * e ≤ N) = Icc 1 (N / d) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · intro ⟨⟨he0, _⟩, hde⟩
    refine ⟨he0, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
    rw [Nat.mul_comm]
    exact hde
  · intro ⟨he1, heNd⟩
    have hde : d * e ≤ N := by
      have h := (Nat.le_div_iff_mul_le hd).mp heNd
      rw [Nat.mul_comm e d] at h
      exact h
    have heN : e ≤ N := by
      calc e ≤ d * e := Nat.le_mul_of_pos_left e hd
        _ ≤ N := hde
    exact ⟨⟨by omega, heN⟩, hde⟩
/-- Column fibers above the split: for `1 ≤ e`, the `d > y` with `d·e ≤ N` form
    `Icc (y+1) (N/e)`. -/
lemma col_fiber (N y e : ℕ) (he : 0 < e) :
    (Ioc 0 N).filter (fun d => ¬ d ≤ y ∧ d * e ≤ N) = Icc (y + 1) (N / e) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc, not_le]
  constructor
  · intro ⟨⟨_, _⟩, hyd, hde⟩
    exact ⟨hyd, (Nat.le_div_iff_mul_le he).mpr hde⟩
  · intro ⟨hyd, hdNe⟩
    have hde : d * e ≤ N := (Nat.le_div_iff_mul_le he).mp hdNe
    have hdN : d ≤ N := by
      calc d ≤ d * e := Nat.le_mul_of_pos_right d he
        _ ≤ N := hde
    exact ⟨⟨by omega, hdN⟩, hyd, hde⟩
/-- **The Dirichlet hyperbola identity** (Siegel brick A2a): for any split `y ≤ N`,
    `Σ_{n≤N}(f⋆g)(n) = Σ_{d≤y} f(d)·G(N/d) + Σ_{e≤N/(y+1)} g(e)·(F(N/e) − F(y))` —
    the exact identity behind the coefficient asymptotic `A(x) = λx + O(Q^c x^{4/5})`. -/
theorem hyperbola_identity (f g : ArithmeticFunction ℝ) (N y : ℕ) (hy : y ≤ N) :
    ∑ n ∈ Icc 1 N, (f * g) n
      = ∑ d ∈ Icc 1 y, f d * (∑ e ∈ Icc 1 (N / d), g e)
        + ∑ e ∈ Icc 1 (N / (y + 1)),
            g e * ((∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d) := by
  rw [sum_conv_eq_sum_hypSet, hypSet,
    ← Finset.sum_filter_add_sum_filter_not _ (fun p => p.1 ≤ y)]
  congr 1
  · -- head: rows d ≤ y
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product]
    simp only
    rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 N) (fun d => d ≤ y)]
    have hz : ∑ d ∈ (Ioc 0 N).filter (fun d => ¬ d ≤ y),
        ∑ e ∈ Ioc 0 N, (if d * e ≤ N ∧ d ≤ y then f d * g e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro e _
      rw [Finset.mem_filter] at hd
      rw [if_neg]
      intro hcon
      exact hd.2 hcon.2
    rw [hz, add_zero]
    have hIoc : (Ioc 0 N).filter (fun d => d ≤ y) = Icc 1 y := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hIoc]
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [Finset.mul_sum, ← row_fiber N d (by omega), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hde : d * e ≤ N
    · rw [if_pos ⟨hde, hdy⟩, if_pos hde]
    · rw [if_neg (fun h => hde h.1), if_neg hde]
  · -- tail: columns, d > y
    rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_product_right]
    simp only
    have hsub : Icc 1 (N / (y + 1)) ⊆ Ioc 0 N := by
      intro e he
      obtain ⟨he1, heN⟩ := Finset.mem_Icc.mp he
      rw [Finset.mem_Ioc]
      have : N / (y + 1) ≤ N := Nat.div_le_self N (y + 1)
      omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro e he
      obtain ⟨he1, heNy⟩ := Finset.mem_Icc.mp he
      have hy1e : y + 1 ≤ N / e + 1 := by
        have h1 : e * (y + 1) ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp heNy
        have h2 : y + 1 ≤ N / e := by
          apply (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr
          rw [Nat.mul_comm]
          exact h1
        omega
      have hIcoIcc : ∀ a b : ℕ, Ico a (b + 1) = Icc a b := by
        intro a b
        ext x
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
      have hdiff : (∑ d ∈ Icc 1 (N / e), f d) - ∑ d ∈ Icc 1 y, f d
          = ∑ d ∈ Icc (y + 1) (N / e), f d := by
        rw [← hIcoIcc 1 (N / e),
          ← Finset.sum_Ico_consecutive (fun d => f d) (by omega : 1 ≤ y + 1) hy1e,
          hIcoIcc 1 y, hIcoIcc (y + 1) (N / e), add_sub_cancel_left]
      rw [hdiff, Finset.mul_sum, ← col_fiber N y e (by omega), Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hcase : d * e ≤ N ∧ ¬ d ≤ y
      · rw [if_pos hcase, if_pos ⟨hcase.2, hcase.1⟩, mul_comm]
      · rw [if_neg hcase, if_neg (fun hcon => hcase ⟨hcon.2, hcon.1⟩)]
    · intro e heIoc heNot
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      intro ⟨hde, hdy⟩
      apply heNot
      rw [Finset.mem_Icc]
      obtain ⟨he0, _⟩ := Finset.mem_Ioc.mp heIoc
      refine ⟨by omega, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega : 0 < y + 1)]
      push_neg at hdy
      calc e * (y + 1) ≤ e * d := by
            apply Nat.mul_le_mul_left
            omega
        _ = d * e := Nat.mul_comm e d
        _ ≤ N := hde
/-- **Harmonic partial sums** (Siegel brick A2b-i): `Σ_{c≤z} 1/c ≤ 1 + log z`. -/
lemma sum_one_div_le_log (z : ℕ) (hz : 1 ≤ z) :
    ∑ c ∈ Icc 1 z, (1 : ℝ) / c ≤ 1 + Real.log z := by
  have hh := harmonic_le_one_add_log z
  have hcast : ((harmonic z : ℚ) : ℝ) = ∑ c ∈ Icc 1 z, (1 : ℝ) / c := by
    rw [harmonic,
      show Icc 1 z = Ico 1 (z + 1) from by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega,
      Finset.sum_Ico_eq_sum_range]
    push_cast
    apply Finset.sum_congr (by norm_num)
    intro i _
    push_cast
    ring
  rw [← hcast]
  exact_mod_cast hh
/-- **Square-root reciprocal partial sums** (Siegel brick A2b-ii): `Σ_{e≤z} 1/√e ≤ 2√z` —
    by the telescoping `1/√e ≤ 2(√e − √(e−1))`. -/
lemma sum_one_div_sqrt_le (z : ℕ) :
    ∑ e ∈ Icc 1 z, (1 : ℝ) / Real.sqrt e ≤ 2 * Real.sqrt z := by
  induction z with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hstep : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hstep, Finset.sum_insert (by simp)]
    have hkey : (1 : ℝ) / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
      have hs1 : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      have hprod : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)
          * (Real.sqrt ((n : ℝ) + 1) + Real.sqrt n) = 1 := by
        have h1 : Real.sqrt ((n : ℝ) + 1) ^ 2 = (n : ℝ) + 1 :=
          Real.sq_sqrt (by positivity)
        have h2 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
        nlinarith [h1, h2]
      have hsumle : Real.sqrt ((n : ℝ) + 1) + Real.sqrt n
          ≤ 2 * Real.sqrt ((n : ℝ) + 1) := by
        have := Real.sqrt_le_sqrt (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
        linarith
      rw [div_le_iff₀ hs1]
      have hdiffpos : 0 < Real.sqrt ((n : ℝ) + 1) - Real.sqrt n := by
        rcases lt_or_ge (Real.sqrt n) (Real.sqrt ((n:ℝ) + 1)) with h | h
        · linarith
        · exfalso
          nlinarith [hprod]
      nlinarith [hprod, hsumle, hdiffpos, hs1]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast] at *
    linarith [ih, hkey]
/-- **Row decomposition of hyperbola-set sums** (Siegel brick A2b-iii):
    `Σ_{p ∈ hypSet N} F(p) = Σ_{d≤N} Σ_{e≤N/d} F(d,e)`. -/
lemma sum_hypSet_eq_rows (N : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ p ∈ (Ioc 0 N ×ˢ Ioc 0 N).filter (fun p => p.1 * p.2 ≤ N), F p
      = ∑ d ∈ Icc 1 N, ∑ e ∈ Icc 1 (N / d), F (d, e) := by
  rw [Finset.sum_filter, Finset.sum_product]
  have hIoc : (Ioc 0 N : Finset ℕ) = Icc 1 N := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc]
  apply Finset.sum_congr rfl
  intro d hd
  obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
  have hrow : Icc 1 (N / d) = (Icc 1 N).filter (fun e => d * e ≤ N) := by
    ext e
    simp only [Finset.mem_Icc, Finset.mem_filter]
    constructor
    · intro ⟨he1, heNd⟩
      have hde : d * e ≤ N := by
        have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp heNd
        rw [Nat.mul_comm e d] at h
        exact h
      have heN : e ≤ N := le_trans (Nat.le_mul_of_pos_left e (by omega)) hde
      exact ⟨⟨he1, heN⟩, hde⟩
    · intro ⟨⟨he1, _⟩, hde⟩
      refine ⟨he1, (Nat.le_div_iff_mul_le (by omega : 0 < d)).mpr ?_⟩
      rw [Nat.mul_comm]
      exact hde
  rw [hrow, Finset.sum_filter]
/-- **The divisor-weighted root sum** (Siegel brick A2b-iv):
    `Σ_{p ∈ hypSet z} 1/√(p₁p₂) ≤ 2√z(1 + log z)` — the error-term workhorse:
    every `Σ_{e≤z} d(e)/√e` style bound routes through this lattice form. -/
lemma sum_hypSet_inv_sqrt_le (z : ℕ) (hz : 1 ≤ z) :
    ∑ p ∈ (Ioc 0 z ×ˢ Ioc 0 z).filter (fun p => p.1 * p.2 ≤ z),
        (1 : ℝ) / Real.sqrt (p.1 * p.2)
      ≤ 2 * Real.sqrt z * (1 + Real.log z) := by
  rw [sum_hypSet_eq_rows]
  have hrow : ∀ d ∈ Icc 1 z, ∑ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
      ≤ (1 / (d : ℝ)) * (2 * Real.sqrt z) := by
    intro d hd
    obtain ⟨hd1, hdz⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    have hsplit : ∀ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
        = (1 / Real.sqrt d) * (1 / Real.sqrt e) := by
      intro e he
      obtain ⟨he1, _⟩ := Finset.mem_Icc.mp he
      simp only
      rw [Real.sqrt_mul (Nat.cast_nonneg d)]
      ring
    rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
    have hsum := sum_one_div_sqrt_le (z / d)
    have hdivle : Real.sqrt ((z / d : ℕ) : ℝ) ≤ Real.sqrt z / Real.sqrt d := by
      calc Real.sqrt ((z / d : ℕ) : ℝ) ≤ Real.sqrt ((z : ℝ) / d) :=
            Real.sqrt_le_sqrt Nat.cast_div_le
        _ = Real.sqrt z / Real.sqrt d := Real.sqrt_div (Nat.cast_nonneg z) d
    have hsd : (0:ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd0
    calc (1 / Real.sqrt d) * ∑ e ∈ Icc 1 (z / d), (1:ℝ) / Real.sqrt e
        ≤ (1 / Real.sqrt d) * (2 * Real.sqrt ((z / d : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ (1 / Real.sqrt d) * (2 * (Real.sqrt z / Real.sqrt d)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [hdivle]
      _ = 2 * Real.sqrt z / (Real.sqrt d * Real.sqrt d) := by ring
      _ = (1 / (d : ℝ)) * (2 * Real.sqrt z) := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg d)]
          ring
  calc ∑ d ∈ Icc 1 z, ∑ e ∈ Icc 1 (z / d), (1 : ℝ) / Real.sqrt ((d, e).1 * (d, e).2)
      ≤ ∑ d ∈ Icc 1 z, (1 / (d : ℝ)) * (2 * Real.sqrt z) := Finset.sum_le_sum hrow
    _ = (∑ d ∈ Icc 1 z, (1 : ℝ) / d) * (2 * Real.sqrt z) := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + Real.log z) * (2 * Real.sqrt z) := by
        apply mul_le_mul_of_nonneg_right (sum_one_div_le_log z hz) (by positivity)
    _ = 2 * Real.sqrt z * (1 + Real.log z) := by ring
/-- **Abel rearrangement over a tail window** (Siegel brick A2c-i-a): with
    `G t = Σ_{n≤t} g n`, for `y ≤ z`:
    `Σ_{y<d≤z} g(d)/d = Σ_{y<d≤z} G(d)(1/d − 1/(d+1)) + G(z)/(z+1) − G(y)/(y+1)`. -/
lemma abel_window (g : ℕ → ℝ) (y : ℕ) :
    ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, g d / d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1) := by
  intro z
  induction z with
  | zero =>
    intro hy0
    interval_cases y
    simp
  | succ m ih =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · -- y = m + 1: both windows empty
      have hy : y = m + 1 := by omega
      subst hy
      simp
    · -- extend from m to m+1
      have hstepL : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hstepG : Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstepL, Finset.sum_insert (by simp), Finset.sum_insert (by simp),
        hstepG, Finset.sum_insert (by simp), ih hge]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
/-- The telescoping kernel sum: `Σ_{y<d≤z} (1/d − 1/(d+1)) = 1/(y+1) − 1/(z+1)`. -/
lemma telescope_kernel (y : ℕ) : ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, ((1 : ℝ) / d - 1 / (d + 1)) = 1 / (y + 1) - 1 / (z + 1) := by
  intro z
  induction z with
  | zero =>
    intro hy0
    interval_cases y
    simp
  | succ m ihm =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · have hy : y = m + 1 := by omega
      subst hy
      simp
    · have hstep : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstep, Finset.sum_insert (by simp), ihm hge]
      push_cast
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hm2 : ((m : ℝ) + 1 + 1) ≠ 0 := by positivity
      field_simp
      ring
/-- **The bounded-sum Abel tail bound** (Siegel brick A2c-i): if all partial sums of `g`
    are bounded by `q`, the tail `Σ_{y<d≤z} g(d)/d` is at most `2q/(y+1)` — uniformly
    in `z`. The engine of both `Σ_{d≤y} g(d)/d`'s convergence and its tail rate. -/
lemma abel_tail_bound (g : ℕ → ℝ) (q : ℝ)
    (hG : ∀ t : ℕ, |∑ n ∈ Icc 1 t, g n| ≤ q) (y z : ℕ) (hyz : y ≤ z) :
    |∑ d ∈ Icc (y + 1) z, g d / d| ≤ 2 * q / (y + 1) := by
  have hq : 0 ≤ q := le_trans (abs_nonneg _) (hG 0)
  rw [abel_window g y z hyz]
  have hterm : ∀ d ∈ Icc (y + 1) z,
      |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        ≤ q * ((1 : ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by
      have : (1:ℕ) ≤ d := by omega
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    have hker : (0:ℝ) ≤ 1 / (d : ℝ) - 1 / (d + 1) := by
      rw [sub_nonneg, div_le_div_iff₀ (by positivity) hd0]
      linarith
    rw [abs_mul, abs_of_nonneg hker]
    exact mul_le_mul_of_nonneg_right (hG d) hker
  have htele := telescope_kernel y z hyz
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))
        + (∑ n ∈ Icc 1 z, g n) / (z + 1) - (∑ n ∈ Icc 1 y, g n) / (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
        + |(∑ n ∈ Icc 1 z, g n) / (z + 1)| + |(∑ n ∈ Icc 1 y, g n) / (y + 1)| := by
        set A := ∑ d ∈ Icc (y + 1) z,
          (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1)) with hA
        set B := (∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1) with hB
        set C := (∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1) with hC
        have h1 : |A + B| ≤ |A| + |B| := abs_add_le A B
        have h2 : |A + B - C| ≤ |A + B| + |C| := by
          rw [sub_eq_add_neg]
          have := abs_add_le (A + B) (-C)
          rwa [abs_neg] at this
        linarith [h1, h2]
    _ ≤ (q * ((1:ℝ) / (y + 1) - 1 / (z + 1))) + q / (z + 1) + q / (y + 1) := by
        have hs : |∑ d ∈ Icc (y + 1) z,
            (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
            ≤ q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
          calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))|
              ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, g n) * ((1 : ℝ) / d - 1 / (d + 1))| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ d ∈ Icc (y + 1) z, q * ((1 : ℝ) / d - 1 / (d + 1)) :=
                Finset.sum_le_sum hterm
            _ = q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) := by
                rw [← Finset.mul_sum, htele]
        have hz1 : |(∑ n ∈ Icc 1 z, g n) / ((z:ℝ) + 1)| ≤ q / (z + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (z:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG z) (by positivity)
        have hy1 : |(∑ n ∈ Icc 1 y, g n) / ((y:ℝ) + 1)| ≤ q / (y + 1) := by
          rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (y:ℝ) + 1)]
          apply div_le_div_of_nonneg_right (hG y) (by positivity)
        linarith [hs, hz1, hy1]
    _ ≤ 2 * q / (y + 1) := by
        have hzq : (0:ℝ) ≤ q / (z + 1) := by positivity
        have h1 : q * ((1:ℝ) / (y + 1) - 1 / (z + 1)) + q / (z + 1) = q / (y + 1) := by
          field_simp
          ring
        have h2 : q / ((y:ℝ) + 1) + q / (y + 1) = 2 * q / (y + 1) := by ring
        linarith [h1, h2]
/-- Sharp 3/2-power telescoping (Siegel brick A2e-i-a):
    `Σ_{y<d≤z} 1/(d√d) ≤ 2/√y − 2/√z` for `1 ≤ y ≤ z` — from the previous-interval
    comparison `1/(d√d) ≤ 2(1/√(d−1) − 1/√d)`. -/
lemma sum_three_half_tail_sharp (y : ℕ) (hy1 : 1 ≤ y) : ∀ z : ℕ, y ≤ z →
    ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d)
      ≤ 2 / Real.sqrt y - 2 / Real.sqrt z := by
  intro z
  induction z with
  | zero =>
    intro hy0
    omega
  | succ m ihm =>
    intro hym
    rcases Nat.lt_or_ge m y with hlt | hge
    · -- y = m + 1: empty window, RHS = 0
      have hy : y = m + 1 := by omega
      subst hy
      simp
    · -- extend from m to m+1; m ≥ y ≥ 1
      have hm1 : 1 ≤ m := le_trans hy1 hge
      have hstep : Icc (y + 1) (m + 1) = insert (m + 1) (Icc (y + 1) m) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [hstep, Finset.sum_insert (by simp)]
      have hm0 : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hm10 : (0:ℝ) < (m : ℝ) + 1 := by linarith
      set a : ℝ := Real.sqrt m with ha
      set b : ℝ := Real.sqrt ((m : ℝ) + 1) with hb
      have hs1 : (0:ℝ) < a := Real.sqrt_pos.mpr hm0
      have hs2 : (0:ℝ) < b := Real.sqrt_pos.mpr hm10
      have hsq1 : a * a = (m : ℝ) := Real.mul_self_sqrt hm0.le
      have hsq2 : b * b = (m : ℝ) + 1 := Real.mul_self_sqrt hm10.le
      have hmono : a ≤ b := Real.sqrt_le_sqrt (by linarith)
      have hba : b * b - a * a = 1 := by linarith [hsq1, hsq2]
      have hkey : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))
          ≤ 2 / a - 2 / b := by
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast, ← hb]
        rw [div_sub_div _ _ (ne_of_gt hs1) (ne_of_gt hs2),
          div_le_div_iff₀ (by positivity) (by positivity)]
        -- goal: 1·(a·b) ≤ (2b − 2a)·((m+1)·b); with m+1 = b², reduces to ab ≤ m+2
        have hab : a * b ≤ b * b := mul_le_mul_of_nonneg_right hmono hs2.le
        nlinarith [hab, hba, hsq1, hsq2, hs1, hs2, hmono,
          mul_pos hs1 hs2, mul_nonneg (mul_nonneg (sub_nonneg.mpr hmono) hs2.le) hs2.le,
          mul_le_mul_of_nonneg_right hab hs2.le]
      have hih := ihm hge
      have hccast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      have hsm : Real.sqrt ((m : ℕ) : ℝ) = a := rfl
      calc (1 : ℝ) / (((m + 1 : ℕ) : ℝ) * Real.sqrt ((m + 1 : ℕ) : ℝ))
            + ∑ d ∈ Icc (y + 1) m, (1 : ℝ) / (d * Real.sqrt d)
          ≤ (2 / a - 2 / b) + (2 / Real.sqrt y - 2 / a) :=
            add_le_add hkey hih
        _ = 2 / Real.sqrt y - 2 / b := by ring
        _ = 2 / Real.sqrt y - 2 / Real.sqrt ((m + 1 : ℕ) : ℝ) := by
            rw [show Real.sqrt ((m + 1 : ℕ) : ℝ) = b from by rw [hccast]]
/-- Boundary helper: `(√t+1)/(t+1) ≤ 2/√t` for `t ≥ 1`. -/
lemma sqrt_boundary_le (t : ℕ) (ht : 1 ≤ t) :
    (Real.sqrt t + 1) / ((t : ℝ) + 1) ≤ 2 / Real.sqrt t := by
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hs : (0:ℝ) < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsq : Real.sqrt t * Real.sqrt t = (t : ℝ) := Real.mul_self_sqrt ht0.le
  have hs1 : (1:ℝ) ≤ Real.sqrt t :=
    Real.one_le_sqrt.mpr (by exact_mod_cast ht)
  rw [div_le_div_iff₀ (by positivity) hs]
  nlinarith [hsq, hs1, hs]
/-- **The √-growth Abel tail** (Siegel brick A2e-ii-a): if the partial sums of `k`
    satisfy `|K(t)| ≤ B(√t+1)`, then `|Σ_{y<d≤z} k(d)/d| ≤ 7B/√y` for `1 ≤ y ≤ z` —
    the tail engine for the pole-free convolution side of the Goldfeld product. -/
theorem abel_tail_sqrt (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    (y z : ℕ) (hy1 : 1 ≤ y) (hyz : y ≤ z) :
    |∑ d ∈ Icc (y + 1) z, k d / d| ≤ 7 * B / Real.sqrt y := by
  have hB : 0 ≤ B := by
    have h0 := hK 0
    simp at h0
    linarith [abs_nonneg (∑ n ∈ Icc 1 0, k n), h0]
  have hy0 : (0:ℝ) < y := by exact_mod_cast hy1
  have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsyz : Real.sqrt y ≤ Real.sqrt z := Real.sqrt_le_sqrt (by exact_mod_cast hyz)
  have hsz : (0:ℝ) < Real.sqrt z := lt_of_lt_of_le hsy hsyz
  rw [abel_window k y z hyz]
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
          · exact mul_le_mul_of_nonneg_left (sum_three_half_tail_sharp y hy1 z hyz) hB
          · rw [telescope_kernel y z hyz]
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
      sqrt_boundary_le z (by omega)
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
      sqrt_boundary_le y hy1
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
/-- Convolution values are divisor-counted (Siegel brick A2e-iii-a1): for 1-bounded
    inputs, `|(k₁⋆k₂)(n)| ≤ τ(n)` where `τ(n) = #divisorsAntidiagonal(n)`. -/
lemma conv_value_le_tau (k₁ k₂ : ℕ → ℝ) (h1b : ∀ n, |k₁ n| ≤ 1) (h2b : ∀ n, |k₂ n| ≤ 1)
    (n : ℕ) :
    |(toArith k₁ * toArith k₂) n| ≤ ((n.divisorsAntidiagonal).card : ℝ) := by
  rw [ArithmeticFunction.mul_apply]
  calc |∑ p ∈ n.divisorsAntidiagonal, toArith k₁ p.1 * toArith k₂ p.2|
      ≤ ∑ p ∈ n.divisorsAntidiagonal, |toArith k₁ p.1 * toArith k₂ p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal, 1 := by
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul]
        have h1 : |toArith k₁ p.1| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.1 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₁ p.1 = k₁ p.1 from by simp [toArith, h0.ne']]
            exact h1b p.1
        have h2 : |toArith k₂ p.2| ≤ 1 := by
          rcases Nat.eq_zero_or_pos p.2 with h0 | h0
          · simp [toArith, h0]
          · rw [show toArith k₂ p.2 = k₂ p.2 from by simp [toArith, h0.ne']]
            exact h2b p.2
        calc |toArith k₁ p.1| * |toArith k₂ p.2| ≤ 1 * 1 :=
            mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    _ = ((n.divisorsAntidiagonal).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
/-- Fiberwise unfolding: divisor-pair sums over `d ≤ y` are hyperbola-set sums
    (Siegel brick A2e-iii-a2). -/
lemma sum_divA_eq_hypSet (y : ℕ) (F : ℕ × ℕ → ℝ) :
    ∑ d ∈ Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p
      = ∑ p ∈ (Ioc 0 y ×ˢ Ioc 0 y).filter (fun p => p.1 * p.2 ≤ y), F p := by
  have hL : ∑ d ∈ Icc 1 y, ∑ p ∈ d.divisorsAntidiagonal, F p
      = ∑ d ∈ Icc 1 y, ∑ p ∈ (Ioc 0 y ×ˢ Ioc 0 y).filter (fun x => x.1 * x.2 = d), F p := by
    apply Finset.sum_congr rfl
    intro d hd
    obtain ⟨hd1, hdy⟩ := Finset.mem_Icc.mp hd
    rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le (by omega) hdy]
  rw [hL, Finset.sum_fiberwise_eq_sum_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_congr
  intro p hp
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  simp only [Finset.mem_Icc]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hp.1.1 hp.2.1).ne', h⟩
/-- **τ partial sums** (Siegel brick A2e-iii-a3): `Σ_{d≤y} τ(d) ≤ y(1 + log y)`. -/
lemma sum_tau_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) ≤ (y : ℝ) * (1 + Real.log y) := by
  have hcard : ∀ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ)
      = ∑ p ∈ d.divisorsAntidiagonal, (1 : ℝ) := by
    intro d _
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_congr rfl hcard, sum_divA_eq_hypSet, sum_hypSet_eq_rows]
  have hrow : ∀ d ∈ Icc 1 y, ∑ e ∈ Icc 1 (y / d), (1:ℝ) ≤ (y : ℝ) * (1 / d) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hd0 : (0:ℝ) < d := by exact_mod_cast hd1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.add_sub_cancel]
    have h1 : ((y / d : ℕ) : ℝ) ≤ (y : ℝ) / d := Nat.cast_div_le
    rw [mul_one_div]
    exact h1
  calc ∑ d ∈ Icc 1 y, ∑ e ∈ Icc 1 (y / d), (1:ℝ)
      ≤ ∑ d ∈ Icc 1 y, (y : ℝ) * (1 / d) := Finset.sum_le_sum hrow
    _ = (y : ℝ) * ∑ d ∈ Icc 1 y, (1 : ℝ) / d := by rw [← Finset.mul_sum]
    _ ≤ (y : ℝ) * (1 + Real.log y) := by
        apply mul_le_mul_of_nonneg_left (sum_one_div_le_log y hy) (by positivity)
/-- **τ/√ partial sums** (Siegel brick A2e-iii-a4):
    `Σ_{d≤y} τ(d)/√d ≤ 2√y(1 + log y)` — on each antidiagonal `p₁p₂ = d`. -/
lemma sum_tau_div_sqrt_le (y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      ≤ 2 * Real.sqrt y * (1 + Real.log y) := by
  have hstep : ∀ d ∈ Icc 1 y, ((d.divisorsAntidiagonal).card : ℝ) / Real.sqrt d
      = ∑ p ∈ d.divisorsAntidiagonal, (1 : ℝ) / Real.sqrt (p.1 * p.2) := by
    intro d hd
    obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
    have hterm : ∀ p ∈ d.divisorsAntidiagonal, (1 : ℝ) / Real.sqrt (p.1 * p.2)
        = (1 : ℝ) / Real.sqrt d := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [show ((p.1 : ℝ) * (p.2 : ℝ)) = ((d : ℕ) : ℝ) from by exact_mod_cast hp.1]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one_div]
  rw [Finset.sum_congr rfl hstep, sum_divA_eq_hypSet]
  exact sum_hypSet_inv_sqrt_le y hy
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
/-- **ℂ-weighted Abel summation over an initial window** (Siegel brick A2g-i):
    `Σ_{n≤x} a(n)w(n) = A(x)w(x) + Σ_{n<x} A(n)(w(n) − w(n+1))` with
    `A(t) = Σ_{n≤t} a(n)` — the discrete engine of the integral representation,
    for arbitrary complex weights `w`. -/
lemma abel_initial (a : ℕ → ℂ) (w : ℕ → ℂ) :
    ∀ x : ℕ, 1 ≤ x →
    ∑ n ∈ Icc 1 x, a n * w n
      = (∑ n ∈ Icc 1 x, a n) * w x
        + ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) := by
  intro x
  induction x with
  | zero =>
    intro h0
    omega
  | succ p ih =>
    intro _
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · -- x = 1
      simp
    · -- step p → p+1
      have hstepL : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hp1 : p + 1 - 1 = p := by omega
      rw [hstepL, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih hp, hp1]
      have hstepW : Icc 1 p = insert p (Icc 1 (p - 1)) := by
        ext m
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      rw [show ∑ n ∈ Icc 1 p, (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1))
          = (∑ m ∈ Icc 1 p, a m) * (w p - w (p + 1))
            + ∑ n ∈ Icc 1 (p - 1), (∑ m ∈ Icc 1 n, a m) * (w n - w (n + 1)) from by
        rw [hstepW, Finset.sum_insert (by
          simp only [Finset.mem_Icc]
          omega), ← hstepW]]
      ring
/-! ### Duplicated verbatim from DirichletLPoleBound.lean (verified there) -/
/-- The weighted telescope: `Σ_{n≤x} n(wₙ − wₙ₊₁) = Σ_{n≤x} wₙ − x·w_{x+1}` (real). -/
lemma weighted_telescope (w : ℕ → ℝ) : ∀ x : ℕ,
    ∑ n ∈ Icc 1 x, (n : ℝ) * (w n - w (n + 1))
      = ∑ n ∈ Icc 1 x, w n - (x : ℝ) * w (x + 1) := by
  intro x
  induction x with
  | zero => simp
  | succ p ih =>
    have hstep : Icc 1 (p + 1) = insert (p + 1) (Icc 1 p) := by
      ext m
      simp only [Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hstep, Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih]
    push_cast
    ring
/-- **The partial-sum series representation** (Siegel brick A2g-ii): for linearly
    bounded partial sums `‖A(x)‖ ≤ Cx` and `Re s > 1`,
    `Σ' n, a(n)n^{−s} = Σ' n, A(n)(n^{−s} − (n+1)^{−s})` — the boundary term
    `A(x)x^{−s}` dies and the Abel-rearranged series converges to the L-series. -/
theorem lseries_eq_tsum_abel (a : ℕ → ℂ) (C : ℝ)
    (hC : ∀ x : ℕ, ‖∑ n ∈ Icc 1 x, a n‖ ≤ C * x)
    {s : ℂ} (hs : 1 < s.re) (hsum : LSeriesSummable a s) :
    LSeries a s
      = ∑' n : ℕ, (∑ m ∈ Icc 1 n, a m) * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
  -- the partial sums of the L-series along Icc 1 x
  have hterm_eq : ∀ n : ℕ, 1 ≤ n → LSeries.term a s n = a n * ((n:ℂ)) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero (by omega), Complex.cpow_neg, div_eq_mul_inv]
  have hpartial : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
      atTop (nhds (LSeries a s)) := by
    have h1 : Tendsto (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n)
        atTop (nhds (LSeries a s)) := by
      have := hsum.hasSum.tendsto_sum_nat
      exact this.comp (tendsto_add_atTop_nat 1)
    have h2 : ∀ x : ℕ, ∑ n ∈ range (x + 1), LSeries.term a s n
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s) := by
      intro x
      rw [show range (x + 1) = insert 0 (Icc 1 x) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [LSeries.term_zero, zero_add]
      exact Finset.sum_congr rfl (fun n hn => hterm_eq n (Finset.mem_Icc.mp hn).1)
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s))
        = (fun x : ℕ => ∑ n ∈ range (x + 1), LSeries.term a s n) from
      funext (fun x => (h2 x).symm)]
    exact h1
  -- boundary decay: A(x)·x^{−s} → 0
  have hboundary : Tendsto (fun x : ℕ => (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s))
      atTop (nhds 0) := by
    have hC0 : 0 ≤ C := by
      have h0 := hC 1
      have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
      have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
      linarith [h0, h1, h2.le, h2.ge]
    have hbnd : ∀ x : ℕ, ‖(∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s)‖
        ≤ C * ((x:ℝ)) ^ (1 - s.re) := by
      intro x
      rcases Nat.eq_zero_or_pos x with rfl | hx0
      · rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
          Finset.sum_empty, zero_mul, norm_zero, Nat.cast_zero,
          Real.zero_rpow (by linarith : (1:ℝ) - s.re ≠ 0), mul_zero]
      · rw [norm_mul, Complex.norm_natCast_cpow_of_pos hx0, Complex.neg_re]
        have hxr : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx0
        calc ‖∑ n ∈ Icc 1 x, a n‖ * ((x:ℝ)) ^ (-s.re)
            ≤ (C * x) * ((x:ℝ)) ^ (-s.re) := by
              apply mul_le_mul_of_nonneg_right (hC x) (Real.rpow_nonneg hxr.le _)
          _ = C * ((x:ℝ)) ^ (1 - s.re) := by
              rw [show (1:ℝ) - s.re = 1 + (-s.re) by ring, Real.rpow_add hxr,
                Real.rpow_one]
              ring
    have hg0 : Tendsto (fun x : ℕ => C * ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
      have h1 : Tendsto (fun x : ℕ => ((x:ℝ)) ^ (1 - s.re)) atTop (nhds 0) := by
        have := tendsto_rpow_neg_atTop (show (0:ℝ) < s.re - 1 by linarith)
        have hcomp := this.comp tendsto_natCast_atTop_atTop
        simpa [Function.comp_def, neg_sub] using hcomp
      simpa using h1.const_mul C
    exact squeeze_zero_norm hbnd hg0
  -- Abel + limits
  have hAbel : ∀ x : ℕ, 1 ≤ x →
      ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
        - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
    intro x hx
    have := abel_initial a (fun n => ((n:ℂ)) ^ (-s)) x hx
    push_cast at this ⊢
    linear_combination -this
  have hlim : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop (nhds (LSeries a s)) := by
    have heq : ∀ᶠ x : ℕ in atTop, ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
        = ∑ n ∈ Icc 1 x, a n * ((n:ℂ)) ^ (-s)
          - (∑ n ∈ Icc 1 x, a n) * ((x:ℂ)) ^ (-s) := by
      filter_upwards [eventually_ge_atTop 1] with x hx
      exact hAbel x hx
    rw [Filter.tendsto_congr' heq]
    have := hpartial.sub hboundary
    simpa using this
  -- absolute convergence via the real difference kernel
  have hC0' : 0 ≤ C := by
    have h0 := hC 1
    have h1 : (0:ℝ) ≤ ‖∑ n ∈ Icc 1 1, a n‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  have hsummable : Summable (fun n : ℕ => (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
    set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
    have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
      intro n hn
      rw [hw]
      simp only
      apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
      linarith
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
    · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
      · intro n
        rcases Nat.eq_zero_or_pos n with rfl | hn0
        · simp
        · apply mul_nonneg (by positivity)
          apply mul_nonneg (Nat.cast_nonneg n)
          linarith [hwanti n hn0]
      · intro x
        have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
            = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
          rw [Finset.mul_sum]
          rcases Nat.eq_zero_or_pos x with rfl | hx0
          · simp
          · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
              ext m
              simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
              omega]
            rw [Finset.sum_insert (by simp)]
            simp
        rw [hIcc, weighted_telescope w (x - 1)]
        have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
          apply mul_nonneg (Nat.cast_nonneg _)
          rw [hw]
          simp only
          positivity
        have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
          have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
            intro n hn
            obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
            rw [hw]
            simp only
            rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
          rw [Finset.sum_congr rfl hterm]
          calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
              ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
                Summable.sum_le_tsum _ (fun n _ => by positivity)
                  (Real.summable_one_div_nat_rpow.mpr hs)
            _ ≤ s.re / (s.re - 1) := tsum_one_div_nat_rpow_le s.re hs
        have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
        apply mul_le_mul_of_nonneg_left _ hfac
        linarith [hsums, htail]
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · rw [norm_mul]
        have h1 := hC n
        have h2 := cpow_diff_kernel_bound n hn0 s hσ0
        calc ‖∑ m ∈ Icc 1 n, a m‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
            ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
              apply mul_le_mul h1 h2 (norm_nonneg _)
              positivity
          _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
              rw [hw]
              simp only
              push_cast
              ring
  have hrange := hsummable.hasSum.tendsto_sum_nat
  have hIccrange : ∀ x : ℕ, ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))
      = ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)) := by
    intro x
    rcases Nat.eq_zero_or_pos x with rfl | hx0
    · simp
    · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
        ext m
        simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
        omega]
      rw [Finset.sum_insert (by simp)]
      rw [show (Icc 1 0 : Finset ℕ) = ∅ from Finset.Icc_eq_empty (by omega),
        Finset.sum_empty, zero_mul, zero_add]
  have hrange' : Tendsto (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
      * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) atTop
      (nhds (∑' n : ℕ, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))) := by
    rw [show (fun x : ℕ => ∑ n ∈ Icc 1 (x - 1), (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)))
        = (fun x : ℕ => ∑ n ∈ range x, (∑ m ∈ Icc 1 n, a m)
        * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) from
      funext (fun x => (hIccrange x).symm)]
    exact hrange
  exact (tendsto_nhds_unique hrange' hlim).symm
/-- Bernoulli for negative real exponents (Siegel brick A2g-a1-i):
    `(1+u)^{−σ} ≥ 1 − σu` for `u, σ ≥ 0` — from `(1−x)eˣ ≤ 1` and `log(1+u) ≤ u`. -/
lemma rpow_neg_ge_one_sub (u σ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ) :
    1 - σ * u ≤ (1 + u) ^ (-σ) := by
  by_cases hbig : 1 ≤ σ * u
  · -- trivial: LHS ≤ 0 ≤ RHS
    have h1 : (0:ℝ) < 1 + u := by linarith
    have h2 : (0:ℝ) ≤ (1 + u) ^ (-σ) := Real.rpow_nonneg h1.le _
    linarith
  · -- (1+u)^σ ≤ e^{σu} ≤ 1/(1−σu)
    push_neg at hbig
    have hsmall : σ * u < 1 := hbig
    have h1 : (0:ℝ) < 1 + u := by linarith
    have hlog : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos h1
      linarith
    have hpow : (1 + u) ^ σ ≤ Real.exp (σ * u) := by
      rw [Real.rpow_def_of_pos h1]
      apply Real.exp_le_exp.mpr
      calc Real.log (1 + u) * σ ≤ u * σ := mul_le_mul_of_nonneg_right hlog hσ
        _ = σ * u := mul_comm _ _
    have hexp : Real.exp (σ * u) * (1 - σ * u) ≤ 1 := by
      have h2 := Real.add_one_le_exp (-(σ * u))
      have h3 : (0:ℝ) < Real.exp (σ * u) := Real.exp_pos _
      have h4 : Real.exp (-(σ * u)) = 1 / Real.exp (σ * u) := by
        rw [Real.exp_neg, one_div]
      rw [h4, le_div_iff₀ h3] at h2
      nlinarith [h2]
    have hposσu : (0:ℝ) < 1 - σ * u := by linarith
    have hpow0 : (0:ℝ) < (1 + u) ^ σ := Real.rpow_pos_of_pos h1 _
    rw [Real.rpow_neg h1.le, le_inv_comm₀ hposσu hpow0]
    calc (1 + u) ^ σ ≤ Real.exp (σ * u) := hpow
      _ ≤ 1 / (1 - σ * u) := by
          rw [le_div_iff₀ hposσu]
          exact hexp
      _ = (1 - σ * u)⁻¹ := one_div _
/-- **The kernel decay bound** (Siegel brick A2g-a1): for `σ ≥ 0` and `n ≥ 1`,
    `n^{−σ} − (n+1)^{−σ} ≤ σ·n^{−σ−1}` — the uniform-in-window majorant. -/
lemma rpow_diff_le (n : ℕ) (hn : 1 ≤ n) (σ : ℝ) (hσ : 0 ≤ σ) :
    (n : ℝ) ^ (-σ) - ((n + 1 : ℕ) : ℝ) ^ (-σ) ≤ σ * (n : ℝ) ^ (-σ - 1) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hu : (0:ℝ) ≤ 1 / n := by positivity
  have hb := rpow_neg_ge_one_sub (1 / n) σ hu hσ
  have hsplit : ((n + 1 : ℕ) : ℝ) = (n : ℝ) * (1 + 1 / n) := by
    push_cast
    field_simp
  have hmul : ((n + 1 : ℕ) : ℝ) ^ (-σ) = (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ) := by
    rw [hsplit, Real.mul_rpow hn0.le (by positivity)]
  rw [hmul]
  have hnσ : (0:ℝ) < (n : ℝ) ^ (-σ) := Real.rpow_pos_of_pos hn0 _
  have hkey : (n : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ)
      ≤ (n : ℝ) ^ (-σ) * (σ * (1 / n)) := by
    have h1 : (n : ℝ) ^ (-σ) * (1 - σ * (1 / n)) ≤ (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ) :=
      mul_le_mul_of_nonneg_left hb hnσ.le
    nlinarith [h1]
  calc (n : ℝ) ^ (-σ) - (n : ℝ) ^ (-σ) * (1 + 1 / n) ^ (-σ)
      ≤ (n : ℝ) ^ (-σ) * (σ * (1 / n)) := hkey
    _ = σ * ((n : ℝ) ^ (-σ) * (n : ℝ) ^ (-(1:ℝ))) := by
        rw [Real.rpow_neg_one]
        field_simp
    _ = σ * (n : ℝ) ^ (-σ - 1) := by
        rw [← Real.rpow_add hn0]
        ring_nf
/-- **The E-series is differentiable on `Re s > 9/10`** (Siegel brick A2g-a2): with
    `|E(n)| ≤ C·n^{3/4}(1+log n)` and `E(0) = 0`, the series
    `s ↦ Σ' E(n)(n^{−s} − (n+1)^{−s})` is differentiable at every point of the
    half-plane — the analytic error part of the continuation `G`, via Mathlib's
    Weierstrass M-test `differentiableOn_tsum_of_summable_norm` on windows. -/
theorem eseries_differentiableAt (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) :
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
      have h2 := cpow_diff_kernel_bound n hn1 w hwσ
      have h3 := rpow_diff_le n hn1 w.re hwσ.le
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
/-- Linear-growth sequences give absolutely convergent Abel series (A2g-c-i):
    the summability half of `lseries_eq_tsum_abel`, exposed standalone. -/
lemma abel_tsum_summable (b : ℕ → ℂ) (C : ℝ)
    (hb : ∀ n : ℕ, ‖b n‖ ≤ C * n)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => b n * (((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s))) := by
  have hC0 : 0 ≤ C := by
    have h0 := hb 1
    have h1 : (0:ℝ) ≤ ‖b 1‖ := norm_nonneg _
    have h2 : C * ((1:ℕ):ℝ) = C := by norm_num
    linarith [h0, h1, h2.le, h2.ge]
  have hσ0 : (0:ℝ) < s.re := by linarith
  set w : ℕ → ℝ := fun n => ((n:ℝ)) ^ (-s.re) with hw
  have hwanti : ∀ n : ℕ, 1 ≤ n → w (n + 1) ≤ w n := by
    intro n hn
    rw [hw]
    simp only
    apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hn) (by push_cast; linarith)
    linarith
  apply Summable.of_norm_bounded
    (g := fun n : ℕ => (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))))
  · apply summable_of_sum_range_le (c := (C * (‖s‖ / s.re)) * (s.re / (s.re - 1)))
    · intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · simp
      · apply mul_nonneg (by positivity)
        apply mul_nonneg (Nat.cast_nonneg n)
        linarith [hwanti n hn0]
    · intro x
      have hIcc : ∑ i ∈ range x, (C * (‖s‖ / s.re)) * ((i:ℝ) * (w i - w (i + 1)))
          = (C * (‖s‖ / s.re)) * ∑ i ∈ Icc 1 (x - 1), ((i:ℝ) * (w i - w (i + 1))) := by
        rw [Finset.mul_sum]
        rcases Nat.eq_zero_or_pos x with rfl | hx0
        · simp
        · rw [show range x = insert 0 (Icc 1 (x - 1)) from by
            ext m
            simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
            omega]
          rw [Finset.sum_insert (by simp)]
          simp
      rw [hIcc, weighted_telescope w (x - 1)]
      have htail : (0:ℝ) ≤ ((x - 1 : ℕ):ℝ) * w ((x - 1) + 1) := by
        apply mul_nonneg (Nat.cast_nonneg _)
        rw [hw]
        simp only
        positivity
      have hsums : ∑ n ∈ Icc 1 (x - 1), w n ≤ s.re / (s.re - 1) := by
        have hterm : ∀ n ∈ Icc 1 (x - 1), w n = 1 / ((n:ℝ)) ^ s.re := by
          intro n hn
          obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
          rw [hw]
          simp only
          rw [Real.rpow_neg (Nat.cast_nonneg n), one_div]
        rw [Finset.sum_congr rfl hterm]
        calc ∑ n ∈ Icc 1 (x - 1), 1 / ((n:ℝ)) ^ s.re
            ≤ ∑' n : ℕ, (1:ℝ) / ((n:ℝ)) ^ s.re :=
              Summable.sum_le_tsum _ (fun n _ => by positivity)
                (Real.summable_one_div_nat_rpow.mpr hs)
          _ ≤ s.re / (s.re - 1) := tsum_one_div_nat_rpow_le s.re hs
      have hfac : (0:ℝ) ≤ C * (‖s‖ / s.re) := by positivity
      apply mul_le_mul_of_nonneg_left _ hfac
      linarith [hsums, htail]
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · have hb0 : ‖b 0‖ = 0 := by
        have h := hb 0
        have h2 : C * ((0:ℕ):ℝ) = 0 := by norm_num
        have := norm_nonneg (b 0)
        linarith [h, h2.le, h2.ge]
      rw [norm_mul, hb0, zero_mul]
      have hrhs : (C * (‖s‖ / s.re)) * (((0:ℕ):ℝ) * (w 0 - w (0 + 1))) = 0 := by
        norm_num
      rw [hrhs]
    · rw [norm_mul]
      have h1 := hb n
      have h2 := cpow_diff_kernel_bound n hn0 s hσ0
      calc ‖b n‖ * ‖((n:ℂ)) ^ (-s) - (((n + 1 : ℕ):ℂ)) ^ (-s)‖
          ≤ (C * n) * ((‖s‖ / s.re) * ((n : ℝ) ^ (-s.re) - ((n + 1 : ℕ) : ℝ) ^ (-s.re))) := by
            apply mul_le_mul h1 h2 (norm_nonneg _)
            positivity
        _ = (C * (‖s‖ / s.re)) * ((n:ℝ) * (w n - w (n + 1))) := by
            rw [hw]
            simp only
            push_cast
            ring
/-- Identity-theorem step on a convex open piece: agreement near one interior point
    propagates to the whole piece. -/
lemma eqOn_of_convex_piece (f g : ℂ → ℂ) (V : Set ℂ) (hVo : IsOpen V)
    (hVc : Convex ℝ V)
    (hf : DifferentiableOn ℂ f V) (hg : DifferentiableOn ℂ g V)
    (z₀ : ℂ) (hz₀ : z₀ ∈ V) (hseed : f =ᶠ[nhds z₀] g) :
    Set.EqOn f g V := by
  have hfa : AnalyticOnNhd ℂ f V := hf.analyticOnNhd hVo
  have hga : AnalyticOnNhd ℂ g V := hg.analyticOnNhd hVo
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hVc.isPreconnected hz₀ hseed
/-- **The identity theorem on the slit half-plane** (Siegel brick A2h-iii): two
    functions differentiable on `{Re > 9/10} ∖ {1}` that agree on `{Re > 1}` agree
    everywhere on the slit half-plane — by chaining through overlapping convex pieces
    (no slit-plane connectivity needed). -/
theorem eqOn_slit_halfplane (f g : ℂ → ℂ)
    (hf : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ f s)
    (hg : ∀ s : ℂ, 9/10 < s.re → s ≠ 1 → DifferentiableAt ℂ g s)
    (heq : ∀ s : ℂ, 1 < s.re → f s = g s)
    (s₀ : ℂ) (h₀re : 9/10 < s₀.re) (h₀ne : s₀ ≠ 1) : f s₀ = g s₀ := by
  -- the convex pieces
  set V₁ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ 0 < s.im} with hV₁
  set V₂ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ s.im < 0} with hV₂
  set V₃ : Set ℂ := {s : ℂ | 1 < s.re} with hV₃
  set V₄ : Set ℂ := {s : ℂ | 9/10 < s.re ∧ s.re < 1} with hV₄
  -- openness
  have hV₁o : IsOpen V₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hV₂o : IsOpen V₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hV₃o : IsOpen V₃ := isOpen_lt continuous_const Complex.continuous_re
  have hV₄o : IsOpen V₄ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  -- convexity: intersections of re/im half-spaces
  have hV₁c : Convex ℝ V₁ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_im_gt 0)
  have hV₂c : Convex ℝ V₂ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_im_lt 0)
  have hV₃c : Convex ℝ V₃ := convex_halfSpace_re_gt 1
  have hV₄c : Convex ℝ V₄ :=
    (convex_halfSpace_re_gt (9/10)).inter (convex_halfSpace_re_lt 1)
  -- every piece avoids 1 and sits in the domain
  have hne1 : ∀ {V : Set ℂ}, (∀ s ∈ V, 9/10 < s.re ∧ s ≠ 1) →
      DifferentiableOn ℂ f V ∧ DifferentiableOn ℂ g V := by
    intro V hV
    constructor
    · intro s hs
      exact ((hf s (hV s hs).1 (hV s hs).2).differentiableWithinAt)
    · intro s hs
      exact ((hg s (hV s hs).1 (hV s hs).2).differentiableWithinAt)
  have hdom₁ : ∀ s ∈ V₁, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  have hdom₂ : ∀ s ∈ V₂, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  have hdom₃ : ∀ s ∈ V₃, 9/10 < s.re ∧ s ≠ 1 := by
    intro s hs
    have h1 : 1 < s.re := hs
    refine ⟨by linarith, ?_⟩
    intro hc
    rw [hc] at h1
    simp at h1
  have hdom₄ : ∀ s ∈ V₄, 9/10 < s.re ∧ s ≠ 1 := by
    rintro s ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro hc
    rw [hc] at h2
    simp at h2
  obtain ⟨hf₁, hg₁⟩ := hne1 hdom₁
  obtain ⟨hf₂, hg₂⟩ := hne1 hdom₂
  obtain ⟨hf₄, hg₄⟩ := hne1 hdom₄
  -- seed on V₃ overlaps: 2 + i ∈ V₁ ∩ V₃, 2 − i ∈ V₂ ∩ V₃
  have hseed₁ : f =ᶠ[nhds (2 + Complex.I)] g := by
    have hmem : (2 + Complex.I) ∈ V₃ := by
      show (1:ℝ) < (2 + Complex.I).re
      simp
    filter_upwards [hV₃o.mem_nhds hmem] with w hw
    exact heq w hw
  have hseed₂ : f =ᶠ[nhds (2 - Complex.I)] g := by
    have hmem : (2 - Complex.I) ∈ V₃ := by
      show (1:ℝ) < (2 - Complex.I).re
      simp
    filter_upwards [hV₃o.mem_nhds hmem] with w hw
    exact heq w hw
  -- V₁, V₂ agreement
  have hEq₁ : Set.EqOn f g V₁ := by
    apply eqOn_of_convex_piece f g V₁ hV₁o hV₁c hf₁ hg₁ (2 + Complex.I) _ hseed₁
    constructor
    · show (9:ℝ)/10 < (2 + Complex.I).re
      simp
      norm_num
    · show (0:ℝ) < (2 + Complex.I).im
      simp
  have hEq₂ : Set.EqOn f g V₂ := by
    apply eqOn_of_convex_piece f g V₂ hV₂o hV₂c hf₂ hg₂ (2 - Complex.I) _ hseed₂
    constructor
    · show (9:ℝ)/10 < (2 - Complex.I).re
      simp
      norm_num
    · show (2 - Complex.I).im < 0
      simp
  -- V₄ agreement, seeded from V₁ at 19/20 + i/2
  have hmid : ((19:ℝ)/20 + Complex.I * (1/2)) ∈ V₁ ∩ V₄ := by
    constructor
    · constructor
      · show (9:ℝ)/10 < ((19:ℝ)/20 + Complex.I * (1/2)).re
        simp
        norm_num
      · show (0:ℝ) < ((19:ℝ)/20 + Complex.I * (1/2)).im
        simp
    · constructor
      · show (9:ℝ)/10 < ((19:ℝ)/20 + Complex.I * (1/2)).re
        simp
        norm_num
      · show ((19:ℝ)/20 + Complex.I * (1/2)).re < 1
        simp
        norm_num
  have hseed₄ : f =ᶠ[nhds ((19:ℝ)/20 + Complex.I * (1/2))] g := by
    filter_upwards [hV₁o.mem_nhds hmid.1] with w hw
    exact hEq₁ hw
  have hEq₄ : Set.EqOn f g V₄ := by
    apply eqOn_of_convex_piece f g V₄ hV₄o hV₄c hf₄ hg₄ _ hmid.2 hseed₄
  -- conclude by cases on s₀
  rcases lt_trichotomy s₀.re 1 with hlt | heq1 | hgt
  · exact hEq₄ ⟨h₀re, hlt⟩
  · -- re = 1: im ≠ 0
    have him : s₀.im ≠ 0 := by
      intro hc
      apply h₀ne
      apply Complex.ext
      · rw [heq1]
        simp
      · rw [hc]
        simp
    rcases lt_or_gt_of_ne him with hneg | hpos
    · exact hEq₂ ⟨h₀re, hneg⟩
    · exact hEq₁ ⟨h₀re, hpos⟩
  · exact heq s₀ hgt
/-- Complex log-Taylor remainder (A2h-i-a): for real `0 ≤ z ≤ 1/2`,
    `|log(1+z) − z| ≤ z²`. -/
lemma log_taylor_remainder (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2) :
    |Real.log (1 + z) - z| ≤ z ^ 2 := by
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- upper: log(1+z) ≤ z
  have hup : Real.log (1 + z) ≤ z := by
    have := Real.log_le_sub_one_of_pos h1z
    linarith
  -- lower: log(1+z) ≥ z − z² via log(1+z) = −log(1/(1+z)) and log(1/(1+z)) ≤ 1/(1+z) − 1
  have hlow : z - z ^ 2 ≤ Real.log (1 + z) := by
    have hinv : Real.log (1 / (1 + z)) ≤ 1 / (1 + z) - 1 := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 / (1 + z) by positivity)
      linarith
    have hneg : Real.log (1 / (1 + z)) = -Real.log (1 + z) := by
      rw [one_div, Real.log_inv]
    rw [hneg] at hinv
    have halg : 1 / (1 + z) - 1 = -z / (1 + z) := by
      field_simp
      ring
    rw [halg] at hinv
    -- −log(1+z) ≤ −z/(1+z) ⟹ log(1+z) ≥ z/(1+z) ≥ z − z²
    have hfrac : z - z ^ 2 ≤ z / (1 + z) := by
      rw [le_div_iff₀ h1z]
      nlinarith [h0, h1]
    have : z / (1 + z) ≤ Real.log (1 + z) := by
      have := neg_le_neg hinv
      simp only [neg_neg] at this
      calc z / (1 + z) = -(-z / (1 + z)) := by ring
        _ ≤ Real.log (1 + z) := by linarith [hinv]
    linarith
  rw [abs_le]
  constructor
  · linarith
  · nlinarith [hup, h0]
/-- **Second-order cpow Taylor bound** (Siegel brick A2h-i): for `w : ℂ` and real
    `0 ≤ z ≤ 1/2` with `‖w‖ ≤ W` and `W*z ≤ 1`,
    `‖(1+z)^w − 1 − wz‖ ≤ 4(W+1)²z²` — the engine of the ζ-truncation defect. -/
lemma cpow_taylor_two (w : ℂ) (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1/2)
    (W : ℝ) (hW : ‖w‖ ≤ W) (hWz : W * z ≤ 1) :
    ‖((1 + z : ℝ) : ℂ) ^ w - 1 - w * z‖ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
  have hW0 : 0 ≤ W := le_trans (norm_nonneg w) hW
  have h1z : (0:ℝ) < 1 + z := by linarith
  -- (1+z)^w = exp(w log(1+z))
  have hcpow : ((1 + z : ℝ) : ℂ) ^ w = Complex.exp (w * Real.log (1 + z)) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt h1z)]
    congr 1
    rw [Complex.ofReal_log h1z.le]
    ring
  rw [hcpow]
  -- split: exp(wL) − 1 − wz = [exp(wL) − 1 − wL] + w(L − z)
  set L : ℝ := Real.log (1 + z) with hL
  have hLz : |L - z| ≤ z ^ 2 := log_taylor_remainder z h0 h1
  have hLb : |L| ≤ z := by
    have h2 : 0 ≤ L := Real.log_nonneg (by linarith)
    have h3 : L ≤ z := by
      have := Real.log_le_sub_one_of_pos h1z
      rw [hL]
      linarith
    rw [abs_of_nonneg h2]
    exact h3
  have hwL : ‖w * (L : ℂ)‖ ≤ W * z := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hW hLb (abs_nonneg _) hW0
  -- ‖exp(u) − 1 − u‖ ≤ ‖u‖² for ‖u‖ ≤ 1
  have hexp2 : ‖Complex.exp (w * L) - 1 - w * L‖ ≤ ‖w * (L : ℂ)‖ ^ 2 := by
    have := Complex.norm_exp_sub_one_sub_id_le (x := w * (L : ℂ)) (by
      calc ‖w * (L : ℂ)‖ ≤ W * z := hwL
        _ ≤ 1 := hWz)
    exact this
  have hsplit : Complex.exp (w * L) - 1 - w * z
      = (Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z) := by
    ring
  rw [hsplit]
  have hterm2 : ‖w * ((L : ℂ) - z)‖ ≤ W * z ^ 2 := by
    rw [norm_mul, show ((L : ℂ) - (z : ℝ)) = (((L - z : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hW hLz (abs_nonneg _) hW0
  have hsq : ‖w * (L : ℂ)‖ ^ 2 ≤ (W * z) ^ 2 := by
    have h := norm_nonneg (w * (L : ℂ))
    nlinarith [hwL, h]
  calc ‖(Complex.exp (w * L) - 1 - w * L) + w * ((L : ℂ) - z)‖
      ≤ ‖Complex.exp (w * L) - 1 - w * L‖ + ‖w * ((L : ℂ) - z)‖ := norm_add_le _ _
    _ ≤ ‖w * (L : ℂ)‖ ^ 2 + W * z ^ 2 := add_le_add hexp2 hterm2
    _ ≤ (W * z) ^ 2 + W * z ^ 2 := by linarith [hsq]
    _ ≤ 4 * (W + 1) ^ 2 * z ^ 2 := by
        nlinarith [hW0, sq_nonneg z, sq_nonneg W, mul_nonneg hW0 (sq_nonneg z)]
/-- **The second-order Euler–Maclaurin kernel bound** (Siegel brick A2h-ii-α), in the
    `(s−1)`-cleared form: for `n ≥ 2`, `‖1−s‖ ≤ W`, `W/n ≤ 1`:
    `‖(s−1)n^{−s} − (n^{1−s} − (n+1)^{1−s})‖ ≤ 4(W+1)²·n^{−2}·n^{1−Re s}`. -/
lemma euler_maclaurin_kernel (s : ℂ) (n : ℕ) (hn2 : 2 ≤ n)
    (W : ℝ) (hW : ‖1 - s‖ ≤ W) (hWn : W * (1 / n) ≤ 1) :
    ‖(s - 1) * ((n:ℂ)) ^ (-s) - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))‖
      ≤ 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hnc0 : ((n:ℂ)) ≠ 0 := by
    exact_mod_cast (by omega : n ≠ 0)
  have hz1 : (1:ℝ) / n ≤ 1/2 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    push_cast
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn2]
  have hz0 : (0:ℝ) ≤ 1 / n := by positivity
  -- (n+1)^{1−s} = n^{1−s}·(1+1/n)^{1−s}
  have hsplit : (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)
      = ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) := by
    have hy0 : (0:ℝ) ≤ 1 + 1/(n:ℝ) := by positivity
    have hb : (((n + 1 : ℕ):ℂ)) = (((n:ℝ) : ℂ)) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) := by
      push_cast
      field_simp
    rw [hb, Complex.mul_cpow_ofReal_nonneg hn0.le hy0]
    norm_cast
  rw [hsplit]
  -- factor: LHS = n^{1−s}·[(1+1/n)^{1−s} − 1 − (1−s)(1/n)]
  have hpow : ((n:ℂ)) ^ ((1:ℂ) - s) = ((n:ℂ)) * ((n:ℂ)) ^ (-s) := by
    rw [show (1:ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ hnc0, Complex.cpow_one]
  have hnz : ((n:ℂ)) * ((1/(n:ℝ) : ℝ) : ℂ) = 1 := by
    have hc : ((1/(n:ℝ) : ℝ) : ℂ) = 1 / ((n:ℂ)) := by push_cast; ring
    rw [hc, mul_one_div, div_self hnc0]
  have hfactor : (s - 1) * ((n:ℂ)) ^ (-s)
      - (((n:ℂ)) ^ ((1:ℂ) - s) - ((n:ℂ)) ^ ((1:ℂ) - s) * (((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s))
      = ((n:ℂ)) ^ ((1:ℂ) - s)
        * ((((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)) := by
    rw [hpow]
    linear_combination (((1:ℂ) - s) * ((n:ℂ)) ^ (-s)) * hnz
  rw [hfactor, norm_mul]
  have hnorm1 : ‖((n:ℂ)) ^ ((1:ℂ) - s)‖ = ((n:ℝ)) ^ (1 - s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega)]
    simp [Complex.sub_re]
  rw [hnorm1]
  have hbr := cpow_taylor_two ((1:ℂ) - s) (1/(n:ℝ)) hz0 hz1 W hW hWn
  calc ((n:ℝ)) ^ (1 - s.re)
        * ‖(((1 + 1/(n:ℝ) : ℝ)) : ℂ) ^ ((1:ℂ) - s) - 1 - ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)‖
      ≤ ((n:ℝ)) ^ (1 - s.re) * (4 * (W + 1) ^ 2 * (1/(n:ℝ)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
        have hcast : ((1:ℂ) - s) * ((1/(n:ℝ) : ℝ) : ℂ)
            = ((1:ℂ) - s) * (1/(n:ℝ) : ℝ) := by norm_num
        rw [hcast]
        exact hbr
    _ = 4 * (W + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - s.re) := by ring
/-- Reverse Bernoulli (A2h-ii-β1): `(1+θu)(1−u)^θ ≤ 1` for `θ ≥ 0`, `0 ≤ u < 1` —
    hence `(n−1)^{1−p} − n^{1−p} ≥ (p−1)n^{−p}`. -/
lemma one_add_mul_rpow_one_sub_le (θ u : ℝ) (hθ : 0 ≤ θ) (h0 : 0 ≤ u) (h1 : u < 1) :
    (1 + θ * u) * (1 - u) ^ θ ≤ 1 := by
  have h1u : (0:ℝ) < 1 - u := by linarith
  -- (1−u)^θ ≤ e^{−θu}
  have hlog : Real.log (1 - u) ≤ -u := by
    have := Real.log_le_sub_one_of_pos h1u
    linarith
  have hpow : (1 - u) ^ θ ≤ Real.exp (-(θ * u)) := by
    rw [Real.rpow_def_of_pos h1u]
    apply Real.exp_le_exp.mpr
    calc Real.log (1 - u) * θ ≤ (-u) * θ := mul_le_mul_of_nonneg_right hlog hθ
      _ = -(θ * u) := by ring
  -- (1+w)e^{−w} ≤ 1 for w := θu ≥ 0
  have hw0 : 0 ≤ θ * u := mul_nonneg hθ h0
  have hexp : (1 + θ * u) * Real.exp (-(θ * u)) ≤ 1 := by
    have h2 := Real.add_one_le_exp (θ * u)
    have h3 : (0:ℝ) < Real.exp (θ * u) := Real.exp_pos _
    have h4 : Real.exp (-(θ * u)) = 1 / Real.exp (θ * u) := by
      rw [Real.exp_neg, one_div]
    rw [h4, mul_one_div, div_le_one h3]
    linarith
  calc (1 + θ * u) * (1 - u) ^ θ ≤ (1 + θ * u) * Real.exp (-(θ * u)) := by
        apply mul_le_mul_of_nonneg_left hpow (by linarith)
    _ ≤ 1 := hexp
/-- The decreasing-power telescoping comparison (A2h-ii-β2): for `p > 1`, `n ≥ 2`:
    `(p−1)·n^{−p} ≤ (n−1)^{1−p} − n^{1−p}` — each tail term is dominated by the
    telescoping antiderivative decrement. -/
lemma rpow_tail_term_le (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 2 ≤ n) :
    (p - 1) * ((n:ℝ)) ^ (-p) ≤ (((n - 1 : ℕ)):ℝ) ^ (1 - p) - ((n:ℝ)) ^ (1 - p) := by
  have hn0 : (0:ℝ) < (n:ℝ) := by
    have : (0:ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by
    have : (1:ℕ) ≤ n := by omega
    exact_mod_cast this
  set u : ℝ := 1 / n with hu
  have hu0 : 0 ≤ u := by positivity
  have hu1 : u < 1 := by
    rw [hu, div_lt_one hn0]
    linarith [show (2:ℝ) ≤ (n:ℝ) from by exact_mod_cast hn]
  have hcast : (((n - 1 : ℕ)):ℝ) = (n:ℝ) * (1 - u) := by
    rw [hu]
    push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
    field_simp
  have hber := one_add_mul_rpow_one_sub_le (p - 1) u (by linarith) hu0 hu1
  -- (n−1)^{1−p} = n^{1−p}·(1−u)^{1−p}; want n^{1−p}[(1−u)^{1−p} − 1] ≥ (p−1)n^{−p}
  have hsplit : (((n - 1 : ℕ)):ℝ) ^ (1 - p) = ((n:ℝ)) ^ (1 - p) * (1 - u) ^ (1 - p) := by
    rw [hcast, Real.mul_rpow hn0.le (by linarith)]
  rw [hsplit]
  have hnp : ((n:ℝ)) ^ (1 - p) = (n:ℝ) * ((n:ℝ)) ^ (-p) := by
    rw [show (1:ℝ) - p = 1 + (-p) by ring, Real.rpow_add hn0, Real.rpow_one]
  have hkey : 1 + (p - 1) * u ≤ (1 - u) ^ (1 - p) := by
    have hpow0 : (0:ℝ) < (1 - u) ^ (p - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hinv : (1 - u) ^ (1 - p) = ((1 - u) ^ (p - 1))⁻¹ := by
      rw [← Real.rpow_neg (by linarith : (0:ℝ) ≤ 1 - u)]
      congr 1
      ring
    rw [hinv, le_inv_comm₀ (by positivity) hpow0]
    calc (1 - u) ^ (p - 1) ≤ 1 / (1 + (p - 1) * u) := by
          rw [le_div_iff₀ (by nlinarith [mul_nonneg (show (0:ℝ) ≤ p - 1 by linarith) hu0])]
          calc (1 - u) ^ (p - 1) * (1 + (p - 1) * u)
              = (1 + (p - 1) * u) * (1 - u) ^ (p - 1) := by ring
            _ ≤ 1 := hber
      _ = (1 + (p - 1) * u)⁻¹ := one_div _
  -- assemble: n^{1−p}(1−u)^{1−p} − n^{1−p} ≥ n^{1−p}·(p−1)u = (p−1)n^{−p}
  have hnu : (n:ℝ) * u = 1 := by
    rw [hu]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hkey
    (Real.rpow_nonneg hn0.le (1 - p))
  have hfin : ((n:ℝ)) ^ (1 - p) * ((p - 1) * u) = (p - 1) * ((n:ℝ)) ^ (-p) := by
    rw [hnp]
    calc (n:ℝ) * ((n:ℝ)) ^ (-p) * ((p - 1) * u)
        = (p - 1) * ((n:ℝ)) ^ (-p) * ((n:ℝ) * u) := by ring
      _ = (p - 1) * ((n:ℝ)) ^ (-p) := by rw [hnu, mul_one]
  nlinarith [hmul, hfin.le, hfin.ge]
/-- **The p-tail bound** (Siegel brick A2h-ii-β): for `p > 1`, `1 ≤ x`:
    `Σ_{x<n≤z} n^{−p} ≤ x^{1−p}/(p−1)` — sharp telescoping, uniform in `z`. -/
lemma rpow_tail_sum_le (p : ℝ) (hp : 1 < p) (x : ℕ) (hx : 1 ≤ x) : ∀ z : ℕ, x ≤ z →
    ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p) ≤ ((x:ℝ)) ^ (1 - p) / (p - 1) := by
  have hp0 : (0:ℝ) < p - 1 := by linarith
  -- sharp form by induction: Σ ≤ (x^{1−p} − z^{1−p})/(p−1)
  have hsharp : ∀ z : ℕ, x ≤ z →
      ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p)
        ≤ (((x:ℝ)) ^ (1 - p) - ((z:ℝ)) ^ (1 - p)) / (p - 1) := by
    intro z
    induction z with
    | zero =>
      intro hx0
      omega
    | succ m ihm =>
      intro hxm
      rcases Nat.lt_or_ge m x with hlt | hge
      · have hx' : x = m + 1 := by omega
        subst hx'
        simp
      · have hstep : Icc (x + 1) (m + 1) = insert (m + 1) (Icc (x + 1) m) := by
          ext k
          simp only [Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [hstep, Finset.sum_insert (by simp)]
        have hterm := rpow_tail_term_le p hp (m + 1) (by omega)
        have hm1 : (m + 1 : ℕ) - 1 = m := by omega
        rw [hm1] at hterm
        have hih := ihm hge
        have hd : ((m + 1 : ℕ):ℝ) ^ (-p)
            ≤ (((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1) := by
          rw [le_div_iff₀ hp0]
          calc ((m + 1 : ℕ):ℝ) ^ (-p) * (p - 1) = (p - 1) * ((m + 1 : ℕ):ℝ) ^ (-p) := by ring
            _ ≤ ((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p) := hterm
        calc ((m + 1 : ℕ):ℝ) ^ (-p) + ∑ n ∈ Icc (x + 1) m, ((n:ℝ)) ^ (-p)
            ≤ (((m:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1)
              + (((x:ℝ)) ^ (1 - p) - ((m:ℝ)) ^ (1 - p)) / (p - 1) := add_le_add hd hih
          _ = (((x:ℝ)) ^ (1 - p) - ((m + 1 : ℕ):ℝ) ^ (1 - p)) / (p - 1) := by ring
  intro z hz
  have hzp : (0:ℝ) ≤ ((z:ℝ)) ^ (1 - p) := Real.rpow_nonneg (Nat.cast_nonneg z) _
  calc ∑ n ∈ Icc (x + 1) z, ((n:ℝ)) ^ (-p)
      ≤ (((x:ℝ)) ^ (1 - p) - ((z:ℝ)) ^ (1 - p)) / (p - 1) := hsharp z hz
    _ ≤ ((x:ℝ)) ^ (1 - p) / (p - 1) := by
        apply div_le_div_of_nonneg_right _ hp0.le
        linarith
/-- **The Euler–Maclaurin tail series is differentiable on `Re s > 9/10`**
    (Siegel brick A2h-ii-γ): `Wtail_x(s) := Σ'_n [n≥x]·((s−1)n^{−s} − (n^{1−s}−(n+1)^{1−s}))`
    is differentiable at every point of the half-plane — the continuation vehicle of the
    ζ-truncation. M-test on windows, head split off as a finite entire sum. -/
theorem wtail_differentiableAt (x : ℕ) (hx : 1 ≤ x) (s₀ : ℂ) (hs₀ : 9/10 < s₀.re) :
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
    have hker := euler_maclaurin_kernel w n hn2 W hWb hWn
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
/-- **The Euler–Maclaurin tail on `Re s > 1`** (Siegel brick A2h-ii-δ):
    `Wtail_x(s) = (s−1)·(ζ(s) − Σ_{n<x} n^{−s}) − x^{1−s}` — the closed form the
    identity theorem transports to the strip. -/
theorem wtail_eq_on_gt_one (x : ℕ) (hx : 1 ≤ x) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, (if n < x then 0 else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
    = (s - 1) * (riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        - ((x:ℂ)) ^ ((1:ℂ) - s) := by
  -- summability of the pieces
  have hzsum : Summable (fun n : ℕ => ((n:ℂ)) ^ (-s)) := by
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    apply h.congr
    intro n
    rw [Complex.cpow_neg, one_div]
  have hzsum_ite : Summable (fun n : ℕ => if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s)) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ => ‖((n:ℂ)) ^ (-s)‖) hzsum.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have hhead : Summable (fun n : ℕ => if n < x then ((n:ℂ)) ^ (-s) else 0) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htel_sum := tsum_cpow_telescope_summable x hx hs
  have hmul : Summable (fun n : ℕ => (s - 1) * (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))) :=
    hzsum_ite.mul_left (s - 1)
  -- ζ splits as head + tail
  have hzeta_split : riemannZeta s = (∑ n ∈ range x, ((n:ℂ)) ^ (-s))
      + ∑' n : ℕ, (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s)) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs]
    have hconv : ∀ n : ℕ, 1 / ((n:ℂ)) ^ s = ((n:ℂ)) ^ (-s) := by
      intro n
      rw [Complex.cpow_neg, one_div]
    rw [tsum_congr hconv]
    have hsplit : ∀ n : ℕ, ((n:ℂ)) ^ (-s)
        = (if n < x then ((n:ℂ)) ^ (-s) else 0) + (if n < x then 0 else ((n:ℂ)) ^ (-s)) := by
      intro n
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_pos h, add_zero]
      · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
    rw [tsum_congr hsplit, hhead.tsum_add hzsum_ite]
    congr 1
    rw [tsum_eq_sum (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos hn]
  have hz2 : ∑' n : ℕ, (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))
      = riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s) := by
    rw [hzeta_split]
    ring
  -- pointwise split of the V-term
  have hVsplit : ∀ n : ℕ, (if n < x then (0:ℂ) else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))))
      = (s - 1) * (if n < x then (0:ℂ) else ((n:ℂ)) ^ (-s))
        - (if n < x then (0:ℂ)
            else (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, if_pos h, mul_zero, sub_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), if_neg (not_lt.mpr h)]
  -- assemble
  rw [tsum_congr hVsplit, Summable.tsum_sub hmul htel_sum, tsum_mul_left,
    tsum_cpow_telescope x hx hs, hz2]
/-- **The ζ-truncation identity at real `β′ ∈ (9/10, 1)`** (Siegel brick A2h-ii-ε1):
    the closed form of `Wtail_x` continues through the pole-free slit — the identity
    theorem transports `wtail_eq_on_gt_one` from `Re > 1` to the strip. -/
theorem zeta_truncation_identity (x : ℕ) (hx : 1 ≤ x) {β : ℝ}
    (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    ∑' n : ℕ, (if n < x then 0 else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))
    = (((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) := by
  have hx0 : ((x:ℂ)) ≠ 0 := by
    have : x ≠ 0 := by omega
    exact_mod_cast this
  -- differentiability of each n^{−s} term (n = 0 is locally the zero function)
  have hterm0 : ∀ n : ℕ, ∀ s : ℂ, 9/10 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => ((n:ℂ)) ^ (-s)) s := by
    intro n s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · apply (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq
      have hopen : IsOpen {w : ℂ | 9/10 < w.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hs] with w hw
      rw [Nat.cast_zero, Complex.zero_cpow]
      intro hc
      have hw0 : w = 0 := by
        have := neg_eq_zero.mp hc
        exact this
      rw [hw0] at hw
      simp only [Set.mem_setOf_eq, Complex.zero_re] at hw
      linarith
    · have hn0 : ((n:ℂ)) ≠ 0 := by
        have : n ≠ 0 := by omega
        exact_mod_cast this
      exact ((Differentiable.neg differentiable_id).const_cpow
        (Or.inl hn0)).differentiableAt
  -- differentiability of the finite sum
  have hgsum : ∀ s : ℂ, 9/10 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => ∑ n ∈ range x, ((n:ℂ)) ^ (-s)) s := by
    intro s hs
    have h : DifferentiableAt ℂ (∑ n ∈ range x, fun s : ℂ => ((n:ℂ)) ^ (-s)) s := by
      apply DifferentiableAt.sum
      intro n _
      exact hterm0 n s hs
    have hfn : (fun s : ℂ => ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        = ∑ n ∈ range x, fun s : ℂ => ((n:ℂ)) ^ (-s) := by
      funext w
      rw [Finset.sum_apply]
    rw [hfn]
    exact h
  -- apply the identity theorem
  have h₀re : 9/10 < ((β:ℂ)).re := by
    rw [Complex.ofReal_re]
    exact hβ1
  have h₀ne : ((β:ℂ)) ≠ 1 := by
    intro h
    rw [Complex.ofReal_eq_one] at h
    linarith
  exact eqOn_slit_halfplane
    (fun s : ℂ => ∑' n : ℕ, (if n < x then 0 else ((s - 1) * ((n:ℂ)) ^ (-s)
        - (((n:ℂ)) ^ ((1:ℂ) - s) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - s)))))
    (fun s : ℂ => (s - 1) * (riemannZeta s - ∑ n ∈ range x, ((n:ℂ)) ^ (-s))
        - ((x:ℂ)) ^ ((1:ℂ) - s))
    (fun s hs _ => wtail_differentiableAt x hx s hs)
    (by
      intro s hs hs1
      apply DifferentiableAt.sub
      · apply DifferentiableAt.mul
        · exact (differentiable_id.sub (differentiable_const 1)).differentiableAt
        · apply DifferentiableAt.sub
          · exact differentiableAt_riemannZeta hs1
          · exact hgsum s hs
      · exact (((differentiable_const 1).sub differentiable_id).const_cpow
          (Or.inl hx0)).differentiableAt)
    (fun s hs => wtail_eq_on_gt_one x hx hs)
    ((β:ℂ)) h₀re h₀ne
/-- **THE ζ-TRUNCATION BOUND** (Siegel brick A2h-ii-ε): at real `β′ ∈ (9/10, 1)`,
    `‖(β′−1)(ζ(β′) − Σ_{n<x}n^{−β′}) − x^{1−β′}‖ ≤ 11·x^{−β′}` for `x ≥ 2` — the
    quantitative form the Goldfeld master inequality consumes. -/
theorem zeta_truncation (x : ℕ) (hx : 2 ≤ x) {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) :
    ‖(((β:ℂ)) - 1) * (riemannZeta (β:ℂ) - ∑ n ∈ range x, ((n:ℂ)) ^ (-(β:ℂ)))
        - ((x:ℂ)) ^ ((1:ℂ) - (β:ℂ))‖ ≤ 11 * ((x:ℝ)) ^ (-β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  rw [← zeta_truncation_identity x hx1 hβ1 hβ2]
  -- the pointwise kernel bound at s = β′
  have hpoint : ∀ n : ℕ, x ≤ n →
      ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
      ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans hx hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by
      have : (1:ℕ) ≤ n := by omega
      exact_mod_cast this
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hW : ‖1 - ((β:ℂ))‖ ≤ 1/10 := by
      rw [show (1:ℂ) - ((β:ℂ)) = (((1 - β : ℝ)):ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hWn : (1/10 : ℝ) * (1 / (n:ℝ)) ≤ 1 := by
      have h1 : (1:ℝ)/(n:ℝ) ≤ 1 := by
        rw [div_le_one hn0]
        linarith
      linarith
    have hker := euler_maclaurin_kernel ((β:ℂ)) n hn2 (1/10) hW hWn
    rw [Complex.ofReal_re] at hker
    have hcollect : (1/(n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) = ((n:ℝ)) ^ (-(1 + β)) := by
      have hpow2 : (1/(n:ℝ)) ^ 2 = ((n:ℝ)) ^ (-((2:ℕ):ℝ)) := by
        rw [div_pow, one_pow, one_div, ← Real.rpow_natCast (n:ℝ) 2,
          ← Real.rpow_neg hn0.le]
      rw [hpow2, ← Real.rpow_add hn0]
      congr 1
      push_cast
      ring
    calc ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
        ≤ 4 * (1/10 + 1) ^ 2 * (1 / (n:ℝ)) ^ 2 * ((n:ℝ)) ^ (1 - β) := hker
      _ = 4 * (1/10 + 1) ^ 2 * (((n:ℝ)) ^ (-(1 + β))) := by
          rw [← hcollect]
          ring
      _ ≤ 5 * ((n:ℝ)) ^ (-(1 + β)) := by
          have ht : (0:ℝ) ≤ ((n:ℝ)) ^ (-(1 + β)) := Real.rpow_nonneg hn0.le _
          nlinarith [ht]
  -- partial sums of the norms are uniformly ≤ 11 x^{−β}
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (-β) := Real.rpow_nonneg hx0.le _
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z,
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
      ≤ 11 * ((x:ℝ)) ^ (-β) := by
    intro z
    have hite : ∀ n ∈ range z,
        ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖
        = (if x ≤ n then ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
          - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 := hpoint x (le_refl x)
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1),
          ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
            - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 5 * ((n:ℝ)) ^ (-(1 + β))
          = 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β)) := by
        rw [Finset.mul_sum]
      have h4 := rpow_tail_sum_le (1 + β) (by linarith) x hx1 (z - 1) hm
      rw [show (1:ℝ) - (1 + β) = -β by ring, show (1:ℝ) + β - 1 = β by ring] at h4
      -- x-term: 5x^{−(1+β)} ≤ (5/2)x^{−β}
      have hxsplit : ((x:ℝ)) ^ (-(1 + β)) = ((x:ℝ)) ^ (-β) * ((x:ℝ)) ^ (-(1:ℝ)) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring
      have hxinv : ((x:ℝ)) ^ (-(1:ℝ)) ≤ 1/2 := by
        rw [Real.rpow_neg_one, ← one_div]
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast hx
      have h5 : 5 * ((x:ℝ)) ^ (-(1 + β)) ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) := by
        rw [hxsplit]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_left hxinv hxβ
      -- tail: 5·x^{−β}/β ≤ 5·x^{−β}·(10/9)
      have hβinv : (1:ℝ)/β ≤ 10/9 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      have h6 : ((x:ℝ)) ^ (-β) / β ≤ ((x:ℝ)) ^ (-β) * (10/9) := by
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_left hβinv hxβ
      calc ‖(((β:ℂ)) - 1) * ((x:ℂ)) ^ (-(β:ℂ))
            - (((x:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1),
              ‖(((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
                - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))‖
          ≤ 5 * ((x:ℝ)) ^ (-(1 + β))
            + 5 * (((x:ℝ)) ^ (-β) / β) := by
            have := le_trans h2 (le_of_eq h3)
            have h7 : 5 * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(1 + β))
                ≤ 5 * (((x:ℝ)) ^ (-β) / β) := by
              apply mul_le_mul_of_nonneg_left h4 (by norm_num)
            linarith
        _ ≤ 5 * (((x:ℝ)) ^ (-β) * (1/2)) + 5 * (((x:ℝ)) ^ (-β) * (10/9)) := by
            have h8 : 5 * (((x:ℝ)) ^ (-β) / β) ≤ 5 * (((x:ℝ)) ^ (-β) * (10/9)) :=
              mul_le_mul_of_nonneg_left h6 (by norm_num)
            linarith
        _ ≤ 11 * ((x:ℝ)) ^ (-β) := by linarith
  -- summability of the norms
  have hnorm_sum : Summable (fun n : ℕ =>
      ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖) := by
    have hmaj : Summable (fun n : ℕ => (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr (by linarith))
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hmaj
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg (not_lt.mpr h)]
      have hn0 : (0:ℝ) < (n:ℝ) := by
        have : (0:ℕ) < n := by omega
        exact_mod_cast this
      have heq : (5:ℝ) * (1 / ((n:ℝ)) ^ (1 + β)) = 5 * ((n:ℝ)) ^ (-(1 + β)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n h
  -- assemble
  calc ‖∑' n : ℕ, (if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ)))))‖
      ≤ ∑' n : ℕ, ‖if n < x then (0:ℂ) else ((((β:ℂ)) - 1) * ((n:ℂ)) ^ (-(β:ℂ))
        - (((n:ℂ)) ^ ((1:ℂ) - (β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ ((1:ℂ) - (β:ℂ))))‖ :=
        norm_tsum_le_tsum_norm hnorm_sum
    _ ≤ 11 * ((x:ℝ)) ^ (-β) :=
        hnorm_sum.tsum_le_of_sum_range_le hpartial
/-- Real-cast bridge for cpow at real exponents (A2h-iv-b0). -/
lemma cpow_real_cast (n : ℕ) (β : ℝ) :
    ((n:ℂ)) ^ (-(β:ℂ)) = ((((n:ℝ)) ^ (-β) : ℝ) : ℂ) := by
  rw [show -(β:ℂ) = (((-β : ℝ)):ℂ) from by push_cast; ring,
    show ((n:ℂ)) = (((n:ℝ)):ℂ) from by push_cast; ring]
  exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-β)).symm
/-- The E-Abel term is real at real exponents (A2h-iv-b0'). -/
lemma eabel_term_real (E : ℕ → ℝ) (n : ℕ) (β : ℝ) :
    ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
    = (((E n * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)) : ℝ)) : ℂ) := by
  rw [cpow_real_cast n β, cpow_real_cast (n + 1) β]
  push_cast
  ring
/-- **The E-Abel tail bound** (Siegel brick A2h-iv-b): with `|E(n)| ≤ C·n^{3/4}(1+log n)`,
    at real `β ∈ (9/10, 1)` the series tail beyond `x` is `≤ 400C·x^{7/8−β}` — the error
    that the choice `9/10 > 7/8` makes vanish. -/
theorem eabel_tail_bound (E : ℕ → ℝ) (C : ℝ) (hC0 : 0 ≤ C) (hE0 : E 0 = 0)
    (hE : ∀ n : ℕ, 1 ≤ n → |E n| ≤ C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n)))
    {β : ℝ} (hβ1 : 9/10 < β) (hβ2 : β < 1) (x : ℕ) (hx : 2 ≤ x) :
    ‖(∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      - ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
    ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
  have hx1 : 1 ≤ x := by omega
  have hx0 : (0:ℝ) < (x:ℝ) := by
    have : (0:ℕ) < x := by omega
    exact_mod_cast this
  have hβ0 : (0:ℝ) < β := by linarith
  have hp1 : (1:ℝ) < β + 1/8 := by linarith
  -- the pointwise majorant: ‖E(n)Δn‖ ≤ 9C·n^{−(β+1/8)} for n ≥ 1
  have hpoint : ∀ n : ℕ, 1 ≤ n →
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
    intro n hn
    have hn1r : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    rw [eabel_term_real, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hΔ0 : (0:ℝ) ≤ ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := by
      have hmono : (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β) := by
        apply Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith)
        linarith
      linarith
    have hΔle : ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) ≤ ((n:ℝ)) ^ (-β - 1) := by
      calc ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)
          ≤ β * ((n:ℝ)) ^ (-β - 1) := rpow_diff_le n hn β hβ0.le
        _ ≤ 1 * ((n:ℝ)) ^ (-β - 1) := by
            apply mul_le_mul_of_nonneg_right (by linarith)
            exact Real.rpow_nonneg hn0.le _
        _ = ((n:ℝ)) ^ (-β - 1) := one_mul _
    have hlogbound : 1 + Real.log n ≤ 9 * ((n:ℝ)) ^ ((1:ℝ)/8) := by
      have h1 : Real.log n ≤ ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) :=
        Real.log_le_rpow_div hn0.le (by norm_num)
      have h2 : ((n:ℝ)) ^ ((1:ℝ)/8) / (1/8) = 8 * ((n:ℝ)) ^ ((1:ℝ)/8) := by ring
      have h3 : (1:ℝ) ≤ ((n:ℝ)) ^ ((1:ℝ)/8) :=
        Real.one_le_rpow hn1r (by norm_num)
      linarith [h1, h2.le, h2.ge, h3]
    have hlog0 : (0:ℝ) ≤ 1 + Real.log n := by
      have := Real.log_nonneg hn1r
      linarith
    have hEn := hE n hn
    have habs : |((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β)|
        = ((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β) := abs_of_nonneg hΔ0
    rw [habs]
    have hcollect : ((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)
        = ((n:ℝ)) ^ (-(β + 1/8)) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1
      ring
    calc |E n| * (((n:ℝ)) ^ (-β) - (((n + 1 : ℕ)):ℝ) ^ (-β))
        ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (1 + Real.log n))) * (((n:ℝ)) ^ (-β - 1)) := by
          exact mul_le_mul hEn hΔle hΔ0 (by positivity)
      _ ≤ (C * (((n:ℝ)) ^ ((3:ℝ)/4) * (9 * ((n:ℝ)) ^ ((1:ℝ)/8)))) * (((n:ℝ)) ^ (-β - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
          apply mul_le_mul_of_nonneg_left _ hC0
          apply mul_le_mul_of_nonneg_left hlogbound (Real.rpow_nonneg hn0.le _)
      _ = 9 * C * (((n:ℝ)) ^ ((3:ℝ)/4) * ((n:ℝ)) ^ ((1:ℝ)/8) * ((n:ℝ)) ^ (-β - 1)) := by
          ring
      _ = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by rw [hcollect]
  -- summability of the terms
  have hsummable : Summable (fun n : ℕ => ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    have hmaj : Summable (fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) :=
      Summable.mul_left _ (Real.summable_one_div_nat_rpow.mpr hp1)
    apply Summable.of_norm_bounded
      (g := fun n : ℕ => (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))) hmaj
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hE0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have heq : (9 * C) * (1 / ((n:ℝ)) ^ (β + 1/8))
          = 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [one_div, ← Real.rpow_neg hn0.le]
      rw [heq]
      exact hpoint n hn
  -- the finite sum is the range-x head (the n = 0 term vanishes)
  have hhead : ∑ n ∈ Icc 1 (x - 1), ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = ∑ n ∈ range x, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) := by
    rw [show range x = insert 0 (Icc 1 (x - 1)) from by
      ext m
      simp only [Finset.mem_insert, Finset.mem_range, Finset.mem_Icc]
      omega, Finset.sum_insert (by
        simp only [Finset.mem_Icc]
        omega)]
    rw [hE0]
    simp
  rw [hhead]
  -- head/tail split of the tsum
  have hsplit : ∀ n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
      = (if n < x then ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
        + (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, if_pos h, add_zero]
    · rw [if_neg (not_lt.mpr h), if_neg (not_lt.mpr h), zero_add]
  have hheadsum : Summable (fun n : ℕ => (if n < x then ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)) :=
    summable_of_ne_finset_zero (s := range x) (by
      intro n hn
      rw [Finset.mem_range] at hn
      rw [if_neg hn])
  have htailsum : Summable (fun n : ℕ => (if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := by
    apply Summable.of_norm_bounded (g := fun n : ℕ =>
      ‖((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖)
      hsummable.norm
    intro n
    rcases Nat.lt_or_ge n x with h | h
    · rw [if_pos h, norm_zero]
      exact norm_nonneg _
    · rw [if_neg (not_lt.mpr h)]
  have htsum_split : (∑' n : ℕ, ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
      = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
        + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
    calc ∑' n : ℕ, ((E n : ℝ) : ℂ) * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))
        = ∑' n : ℕ, ((if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0)
            + (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))) := tsum_congr hsplit
      _ = (∑' n : ℕ, (if n < x then ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))) else 0))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) :=
          hheadsum.tsum_add htailsum
      _ = (∑ n ∈ range x, ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))
            + ∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))) := by
          congr 1
          rw [tsum_eq_sum (s := range x) (by
            intro n hn
            rw [Finset.mem_range] at hn
            rw [if_neg hn])]
          apply Finset.sum_congr rfl
          intro n hn
          rw [Finset.mem_range] at hn
          rw [if_pos hn]
  rw [htsum_split]
  rw [show ∀ (u v : ℂ), u + v - u = v from fun u v => by ring]
  -- bound the tail tsum by its norms
  have hxβ : (0:ℝ) ≤ ((x:ℝ)) ^ (7/8 - β) := Real.rpow_nonneg hx0.le _
  have hnormsum : Summable (fun n : ℕ => ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖) := htailsum.norm
  have hpartial : ∀ z : ℕ, ∑ n ∈ range z, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
      * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
      ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by
    intro z
    have hite : ∀ n ∈ range z, ‖if n < x then (0:ℂ) else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
        = (if x ≤ n then ‖((E n : ℝ) : ℂ)
          * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ else 0) := by
      intro n _
      rcases Nat.lt_or_ge n x with h | h
      · rw [if_pos h, if_neg (by omega), norm_zero]
      · rw [if_neg (not_lt.mpr h), if_pos h]
    rw [Finset.sum_congr rfl hite, ← Finset.sum_filter]
    have hset : (range z).filter (fun n => x ≤ n) = Icc x (z - 1) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hset]
    rcases Nat.lt_or_ge (z - 1) x with hm | hm
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      positivity
    · rw [show Icc x (z - 1) = insert x (Icc (x + 1) (z - 1)) from by
        ext n
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega, Finset.sum_insert (by simp)]
      have h1 : ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) := hpoint x hx1
      have h2 : ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
            * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8)) := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
        exact hpoint n (by omega)
      have h3 : ∑ n ∈ Icc (x + 1) (z - 1), 9 * C * ((n:ℝ)) ^ (-(β + 1/8))
          = 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8)) := by
        rw [Finset.mul_sum]
      have h4 := rpow_tail_sum_le (β + 1/8) hp1 x hx1 (z - 1) hm
      rw [show (1:ℝ) - (β + 1/8) = 7/8 - β by ring,
        show β + 1/8 - 1 = β - 7/8 by ring] at h4
      have hdenom : ((x:ℝ)) ^ (7/8 - β) / (β - 7/8) ≤ 40 * ((x:ℝ)) ^ (7/8 - β) := by
        rw [div_le_iff₀ (by linarith)]
        have h5 : (1:ℝ) ≤ 40 * (β - 7/8) := by linarith
        nlinarith [hxβ]
      have hxterm : ((x:ℝ)) ^ (-(β + 1/8)) ≤ ((x:ℝ)) ^ (7/8 - β) := by
        apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx1)
        linarith
      calc ‖((E x : ℝ) : ℂ) * (((x:ℂ)) ^ (-(β:ℂ)) - (((x + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
            + ∑ n ∈ Icc (x + 1) (z - 1), ‖((E n : ℝ) : ℂ)
              * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖
          ≤ 9 * C * ((x:ℝ)) ^ (-(β + 1/8))
            + 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
            have h6 : 9 * C * ∑ n ∈ Icc (x + 1) (z - 1), ((n:ℝ)) ^ (-(β + 1/8))
                ≤ 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8)) := by
              apply mul_le_mul_of_nonneg_left h4 (by positivity)
            linarith [le_trans h2 (le_of_eq h3), h1, h6,
              le_trans (le_trans h2 (le_of_eq h3)) h6]
        _ ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) + 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) := by
            have h7 : 9 * C * ((x:ℝ)) ^ (-(β + 1/8)) ≤ 9 * C * ((x:ℝ)) ^ (7/8 - β) :=
              mul_le_mul_of_nonneg_left hxterm (by positivity)
            have h8 : 9 * C * (((x:ℝ)) ^ (7/8 - β) / (β - 7/8))
                ≤ 9 * C * (40 * ((x:ℝ)) ^ (7/8 - β)) :=
              mul_le_mul_of_nonneg_left hdenom (by positivity)
            linarith
        _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) := by nlinarith [hxβ, hC0]
  calc ‖∑' n : ℕ, (if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ))))‖
      ≤ ∑' n : ℕ, ‖if n < x then 0 else ((E n : ℝ) : ℂ)
        * (((n:ℂ)) ^ (-(β:ℂ)) - (((n + 1 : ℕ):ℂ)) ^ (-(β:ℂ)))‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ 400 * C * ((x:ℝ)) ^ (7/8 - β) :=
        hnormsum.tsum_le_of_sum_range_le hpartial
/-- Values of a quadratic Dirichlet character lie in `{−1, 0, 1}` (A3-d1). -/
lemma real_char_repr {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (a : ZMod q) : χ a = -1 ∨ χ a = 0 ∨ χ a = 1 := by
  by_cases hu : IsUnit a
  · have hsq : χ a * χ a = 1 := by
      have h1 : (χ ^ 2) a = 1 := by
        rw [hχ2]
        exact MulChar.one_apply hu
      rw [pow_two, MulChar.mul_apply] at h1
      exact h1
    have hfactor : (χ a - 1) * (χ a + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp hfactor with h | h
    · right; right
      exact sub_eq_zero.mp h
    · left
      have := eq_neg_of_add_eq_zero_left h
      exact this
  · right; left
    exact MulChar.map_nonunit χ hu
/-- The bare real-valued function of a quadratic Dirichlet character (A3-d0). -/
noncomputable def charFn (q : ℕ) (χ : DirichletCharacter ℂ q) : ℕ → ℝ :=
  fun n => (χ ((n : ZMod q))).re
/-- `charFn` takes values in `{−1, 0, 1}` (A3-d3). -/
lemma charFn_values {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    charFn q χ n = -1 ∨ charFn q χ n = 0 ∨ charFn q χ n = 1 := by
  rcases real_char_repr χ hχ2 ((n : ZMod q)) with h | h | h <;>
    rw [charFn, h] <;> norm_num
/-- `charFn` is bounded by 1 (A3-d3'). -/
lemma charFn_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1) (n : ℕ) :
    |charFn q χ n| ≤ 1 := by
  rcases charFn_values χ hχ2 n with h | h | h <;> rw [h] <;> norm_num
/-- Convolving a power-bounded arithmetic function with a 1-bounded bare function
    raises the power by one (A3-g1a helper). -/
lemma conv_abs_le_pow (F : ArithmeticFunction ℝ) (k : ℕ → ℝ) (t : ℕ)
    (hF : ∀ j : ℕ, |F j| ≤ ((j:ℝ)) ^ t) (hkb : ∀ j, |k j| ≤ 1) (m : ℕ) :
    |(F * toArith k) m| ≤ ((m:ℝ)) ^ (t + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ArithmeticFunction.map_zero, abs_zero, Nat.cast_zero, zero_pow (by omega)]
  · have hkb' : ∀ j : ℕ, |toArith k j| ≤ 1 := by
      intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [toArith]
      · rw [toArith_apply k j (by omega)]
        exact hkb j
    rw [ArithmeticFunction.mul_apply]
    calc |∑ p ∈ m.divisorsAntidiagonal, F p.1 * toArith k p.2|
        ≤ ∑ p ∈ m.divisorsAntidiagonal, |F p.1 * toArith k p.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ m.divisorsAntidiagonal, ((m:ℝ)) ^ t := by
          apply Finset.sum_le_sum
          intro p hp
          obtain ⟨he, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
          have hp1m : p.1 ≤ m := Nat.le_of_dvd hm (Dvd.intro p.2 he)
          have hcast : ((p.1:ℝ)) ^ t ≤ ((m:ℝ)) ^ t :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hp1m) t
          rw [abs_mul]
          calc |F p.1| * |toArith k p.2| ≤ ((p.1:ℝ)) ^ t * 1 :=
                mul_le_mul (hF p.1) (hkb' p.2) (abs_nonneg _)
                  (le_trans (abs_nonneg _) (hF p.1))
            _ = ((p.1:ℝ)) ^ t := mul_one _
            _ ≤ ((m:ℝ)) ^ t := hcast
      _ = (m.divisorsAntidiagonal.card : ℝ) * ((m:ℝ)) ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((m:ℝ)) * ((m:ℝ)) ^ t := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : m.divisorsAntidiagonal.card ≤ m := by
            have hmap : ∀ p ∈ m.divisorsAntidiagonal, p.1 ∈ Icc 1 m := by
              intro p hp
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              rw [Finset.mem_Icc]
              constructor
              · by_contra h0
                push_neg at h0
                have h1 : p.1 = 0 := by omega
                rw [h1, zero_mul] at he
                omega
              · exact Nat.le_of_dvd hm (Dvd.intro p.2 he)
            have hinj : ∀ p ∈ m.divisorsAntidiagonal, ∀ p' ∈ m.divisorsAntidiagonal,
                p.1 = p'.1 → p = p' := by
              intro p hp p' hp' hfst
              obtain ⟨he, hm0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
              obtain ⟨he', _⟩ := Nat.mem_divisorsAntidiagonal.mp hp'
              have h1 : p.1 ≠ 0 := by
                intro h0
                rw [h0, zero_mul] at he
                omega
              have h2 : p.2 = p'.2 := by
                apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1)
                rw [he, hfst, he']
              exact Prod.ext hfst h2
            calc m.divisorsAntidiagonal.card ≤ (Icc 1 m).card :=
                  Finset.card_le_card_of_injOn (fun p => p.1)
                    (fun p hp => hmap p hp)
                    (fun p hp p' hp' h => hinj p hp p' hp' h)
              _ = m := by rw [Nat.card_Icc]; omega
          exact_mod_cast hcard
      _ = ((m:ℝ)) ^ (t + 1) := by ring
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
/-- **The √-size partial sums against `d^{−s}` decay at the `1/√y` rate, uniformly
    in `s ∈ [1,2]`** (Siegel brick A5-d1) — the convolution-side twin of
    `char_rpow_tail_rate`, powering the `Lk` identification. -/
lemma conv_rpow_tail_rate (k : ℕ → ℝ) (B : ℝ)
    (hK : ∀ t : ℕ, |∑ n ∈ Icc 1 t, k n| ≤ B * (Real.sqrt t + 1))
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (y : ℕ) (hy1 : 1 ≤ y) :
    ∀ z : ℕ, y ≤ z →
    |∑ d ∈ Icc (y + 1) z, k d * ((d:ℝ)) ^ (-s)| ≤ 30 * B / Real.sqrt y := by
  have hB0 : 0 ≤ B := by
    have h0 := hK 0
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, abs_zero,
      Nat.cast_zero, Real.sqrt_zero, zero_add, mul_one] at h0
    exact h0
  set w : ℕ → ℝ := fun d => ((d:ℝ)) ^ (-s) with hw
  -- the Abel window identity (generic in w)
  have hwindow : ∀ z : ℕ, y ≤ z →
      ∑ d ∈ Icc (y + 1) z, k d * w d
      = ∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1) := by
    intro z
    induction z with
    | zero =>
      intro hy0
      omega
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
        have hS : ∑ n ∈ Icc 1 (m + 1), k n = k (m + 1) + ∑ n ∈ Icc 1 m, k n := by
          rw [show Icc 1 (m + 1) = insert (m + 1) (Icc 1 m) from by
            ext d
            simp only [Finset.mem_insert, Finset.mem_Icc]
            omega, Finset.sum_insert (by
              simp only [Finset.mem_Icc]
              omega)]
        rw [hS]
        ring
  -- per-term kernel bound: |S d|(w d − w(d+1)) ≤ 4B/(d√d) for d ≥ 1
  have hkernel : ∀ d : ℕ, 1 ≤ d →
      |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| ≤ 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
    intro d hd
    have hd0 : (0:ℝ) < (d:ℝ) := by
      have : (0:ℕ) < d := hd
      exact_mod_cast this
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    have hsq1 : (1:ℝ) ≤ Real.sqrt d := Real.one_le_sqrt.mpr hd1r
    have hΔ0 : 0 ≤ w d - w (d + 1) := by
      rw [hw]
      simp only
      have : (((d + 1 : ℕ)):ℝ) ^ (-s) ≤ ((d:ℝ)) ^ (-s) := by
        apply Real.rpow_le_rpow_of_nonpos hd0 (by push_cast; linarith)
        linarith
      push_cast at this ⊢
      linarith
    have hΔle : w d - w (d + 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
      rw [hw]
      simp only
      have h1 := rpow_diff_le d hd s (by linarith)
      have h2 : ((d:ℝ)) ^ (-s - 1) ≤ ((d:ℝ)) ^ (-(2:ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hd1r
        linarith
      have h3 : s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
        calc s * ((d:ℝ)) ^ (-s - 1) ≤ 2 * ((d:ℝ)) ^ (-s - 1) := by
              apply mul_le_mul_of_nonneg_right hs2 (Real.rpow_nonneg hd0.le _)
          _ ≤ 2 * ((d:ℝ)) ^ (-(2:ℝ)) := by
              apply mul_le_mul_of_nonneg_left h2 (by norm_num)
      push_cast at h1 ⊢
      linarith
    have hSb : |∑ n ∈ Icc 1 d, k n| ≤ 2 * B * Real.sqrt d := by
      calc |∑ n ∈ Icc 1 d, k n| ≤ B * (Real.sqrt d + 1) := hK d
        _ ≤ B * (Real.sqrt d + Real.sqrt d) := by
            apply mul_le_mul_of_nonneg_left _ hB0
            linarith
        _ = 2 * B * Real.sqrt d := by ring
    have hrpow2 : ((d:ℝ)) ^ (-(2:ℝ)) = 1 / ((d:ℝ) * (d:ℝ)) := by
      rw [show (-(2:ℝ)) = -(((2:ℕ)):ℝ) from by norm_num, Real.rpow_neg hd0.le,
        Real.rpow_natCast, pow_two, one_div]
    have hcollect : Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ))) = 1 / ((d:ℝ) * Real.sqrt d) := by
      rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity), one_mul]
      calc Real.sqrt d * ((d:ℝ) * Real.sqrt d)
          = (Real.sqrt d * Real.sqrt d) * (d:ℝ) := by ring
        _ = (d:ℝ) * (d:ℝ) := by rw [Real.mul_self_sqrt hd0.le]
    rw [abs_mul, abs_of_nonneg hΔ0]
    calc |∑ n ∈ Icc 1 d, k n| * (w d - w (d + 1))
        ≤ (2 * B * Real.sqrt d) * (2 * ((d:ℝ)) ^ (-(2:ℝ))) := by
          apply mul_le_mul hSb hΔle hΔ0
          positivity
      _ = 4 * B * (Real.sqrt d * ((d:ℝ)) ^ (-(2:ℝ))) := by ring
      _ = 4 * B * (Real.sqrt d * (1 / ((d:ℝ) * (d:ℝ)))) := by rw [hrpow2]
      _ = 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by rw [hcollect]
  intro z hz
  rw [hwindow z hz]
  have hy0 : (0:ℝ) < (y:ℝ) := by
    have : (0:ℕ) < y := hy1
    exact_mod_cast this
  have hz0 : (0:ℝ) < (z:ℝ) := by
    have : (0:ℕ) < z := by omega
    exact_mod_cast this
  have hsqy : (1:ℝ) ≤ Real.sqrt y := Real.one_le_sqrt.mpr (by exact_mod_cast hy1)
  have hsqy0 : (0:ℝ) < Real.sqrt y := by linarith
  have hsqz0 : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.mpr hz0
  -- the three pieces
  have h1 : |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
      ≤ 8 * B / Real.sqrt y := by
    calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        ≤ ∑ d ∈ Icc (y + 1) z, |(∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc (y + 1) z, 4 * B * (1 / ((d:ℝ) * Real.sqrt d)) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          exact hkernel d (by omega)
      _ = 4 * B * ∑ d ∈ Icc (y + 1) z, (1 : ℝ) / (d * Real.sqrt d) := by
          rw [Finset.mul_sum]
      _ ≤ 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z) := by
          apply mul_le_mul_of_nonneg_left (sum_three_half_tail_sharp y hy1 z hz)
            (by positivity)
      _ ≤ 8 * B / Real.sqrt y := by
          have h3 : (0:ℝ) ≤ 4 * B * (2 / Real.sqrt z) := by positivity
          have heq : 4 * B * (2 / Real.sqrt y - 2 / Real.sqrt z)
              = 8 * B / Real.sqrt y - 4 * B * (2 / Real.sqrt z) := by ring
          linarith [heq.le, heq.ge]
  have hwle : ∀ t : ℕ, 1 ≤ t → w (t + 1) ≤ 1 / (t:ℝ) := by
    intro t ht
    have ht0 : (0:ℝ) < (t:ℝ) := by
      have : (0:ℕ) < t := ht
      exact_mod_cast this
    have ht1 : (1:ℝ) ≤ ((t + 1 : ℕ):ℝ) := by push_cast; linarith
    rw [hw]
    simp only
    calc ((t + 1 : ℕ):ℝ) ^ (-s) ≤ ((t + 1 : ℕ):ℝ) ^ (-(1:ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = 1 / ((t + 1 : ℕ):ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1 / (t:ℝ) := by
          apply one_div_le_one_div_of_le ht0
          push_cast
          linarith
  have hbz : |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0z : 0 ≤ w (z + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqzz : Real.sqrt z / (z:ℝ) = 1 / Real.sqrt z := by
      rw [eq_div_iff (ne_of_gt hsqz0)]
      field_simp
      exact Real.sq_sqrt hz0.le
    calc |(∑ n ∈ Icc 1 z, k n) * w (z + 1)|
        = |∑ n ∈ Icc 1 z, k n| * w (z + 1) := by rw [abs_mul, abs_of_nonneg hw0z]
      _ ≤ (2 * B * Real.sqrt z) * (1 / (z:ℝ)) := by
          apply mul_le_mul _ (hwle z (by omega)) hw0z (by positivity)
          calc |∑ n ∈ Icc 1 z, k n| ≤ B * (Real.sqrt z + 1) := hK z
            _ ≤ B * (Real.sqrt z + Real.sqrt z) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                have : (1:ℝ) ≤ Real.sqrt z := Real.one_le_sqrt.mpr (by
                  have : (1:ℕ) ≤ z := by omega
                  exact_mod_cast this)
                linarith
            _ = 2 * B * Real.sqrt z := by ring
      _ = 2 * B * (Real.sqrt z / (z:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt z) := by rw [hsqzz]
      _ ≤ 2 * B / Real.sqrt y := by
          rw [mul_one_div]
          apply div_le_div_of_nonneg_left (by linarith) hsqy0
          exact Real.sqrt_le_sqrt (by exact_mod_cast hz)
  have hby : |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| ≤ 2 * B / Real.sqrt y := by
    have hw0y : 0 ≤ w (y + 1) := by
      rw [hw]
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hsqyy : Real.sqrt y / (y:ℝ) = 1 / Real.sqrt y := by
      rw [eq_div_iff (ne_of_gt hsqy0)]
      field_simp
      exact Real.sq_sqrt hy0.le
    calc |(∑ n ∈ Icc 1 y, k n) * w (y + 1)|
        = |∑ n ∈ Icc 1 y, k n| * w (y + 1) := by rw [abs_mul, abs_of_nonneg hw0y]
      _ ≤ (2 * B * Real.sqrt y) * (1 / (y:ℝ)) := by
          apply mul_le_mul _ (hwle y hy1) hw0y (by positivity)
          calc |∑ n ∈ Icc 1 y, k n| ≤ B * (Real.sqrt y + 1) := hK y
            _ ≤ B * (Real.sqrt y + Real.sqrt y) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                linarith
            _ = 2 * B * Real.sqrt y := by ring
      _ = 2 * B * (Real.sqrt y / (y:ℝ)) := by ring
      _ = 2 * B * (1 / Real.sqrt y) := by rw [hsqyy]
      _ = 2 * B / Real.sqrt y := by rw [mul_one_div]
  calc |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
        + (∑ n ∈ Icc 1 z, k n) * w (z + 1) - (∑ n ∈ Icc 1 y, k n) * w (y + 1)|
      ≤ |∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))|
        + |(∑ n ∈ Icc 1 z, k n) * w (z + 1)| + |(∑ n ∈ Icc 1 y, k n) * w (y + 1)| := by
        have ha := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1))
          + (∑ n ∈ Icc 1 z, k n) * w (z + 1)) (-((∑ n ∈ Icc 1 y, k n) * w (y + 1)))
        have hb := abs_add_le (∑ d ∈ Icc (y + 1) z, (∑ n ∈ Icc 1 d, k n) * (w d - w (d + 1)))
          ((∑ n ∈ Icc 1 z, k n) * w (z + 1))
        rw [abs_neg, ← sub_eq_add_neg] at ha
        linarith
    _ ≤ 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y := by
        linarith [h1, hbz, hby]
    _ ≤ 30 * B / Real.sqrt y := by
        have h30 : (12:ℝ) * B / Real.sqrt y ≤ 30 * B / Real.sqrt y := by
          apply div_le_div_of_nonneg_right _ hsqy0.le
          linarith
        have heq : 8 * B / Real.sqrt y + 2 * B / Real.sqrt y + 2 * B / Real.sqrt y
            = 12 * B / Real.sqrt y := by ring
        linarith [heq.le, heq.ge, h30]
/-- **The head difference across the window** (Siegel brick S2c): moving the
    exponent from `β` to `1` across a window with `N^{1−β} ≤ 2` costs only
    `2(1−β)(1+log N)²` on partial sums of a quadratic character. -/
lemma char_head_diff_bound {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ2 : χ ^ 2 = 1)
    (N : ℕ) (hN : 1 ≤ N) {β : ℝ} (hβ1 : 0 < β) (hβ2 : β < 1)
    (hN2 : ((N:ℝ)) ^ (1 - β) ≤ 2) :
    |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
    ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
  have hNr : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlogN : (0:ℝ) ≤ Real.log N := Real.log_nonneg hNr
  -- per-term bound
  have hterm : ∀ d : ℕ, d ∈ Icc 1 N →
      |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)|
      ≤ 2 * (1 - β) * (Real.log d / d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd1r : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd.1
    have hd0 : (0:ℝ) < (d:ℝ) := by linarith
    have hlogd : (0:ℝ) ≤ Real.log d := Real.log_nonneg hd1r
    -- factor: 1/d − d^{−β} = −d^{−1}(d^{1−β} − 1)
    have hfac : charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)
        = -(charFn q χ d * (((d:ℝ)) ^ (1 - β) - 1) / d) := by
      have hrw : ((d:ℝ)) ^ (-β) = ((d:ℝ)) ^ (1 - β) / d := by
        rw [eq_div_iff (ne_of_gt hd0)]
        calc ((d:ℝ)) ^ (-β) * (d:ℝ) = ((d:ℝ)) ^ (-β) * ((d:ℝ)) ^ (1:ℝ) := by
              rw [Real.rpow_one]
          _ = ((d:ℝ)) ^ (-β + 1) := (Real.rpow_add hd0 _ _).symm
          _ = ((d:ℝ)) ^ (1 - β) := by ring_nf
      rw [hrw]
      field_simp
      ring
    rw [hfac, abs_neg, abs_div, Nat.abs_cast, abs_mul]
    -- d^{1−β} − 1 ≤ 2(1−β)log d
    have hexp : ((d:ℝ)) ^ (1 - β) - 1 ≤ 2 * (1 - β) * Real.log d := by
      have h1β : (0:ℝ) ≤ 1 - β := by linarith
      have hx0 : (0:ℝ) ≤ (1 - β) * Real.log d := mul_nonneg h1β hlogd
      have hrpow : ((d:ℝ)) ^ (1 - β) = Real.exp ((1 - β) * Real.log d) := by
        rw [Real.rpow_def_of_pos hd0]
        ring_nf
      have hEM : Real.exp ((1 - β) * Real.log d) - 1
          ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := by
        set x : ℝ := (1 - β) * Real.log d with hx
        have h1 := Real.add_one_le_exp (-x)
        have h2 : (0:ℝ) < Real.exp x := Real.exp_pos _
        have h3 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
        rw [h3] at h1
        have h4 : (-x + 1) * Real.exp x ≤ 1 := by
          calc (-x + 1) * Real.exp x ≤ (Real.exp x)⁻¹ * Real.exp x := by
                apply mul_le_mul_of_nonneg_right h1 h2.le
            _ = 1 := inv_mul_cancel₀ (ne_of_gt h2)
        nlinarith [h4]
      have hd2 : ((d:ℝ)) ^ (1 - β) ≤ 2 := by
        calc ((d:ℝ)) ^ (1 - β) ≤ ((N:ℝ)) ^ (1 - β) := by
              apply Real.rpow_le_rpow hd0.le _ h1β
              exact_mod_cast hd.2
          _ ≤ 2 := hN2
      calc ((d:ℝ)) ^ (1 - β) - 1
          = Real.exp ((1 - β) * Real.log d) - 1 := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * Real.exp ((1 - β) * Real.log d) := hEM
        _ = ((1 - β) * Real.log d) * ((d:ℝ)) ^ (1 - β) := by rw [hrpow]
        _ ≤ ((1 - β) * Real.log d) * 2 := by
            apply mul_le_mul_of_nonneg_left hd2 hx0
        _ = 2 * (1 - β) * Real.log d := by ring
    have hnn : (0:ℝ) ≤ ((d:ℝ)) ^ (1 - β) - 1 := by
      have : (1:ℝ) ≤ ((d:ℝ)) ^ (1 - β) := Real.one_le_rpow hd1r (by linarith)
      linarith
    calc |charFn q χ d| * |((d:ℝ)) ^ (1 - β) - 1| / (d:ℝ)
        ≤ 1 * (2 * (1 - β) * Real.log d) / (d:ℝ) := by
          apply div_le_div_of_nonneg_right _ hd0.le
          apply mul_le_mul (charFn_bound χ hχ2 d) _ (abs_nonneg _) zero_le_one
          rw [abs_of_nonneg hnn]
          exact hexp
      _ = 2 * (1 - β) * (Real.log d / d) := by ring
  -- sum the per-term bounds
  have hsum : ∑ d ∈ Icc 1 N, Real.log d / d ≤ (1 + Real.log N) ^ 2 := by
    calc ∑ d ∈ Icc 1 N, Real.log d / d
        ≤ ∑ d ∈ Icc 1 N, Real.log N * (1 / d) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [Finset.mem_Icc] at hd
          have hd0 : (0:ℝ) < (d:ℝ) := by
            have : (0:ℕ) < d := by omega
            exact_mod_cast this
          have hlog_le : Real.log d ≤ Real.log N := by
            apply Real.log_le_log hd0
            exact_mod_cast hd.2
          rw [mul_one_div]
          apply div_le_div_of_nonneg_right hlog_le hd0.le
      _ = Real.log N * ∑ d ∈ Icc 1 N, (1:ℝ) / d := by rw [Finset.mul_sum]
      _ ≤ Real.log N * (1 + Real.log N) := by
          apply mul_le_mul_of_nonneg_left (sum_one_div_le_log N hN) hlogN
      _ ≤ (1 + Real.log N) ^ 2 := by nlinarith [hlogN]
  calc |∑ d ∈ Icc 1 N, charFn q χ d / d - ∑ d ∈ Icc 1 N, charFn q χ d * ((d:ℝ)) ^ (-β)|
      = |∑ d ∈ Icc 1 N, (charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β))| := by
        rw [Finset.sum_sub_distrib]
    _ ≤ ∑ d ∈ Icc 1 N, |charFn q χ d / d - charFn q χ d * ((d:ℝ)) ^ (-β)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, 2 * (1 - β) * (Real.log d / d) := Finset.sum_le_sum hterm
    _ = 2 * (1 - β) * ∑ d ∈ Icc 1 N, Real.log d / d := by rw [Finset.mul_sum]
    _ ≤ 2 * (1 - β) * (1 + Real.log N) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsum
        nlinarith [hβ2]
