module
public import Examples.linrock__math_proofs.Dependencies.v2b4777b3fc63.GoldbachSW1
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
