module
/-
The scalar functions of `arbitrary_offspring_matching.tex` (`eq:mean-constants`,
`eq:four-law-constants`) and the pointwise inequalities of the four-law
contraction (`eq:four-law-product` to `eq:four-law-weight`):

* `Lfun α β = max_{0 ≤ q ≤ 1} (q/(1+q)^α + β (1-q)^α)`, as a supremum;
* `Kfun α β = α^α/(α+1)^{α+1} (1-β)^{α+1}`, the maximum of `(q-β)(1-q)^α` on `[0,1]`;
* `lambda α = 2 min_{0 ≤ β ≤ 1} (Lfun α β + Kfun α β)`, the exponent condition `lambda α < 1`;
* `Cfun α L0 u = 4 L0 ((1-u)^{-α} - 1)/u + 4/u + 8α + 2α²`, the quadratic coefficient;
* `phi_sq_le`, `phi_mul_le_beta`: `φ(q²) ≤ L φ(q) - β q` and the product bound
  `φ(xy) ≤ (L/2)(φ(x) + φ(y)) - (β/2)(x + y)`;
* `sq_le_K_phi_add`: `q² ≤ K φ(q) + β q`;
* `chord_gen`: the chord `(1-s)^{-α} ≤ 1 + c s` on `[0,u]`, `c = ((1-u)^{-α} - 1)/u`;
* `rpow_one_sub_le`: `s^{1-α} ≤ 1 + (α-1)(1-s)/s^α` on `(0,1]`;
* the explicit values of `Lfun α 0` and the closed form of `Kfun` as a maximum;
* `exists_beta_of_lambda_lt_one`, `exists_beta_min`: a minimising `β` exists, and the
  exponent condition supplies a `β` with `2 (L + K) < 1`;
* `amgm_pow`: weighted AM–GM in the power form `y x^γ ≤ ((y + γx)/(γ+1))^{γ+1}`, behind
  both the maximum `K_α(β)` and the value of `L_α` for `α ≥ 2`.

The parameters `L`, `K`, `L0` enter the four-law contraction as hypotheses (the bounds
`le_Lfun`, `Kfun_bound`, `le_Lfun` at `β = 0`), so that rational surrogates can replace
the exact maxima in numerical instances.
-/
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Support.Phi
public import Examples.sascha2718__qi_trees_and_matching_lean.Dependencies.v7c687ed7ca22.GraphMarkovMatching.Potential.Directed
@[expose] public section
namespace GraphMarkovMatching.Stopped
open GraphMarkovMatching.Support Real
/-! ### The scalar functions -/
noncomputable def chordSlope (α u : ℝ) : ℝ := ((1 - u) ^ (-α) - 1) / u
/-! ### Weighted AM–GM in power form

`y x^γ ≤ ((y + γ x)/(γ+1))^{γ+1}` for `x, y ≥ 0` and `γ ≥ 0`: the two-point weighted
AM–GM inequality with weights `1/(γ+1)`, `γ/(γ+1)`, raised to the power `γ + 1`. It
supplies the maximum of `(q-β)(1-q)^α` (`Kfun_bound`) and the value of `L_α` for
`α ≥ 2` (`Lfun_zero_eq_of_two_le`). -/
lemma chordSlope_nonneg {α u : ℝ} (hα : 0 ≤ α) (hu0 : 0 < u) (hu1 : u < 1) :
    0 ≤ chordSlope α u := by
  unfold chordSlope
  have h : (1 : ℝ) ≤ (1 - u) ^ (-α) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith) (by linarith) (by linarith)
  exact div_nonneg (by linarith) hu0.le
/-- **The chord bound** on `[0,u]`: `(1-s)^{-α} ≤ 1 + c s` with `c = ((1-u)^{-α} - 1)/u`,
by concavity of the logarithm. -/
lemma chord_gen {α u s : ℝ} (hα : 0 ≤ α) (hu0 : 0 < u) (hu1 : u < 1) (hs0 : 0 ≤ s)
    (hsu : s ≤ u) : (1 - s) ^ (-α) ≤ 1 + chordSlope α u * s := by
  have hs1 : (0 : ℝ) < 1 - s := by linarith
  have hP : 0 < (1 - s) ^ α := rpow_denom_pos α (by linarith)
  have hcs : (0 : ℝ) < 1 + chordSlope α u * s := by
    have := mul_nonneg (chordSlope_nonneg hα hu0 hu1) hs0
    linarith
  rw [Real.rpow_neg hs1.le, inv_eq_one_div, div_le_iff₀ hP]
  -- concavity of log with weights `(1 - s/u, s/u)`
  have hconc : ConcaveOn ℝ (Set.Ioi (0 : ℝ)) Real.log :=
    strictConcaveOn_log_Ioi.concaveOn
  have ha : (0 : ℝ) ≤ 1 - s / u := by
    rw [sub_nonneg, div_le_one hu0]; exact hsu
  have hb : (0 : ℝ) ≤ s / u := div_nonneg hs0 hu0.le
  have hab : (1 - s / u) + s / u = 1 := by ring
  have hx1 : (1 : ℝ) ∈ Set.Ioi (0 : ℝ) := by norm_num
  have hu' : (0 : ℝ) < 1 - u := by linarith
  -- first application: points `1` and `(1-u)^{-α}`, giving `log (1 + c s)`
  have hy1 : (1 - u) ^ (-α) ∈ Set.Ioi (0 : ℝ) := Real.rpow_pos_of_pos hu' _
  have hlog1 : (1 - s / u) * Real.log 1 + (s / u) * Real.log ((1 - u) ^ (-α))
      ≤ Real.log ((1 - s / u) * 1 + (s / u) * (1 - u) ^ (-α)) := by
    have := hconc.2 hx1 hy1 ha hb hab
    simpa [smul_eq_mul] using this
  have he1 : (1 - s / u) * 1 + (s / u) * (1 - u) ^ (-α) = 1 + chordSlope α u * s := by
    unfold chordSlope
    field_simp
    ring
  have hl1 : (s / u) * (-α * Real.log (1 - u)) ≤ Real.log (1 + chordSlope α u * s) := by
    rw [he1, Real.log_one, Real.log_rpow hu'] at hlog1
    linarith [hlog1]
  -- second application: points `1` and `1 - u`, giving `log (1 - s)`
  have hy2 : (1 - u) ∈ Set.Ioi (0 : ℝ) := hu'
  have hlog2 : (1 - s / u) * Real.log 1 + (s / u) * Real.log (1 - u)
      ≤ Real.log ((1 - s / u) * 1 + (s / u) * (1 - u)) := by
    have := hconc.2 hx1 hy2 ha hb hab
    simpa [smul_eq_mul] using this
  have he2 : (1 - s / u) * 1 + (s / u) * (1 - u) = 1 - s := by
    field_simp
    ring
  have hl2 : (s / u) * Real.log (1 - u) ≤ Real.log (1 - s) := by
    rw [he2, Real.log_one] at hlog2
    linarith [hlog2]
  have hl2' : α * ((s / u) * Real.log (1 - u)) ≤ α * Real.log (1 - s) :=
    mul_le_mul_of_nonneg_left hl2 hα
  have hsum : 0 ≤ Real.log (1 + chordSlope α u * s) + α * Real.log (1 - s) := by
    nlinarith [hl1, hl2']
  have hprod : (1 + chordSlope α u * s) * (1 - s) ^ α
      = Real.exp (Real.log (1 + chordSlope α u * s) + α * Real.log (1 - s)) := by
    rw [Real.exp_add, Real.exp_log hcs, Real.rpow_def_of_pos hs1, mul_comm α]
  rw [hprod]
  calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (Real.log (1 + chordSlope α u * s) + α * Real.log (1 - s)) :=
        Real.exp_le_exp.mpr hsum
end GraphMarkovMatching.Stopped
