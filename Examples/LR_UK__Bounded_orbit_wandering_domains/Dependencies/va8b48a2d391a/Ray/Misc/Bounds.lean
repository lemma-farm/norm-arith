module
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Cases
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.MetricSpace.Basic
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Bound
import Examples.LR_UK__Bounded_orbit_wandering_domains.Dependencies.va8b48a2d391a.Ray.Misc.Finset
/-!
## Assorted bound lemmas
-/
open Classical
open Complex (exp log I slitPlane)
open Filter (atTop)
open scoped Real NNReal Topology symmDiff
variable {α : Type}
variable {M : Type} [AddCommMonoid M]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {G : Type} [NormedAddCommGroup G]
public theorem partial_geometric_bound {a : ℝ} (N : Finset ℕ) (a0 : 0 ≤ a) (a1 : a < 1) :
    N.sum (fun n ↦ a^n) ≤ (1 - a)⁻¹ :=
  haveI pos : ∀ n, n ∉ N → 0 ≤ a^n := by intro n _; bound
  sum_le_hasSum N pos (hasSum_geometric_of_lt_one a0 a1)
theorem mem_slitPlane_of_near_one' {z : ℂ} (z1 : ‖z - 1‖ ≤ 1) (z0 : z ≠ 0) : z ∈ slitPlane := by
  rw [← sq_le_sq₀ (by bound) (by norm_num)] at z1
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re, ← pow_two,
    Complex.sub_im, Complex.one_im, sub_zero, one_pow] at z1
  by_cases i0 : z.im ≠ 0
  · right
    exact i0
  · simp only [ne_eq, Decidable.not_not] at i0
    left
    contrapose z0
    simp [i0, abs_sub_le_iff, Complex.ext_iff] at z0 z1 ⊢
    grind
public theorem mem_slitPlane_of_near_one {z : ℂ} (z1 : ‖z - 1‖ < 1) : z ∈ slitPlane := by
  by_cases z0 : z = 0
  · simp [z0] at z1
  · exact mem_slitPlane_of_near_one' z1.le z0
theorem derivWithin.cid {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s) :
    derivWithin (fun z ↦ z) s z = 1 :=
  derivWithin_id z s (IsOpen.uniqueDiffWithinAt o zs)
theorem derivWithin.clog {f : ℂ → ℂ} {z : ℂ} {s : Set ℂ} (o : IsOpen s) (zs : z ∈ s)
    (hf : DifferentiableWithinAt ℂ f s z) (hx : (f z).re > 0 ∨ (f z).im ≠ 0) :
    derivWithin (fun z ↦ Complex.log (f z)) s z = derivWithin f s z / f z := by
  have hz := DifferentiableWithinAt.hasDerivWithinAt hf
  have h := HasDerivWithinAt.clog hz hx
  have u := o.uniqueDiffWithinAt (𝕜 := ℂ) zs
  rw [HasDerivWithinAt.derivWithin h u]
theorem weak_log1p_small {z : ℂ} {r : ℝ} (r1 : r < 1) (h : ‖z‖ < r) :
    ‖log (1 + z)‖ ≤ 1/(1 - r) * ‖z‖ := by
  by_cases rp : r ≤ 0
  · have a0 : ‖z‖ < 0 := lt_of_lt_of_le h rp
    have a0' : ‖z‖ ≥ 0 := by bound
    exfalso
    linarith [a0, a0']
  · simp only [not_le] at rp
    have L : ‖log (1 + z) - log 1‖ ≤ 1/(1 - r) * ‖1 + z - 1‖ := by
      generalize hs : Metric.ball (1:ℂ) r = s
      have o : IsOpen s := by rw [← hs]; exact Metric.isOpen_ball
      have s1z : 1 + z ∈ s := by simp [← hs]; assumption
      have s1 : (1:ℂ) ∈ s := by simp [← hs]; assumption
      have sp : ∀ w : ℂ, w ∈ s → w.re > 0 ∨ w.im ≠ 0 := by
        intro w ws
        apply mem_slitPlane_of_near_one
        simp only [Metric.mem_ball, Complex.dist_eq, ← hs] at ws
        calc ‖w - 1‖ < r := by assumption
          _ < 1 := r1
      have sa : ∀ w : ℂ, w ∈ s → ‖w‖ ≥ 1 - r := by
        intro w ws
        simp only [Metric.mem_ball, Complex.dist_eq, ← hs] at ws
        calc ‖w‖ = ‖1 + (w - 1)‖ := by ring_nf
          _ ≥ ‖(1 : ℂ)‖ - ‖w - 1‖ := by bound
          _ ≥ ‖(1 : ℂ)‖ - r := by bound
          _ = 1 - r := by rw [norm_one]
      refine Convex.norm_image_sub_le_of_norm_derivWithin_le ?_ ?_ ?_ s1 s1z
      · exact DifferentiableOn.clog differentiableOn_id sp
      · intro w ws
        rw [derivWithin.clog o ws, derivWithin.cid o ws]
        simp only [one_div, norm_inv]
        rw [inv_le_comm₀]
        have aw := sa w ws; simp at aw; field_simp; linarith
        have aw := sa w ws; linarith; norm_num; assumption
        exact differentiableWithinAt_id
        exact sp w ws
      · rw [← hs]; exact convex_ball _ _
    simp only [Complex.log_one, sub_zero, one_div, add_sub_cancel_left] at L
    simpa only [one_div, ge_iff_le]
public theorem le_of_forall_small_le_add {a b t : ℝ} (tp : 0 < t)
    (h : ∀ e, 0 < e → e < t → a ≤ b + e) : a ≤ b := by
  apply le_of_forall_pos_lt_add
  intro e ep
  by_cases et : e ≥ t
  · specialize h (t/2) (by bound) (by bound)
    calc a ≤ b + t/2 := h
      _ ≤ b + e/2 := by bound
      _ < b + e := by bound
  · simp only [ge_iff_le, not_le] at et
    calc a ≤ b + e/2 := h (e/2) (by bound) (by linarith)
      _ < b + e := by bound
theorem Metric.continuous_near {f : ℂ → ℂ} {z : ℂ} {r : ℝ} (fc : ContinuousAt f z) (rp : 0 < r)
    : ∀ e, 0 < e → ∃ s, 0 < s ∧ s ≤ r ∧ ∀ {w} , ‖w - z‖ < s → ‖f w - f z‖ < e := by
  intro e ep
  rcases Metric.continuousAt_iff.mp fc e ep with ⟨s,sp,sc⟩
  simp_rw [ Complex.dist_eq ] at sc
  by_cases sr : s ≤ r; exists s
  simp only [not_le] at sr
  exists r
  refine ⟨rp, by bound, ?_⟩
  intro w wr
  refine @sc w ?_
  trans r; assumption; assumption
theorem slightly_smaller {z : ℂ} (nz : z ≠ 0) {r : ℝ} (rp : 0 < r) :
    ∃ w, ‖w - z‖ < r ∧ ‖w‖ < ‖z‖ := by
  by_cases rz : ‖z‖ < r
  · use 0
    simp only [zero_sub, norm_neg, rz, norm_zero, norm_pos_iff, ne_eq, nz, not_false_eq_true,
      and_self]
  simp only [not_lt] at rz
  have azp : 0 < ‖z‖ := norm_pos_iff.mpr nz
  generalize ha : 1 - r/2/‖z‖ = a
  have a0 : 0 ≤ a := by rw [←ha, sub_nonneg, div_le_one azp]; exact _root_.trans (by bound) rz
  have a1 : a < 1 := by rw [←ha, sub_lt_self_iff]; positivity
  generalize hw : ↑a * z = w
  use w; constructor
  · rw [ ←hw, ← ha]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_div]
    rw [mul_sub_right_distrib]
    simp only [one_mul, Complex.ofReal_ofNat, sub_sub_cancel_left, norm_neg, Complex.norm_mul,
      Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos rp, Complex.norm_ofNat,
      div_mul (r / 2), div_one, half_lt_self_iff, div_self azp.ne', abs_norm, rp]
  · simp only [← hw, Complex.norm_mul, Complex.norm_real, Real.norm_of_nonneg a0]
    exact mul_lt_of_lt_one_left azp a1
theorem weak_to_strong_small {f : ℂ → ℂ} {z : ℂ} {r c : ℝ} (rp : 0 < r) (cp : 0 < c)
    (zr : ‖z‖ ≤ r) (fc : ContinuousAt f z) (h : ∀ z : ℂ, ‖z‖ < r → ‖f z‖ ≤ c * ‖z‖) :
    ‖f z‖ ≤ c * ‖z‖ := by
  by_cases nz : z = 0; · refine h z ?_; rw [nz]; simpa
  apply le_of_forall_small_le_add zero_lt_one
  intro e ep _
  rcases Metric.continuous_near fc rp e ep with ⟨s,sp,_,sc⟩
  rcases slightly_smaller nz sp with ⟨w,wz,awz⟩
  have wr : ‖w‖ < r := lt_of_lt_of_le awz zr
  calc ‖f z‖ = ‖f w - (f w - f z)‖ := by ring_nf
    _ ≤ ‖f w‖ + ‖f w - f z‖ := by bound
    _ ≤ c * ‖w‖ + e := by bound [h w wr, sc wz]
    _ ≤ c * ‖z‖ + e := by bound
theorem log1p_small' {z : ℂ} {r : ℝ} (r1 : r < 1) (zr : ‖z‖ ≤ r) :
    ‖log (1 + z)‖ ≤ 1 / (1 - r) * ‖z‖ := by
  by_cases r0 : r ≤ 0
  · have z0 := le_antisymm (le_trans zr r0) (norm_nonneg z)
    simp only [norm_eq_zero] at z0
    simp only [z0, add_zero, Complex.log_one, norm_zero, one_div, mul_zero, le_refl]
  simp only [not_le] at r0
  have fc : ContinuousAt (fun z ↦ log (1 + z)) z := by
    apply ContinuousAt.clog; apply ContinuousAt.add; exact continuousAt_const; exact continuousAt_id
    refine mem_slitPlane_of_near_one ?_
    simp only [add_sub_cancel_left, lt_of_le_of_lt zr r1]
  apply weak_to_strong_small r0 (by bound) zr fc
  intro w wr
  exact @weak_log1p_small w r (by bound) wr
theorem log1p_small {z : ℂ} (zs : ‖z‖ ≤ 1/2) : ‖log (1 + z)‖ ≤ 2 * ‖z‖ :=
  le_trans (log1p_small' (by norm_num) zs) (le_of_eq (by norm_num))
/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small' {x r : ℝ} (r1 : r < 1) (xr : |x| ≤ r) :
    |Real.log (1 + x)| ≤ 1 / (1-r) * |x| := by
  set z := (x : ℂ)
  have zx : ‖z‖ = |x| := by simp only [Complex.norm_real, norm_eq_abs, z]
  simp only [← Complex.log_ofReal_re, ← zx] at xr ⊢
  refine _root_.trans (_root_.trans (Complex.abs_re_le_norm _) ?_) (_root_.log1p_small' r1 xr)
  simp only [Complex.ofReal_add, Complex.ofReal_one, le_refl, z]
/-- `log (1+x)` is small for small `x` -/
theorem Real.log1p_small {x : ℝ} (xr : |x| ≤ 1/2) : |Real.log (1 + x)| ≤ 2 * |x| :=
  le_trans (Real.log1p_small' (by norm_num) xr) (le_of_eq (by norm_num))
/-- `log z` is small for `z ≈ 1` -/
public theorem log_small {z : ℂ} (zs : ‖z - 1‖ ≤ 1 / 2) : ‖log z‖ ≤ 2 * ‖z - 1‖ := by
  generalize zw : z - 1 = z1; have wz : z = 1 + z1 := by rw [← zw]; ring
  rw [wz]; refine log1p_small ?_; rwa [← zw]
theorem weak_exp_small' {z : ℂ} {r : ℝ} (zr : ‖z‖ < r) (r1 : r ≤ 1) :
    ‖exp z - 1‖ ≤ (1 + r) * ‖z‖ := by
  have r0 : 0 ≤ r := le_trans (norm_nonneg _) zr.le
  have L := Complex.locally_lipschitz_exp r0 r1 0 z (by simpa only [sub_zero])
  simpa only [Complex.exp_zero, norm_one, mul_one, sub_zero] using L
theorem exp_small' {z : ℂ} {r : ℝ} (zs : ‖z‖ ≤ r) (r1 : r ≤ 1) : ‖exp z - 1‖ ≤ (1 + r) * ‖z‖ := by
  by_cases z0 : z = 0
  · simp [z0]
  have r0 : 0 < r := lt_of_lt_of_le (norm_pos_iff.mpr z0) zs
  have cp : 0 < 1 + r := by linarith
  have fc : ContinuousAt (fun z ↦ exp z - 1) z := by
    apply ContinuousAt.sub; apply ContinuousAt.cexp
    exact continuousAt_id; exact continuousAt_const
  apply weak_to_strong_small r0 cp zs fc
  intro w wr
  exact weak_exp_small' wr r1
/-- `exp z ≈ 1` for `z ≈ 0` -/
theorem exp_small {z : ℂ} (zs : ‖z‖ ≤ 1) : ‖exp z - 1‖ ≤ 2 * ‖z‖ := by
  have s := exp_small' zs (by norm_num)
  norm_num at s
  exact s
public theorem dist_prod_one_le_abs_sum {f : ℕ → ℂ} {s : Finset ℕ} {c : ℝ}
    (le : s.sum (fun n ↦ ‖f n - 1‖) ≤ c) (c1 : c ≤ 1/2) : ‖s.prod f - 1‖ ≤ 4 * c := by
  set g := fun n ↦ Complex.log (f n)
  have b : ∀ n, n ∈ s → ‖f n - 1‖ ≤ c := by
    intro n m; refine _root_.trans ?_ le
    exact Finset.single_le_sum (f := fun n ↦ ‖f n - 1‖) (fun _ _ ↦ norm_nonneg _) m
  have f0 : ∀ n, n ∈ s → f n ≠ 0 := by
    intro n m; specialize b n m; contrapose b
    simp only [b, not_le]; norm_num; linarith
  have sg : ‖s.sum g‖ ≤ 2 * c := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum (fun n m ↦ log_small (le_trans (b n m) c1))) ?_
    rw [← Finset.mul_sum]; bound
  have e : s.prod f = Complex.exp (s.sum g) := by
    rw [Complex.exp_sum]; apply Finset.prod_congr rfl
    intro n m; rw [Complex.exp_log (f0 n m)]
  rw [e]; exact _root_.trans (exp_small (by linarith)) (by linarith)
