module
public import Examples.AxiomMath__DedekindZetaZeroFree.Dependencies.v384645a008e3.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Ring.Ultra
set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace DedekindZetaZeroFree.KPFiniteLocal
theorem distinct_root_recurrence_formula (u : ℕ → ℂ) (α β : ℂ)
    (hne : α ≠ β)
    (hrec : ∀ n : ℕ, u (n + 2) - (α + β) * u (n + 1) + α * β * u n = 0)
    (n : ℕ) :
    u n = ((u 1 - β * u 0) / (α - β)) * α ^ n +
      ((α * u 0 - u 1) / (α - β)) * β ^ n := by
  have hnz : α - β ≠ 0 := sub_ne_zero.mpr hne
  induction n using Nat.twoStepInduction with
  | zero =>
    simp only [pow_zero, mul_one]
    field_simp
    ring
  | one =>
    simp only [pow_one]
    field_simp
    ring
  | more n ih0 ih1 =>
    have hh := hrec n
    rw [ih0, ih1] at hh
    rw [pow_succ, pow_succ, pow_succ, pow_succ]
    linear_combination hh
theorem distinct_root_recurrence_uniform_bound (u : ℕ → ℂ) (α β : ℂ)
    (hne : α ≠ β) (hnorm : ‖β‖ ≤ ‖α‖)
    (hrec : ∀ n : ℕ, u (n + 2) - (α + β) * u (n + 1) + α * β * u n = 0)
    (H : ℝ) (hH : 0 ≤ H) (h0 : ‖u 0‖ ≤ H) (h1 : ‖u 1‖ ≤ H)
    (n : ℕ) :
    ‖u n‖ ≤ ((2 + ‖α‖ + ‖β‖) * H / ‖α - β‖) * ‖α‖ ^ n := by
  have hd : 0 < ‖α - β‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hA : ‖(u 1 - β * u 0) / (α - β)‖ ≤ (H + ‖β‖ * H) / ‖α - β‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ ‖u 1‖ + ‖β * u 0‖ := norm_sub_le _ _
      _ = ‖u 1‖ + ‖β‖ * ‖u 0‖ := by rw [norm_mul]
      _ ≤ _ := by gcongr
  have hB : ‖(α * u 0 - u 1) / (α - β)‖ ≤ (‖α‖ * H + H) / ‖α - β‖ := by
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ ≤ ‖α * u 0‖ + ‖u 1‖ := norm_sub_le _ _
      _ = ‖α‖ * ‖u 0‖ + ‖u 1‖ := by rw [norm_mul]
      _ ≤ _ := by gcongr
  rw [distinct_root_recurrence_formula u α β hne hrec n]
  calc
    _ ≤ ‖((u 1 - β * u 0) / (α - β)) * α ^ n‖ +
        ‖((α * u 0 - u 1) / (α - β)) * β ^ n‖ := norm_add_le _ _
    _ = ‖(u 1 - β * u 0) / (α - β)‖ * ‖α‖ ^ n +
        ‖(α * u 0 - u 1) / (α - β)‖ * ‖β‖ ^ n := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow]
    _ ≤ ((H + ‖β‖ * H) / ‖α - β‖) * ‖α‖ ^ n +
        ((‖α‖ * H + H) / ‖α - β‖) * ‖α‖ ^ n := by
      gcongr
    _ = _ := by ring
private theorem recurrence_decay {K : Type*} [NormedField K] (f : Kˣ → ℂ)
    (p : Kˣ) (α β : ℂ) (hp : ‖(p : K)‖ < 1)
    (hne : α ≠ β) (hnorm : ‖β‖ ≤ ‖α‖)
    (δ : ℝ) (hd : 0 < δ) (hα : ‖α‖ ≤ Real.rpow ‖(p : K)‖ δ)
    (r : ℝ) (hr : 0 < r)
    (hrec : ∀ y : Kˣ, ‖(y : K)‖ < r →
      f (y * p * p) - (α + β) * f (y * p) + α * β * f y = 0)
    (H : ℝ) (hH : 0 < H)
    (hbound : ∀ y : Kˣ, min (r / 2) 1 * ‖(p : K)‖ ^ 2 ≤ ‖(y : K)‖ →
      ‖(y : K)‖ ≤ 1 → ‖f y‖ ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : Kˣ, ‖(y : K)‖ ≤ 1 →
      ‖f y‖ ≤ C * Real.rpow ‖(y : K)‖ δ := by
  let q := ‖(p : K)‖
  have hq : 0 < q := norm_pos_iff.mpr p.ne_zero
  let s := min (r / 2) 1
  have hs : 0 < s := lt_min (by positivity) zero_lt_one
  have hs1 : s ≤ 1 := min_le_right _ _
  have hsr : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let D := (2 + ‖α‖ + ‖β‖) * H / ‖α - β‖
  have hden : 0 < ‖α - β‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hD : 0 < D := by dsimp [D]; positivity
  let L := Real.rpow (s * q) δ
  have hL : 0 < L := Real.rpow_pos_of_pos (mul_pos hs hq) _
  refine ⟨max H D / L, div_pos (lt_of_lt_of_le hH (le_max_left _ _)) hL, ?_⟩
  intro y hy
  have hyn : 0 < ‖(y : K)‖ := norm_pos_iff.mpr y.ne_zero
  have hql : q ≤ 1 := hp.le
  by_cases hys : ‖(y : K)‖ ≤ s
  · obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
      (div_pos hyn hs) ((div_le_one hs).mpr hys) hq hp
    let z := y / p ^ n
    have hz : ‖(z : K)‖ = ‖(y : K)‖ / q ^ n := by simp [z, q, norm_div, norm_pow]
    have hzlo : s * q < ‖(z : K)‖ := by
      rw [hz, lt_div_iff₀ (pow_pos hq n)]
      have hh := (lt_div_iff₀ hs).mp hnlo
      rw [pow_succ] at hh
      nlinarith
    have hzhi : ‖(z : K)‖ ≤ s := by
      rw [hz, div_le_iff₀ (pow_pos hq n)]
      have hh := (div_le_iff₀ hs).mp hnhi
      nlinarith
    have hzp : ‖((z * p : Kˣ) : K)‖ = ‖(z : K)‖ * q := by simp [q, norm_mul]
    have h0 : ‖f z‖ ≤ H := hbound z (by
      change s * q ^ 2 ≤ _
      have : q ^ 2 ≤ q := by nlinarith
      nlinarith) (hzhi.trans hs1)
    have h1 : ‖f (z * p)‖ ≤ H := hbound (z * p) (by
      rw [hzp]
      change s * q ^ 2 ≤ _
      nlinarith) (by rw [hzp]; nlinarith)
    have hrec' : ∀ k : ℕ,
        f (z * p ^ (k + 2)) - (α + β) * f (z * p ^ (k + 1)) +
          α * β * f (z * p ^ k) = 0 := by
      intro k
      have hzk : ‖((z * p ^ k : Kˣ) : K)‖ < r := by
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
        have hk : q ^ k ≤ 1 := pow_le_one₀ hq.le hp.le
        have : ‖(z : K)‖ * q ^ k ≤ s := by nlinarith [norm_nonneg (z : K)]
        exact this.trans_lt hsr
      simpa only [pow_succ, mul_assoc] using hrec (z * p ^ k) hzk
    have hb := distinct_root_recurrence_uniform_bound (fun k => f (z * p ^ k))
      α β hne hnorm hrec' H hH.le (by simpa using h0) (by simpa using h1) n
    have hzy : z * p ^ n = y := div_mul_cancel _ _
    rw [hzy] at hb
    have hpow : ‖α‖ ^ n ≤ (Real.rpow q δ) ^ n := pow_le_pow_left₀ (norm_nonneg α) hα n
    have hscale : L * (Real.rpow q δ) ^ n ≤ Real.rpow ‖(y : K)‖ δ := by
      have hh : s * q * q ^ n ≤ ‖(y : K)‖ := by
        have := (lt_div_iff₀ hs).mp hnlo
        rw [pow_succ] at this
        nlinarith
      have hh' := Real.rpow_le_rpow (by positivity : 0 ≤ s * q * q ^ n) hh hd.le
      have hpr : (q ^ n) ^ δ = (q ^ δ) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, mul_comm, Real.rpow_mul hq.le,
          Real.rpow_natCast]
      rw [Real.mul_rpow (by positivity) (by positivity), hpr] at hh'
      exact hh'
    have hC : D * (Real.rpow q δ) ^ n ≤ max H D / L * Real.rpow ‖(y : K)‖ δ := by
      have he : max H D / L * Real.rpow ‖(y : K)‖ δ =
          (max H D * Real.rpow ‖(y : K)‖ δ) / L := by ring
      rw [he]
      apply (le_div_iff₀ hL).mpr
      calc
        D * (Real.rpow q δ) ^ n * L = D * (L * (Real.rpow q δ) ^ n) := by ring
        _ ≤ max H D * Real.rpow ‖(y : K)‖ δ :=
          mul_le_mul (le_max_right H D) hscale (mul_nonneg hL.le (pow_nonneg (Real.rpow_pos_of_pos hq δ).le n)) (le_trans hD.le (le_max_right H D))
        _ = (max H D * Real.rpow ‖(y : K)‖ δ) := rfl
    exact hb.trans ((mul_le_mul_of_nonneg_left hpow hD.le).trans hC)
  · have hsy : s ≤ ‖(y : K)‖ := (not_le.mp hys).le
    have hb := hbound y (by
      change s * q ^ 2 ≤ _
      have : q ^ 2 ≤ 1 := pow_le_one₀ hq.le hp.le
      nlinarith) hy
    have hLy : L ≤ Real.rpow ‖(y : K)‖ δ := by
      apply Real.rpow_le_rpow (by positivity) _ hd.le
      nlinarith
    calc
      ‖f y‖ ≤ H := hb
      _ ≤ max H D := le_max_left _ _
      _ = max H D / L * L := (div_mul_cancel₀ _ hL.ne').symm
      _ ≤ max H D / L * Real.rpow ‖(y : K)‖ δ := by gcongr
end DedekindZetaZeroFree.KPFiniteLocal
end
