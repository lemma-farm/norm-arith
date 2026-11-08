module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsMoments
import Mathlib.Tactic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive-axis finite-order expansion of the Kummer integral

The polynomially bounded Taylor remainder is integrated against Gamma moments.
The estimates are direct integral estimates, with constants depending on shape and order.
-/
@[expose] public noncomputable section
open Set MeasureTheory Filter
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- A uniform polynomial majorant integrates to the required inverse argument power. -/
theorem laplaceTaylor_remainder_bound (a : Pos) (q : ℝ) (N L : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hrem : ∀ t : ℝ, 0 ≤ t →
      ‖(1 + t) ^ q - powerTaylor q N t‖ ≤ C * t ^ N * (1 + t) ^ L)
    (z : ℝ) (hz : 1 ≤ z) :
    ‖∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) *
      ((1 + t) ^ q - powerTaylor q N t)‖ ≤
      C * 2 ^ L * (Real.Gamma (a.1 + N) + Real.Gamma (a.1 + N + L)) *
        z ^ (-a.1 - (N : ℝ)) := by
  have hz0 := zero_lt_one.trans_le hz
  let s := a.1 + (N : ℝ)
  have hs : 0 < s := add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg N)
  have hsL : 0 < s + (L : ℝ) := add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg L)
  let K := C * (2 : ℝ) ^ L
  have hK : 0 ≤ K := mul_nonneg hC (pow_nonneg (by norm_num) L)
  have hg := ((integrableOn_gammaKernel s z hs hz0).add
    (integrableOn_gammaKernel (s + L) z hsL hz0)).const_mul K
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖Real.exp (-(z * t)) * t ^ (a.1 - 1) *
        ((1 + t) ^ q - powerTaylor q N t)‖ ≤
        K * (Real.exp (-(z * t)) * t ^ (s - 1) +
          Real.exp (-(z * t)) * t ^ (s + (L : ℝ) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hbase : 0 ≤ Real.exp (-(z * t)) * t ^ (a.1 - 1) :=
      (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht _)).le
    rw [norm_mul, Real.norm_of_nonneg hbase]
    have h1 := mul_le_mul_of_nonneg_left (hrem t ht.le) hbase
    have h2 := mul_le_mul_of_nonneg_left
      (one_add_rpow_le_polynomial (L : ℝ) L le_rfl t ht.le)
      (mul_nonneg (mul_nonneg hbase hC) (pow_nonneg ht.le N))
    simp only [Real.rpow_natCast] at h2
    have hpow : t ^ (s - 1) = t ^ (a.1 - 1) * t ^ N := by
      rw [show s - 1 = a.1 - 1 + (N : ℝ) by dsimp only [s]; ring,
        Real.rpow_add ht, Real.rpow_natCast]
    have hpowL : t ^ (s + (L : ℝ) - 1) = t ^ (s - 1) * t ^ L := by
      rw [show s + (L : ℝ) - 1 = s - 1 + (L : ℝ) by ring,
        Real.rpow_add ht, Real.rpow_natCast]
    calc
      Real.exp (-(z * t)) * t ^ (a.1 - 1) * ‖(1 + t) ^ q - powerTaylor q N t‖
          ≤ Real.exp (-(z * t)) * t ^ (a.1 - 1) * (C * t ^ N * (1 + t) ^ L) := h1
      _ = (Real.exp (-(z * t)) * t ^ (a.1 - 1) * C * t ^ N) * (1 + t) ^ L := by ring
      _ ≤ (Real.exp (-(z * t)) * t ^ (a.1 - 1) * C * t ^ N) *
          (2 ^ L * (1 + t ^ L)) := h2
      _ = _ := by rw [hpowL, hpow]; dsimp only [K]; ring
  have h := norm_integral_le_of_norm_le hg hbound
  have hadd := integral_add (integrableOn_gammaKernel s z hs hz0)
    (integrableOn_gammaKernel (s + L) z hsL hz0)
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [hadd, integral_gammaKernel s z hs hz0,
    integral_gammaKernel (s + L) z hsL hz0] at h
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hp : z ^ (-(s + (L : ℝ))) ≤ z ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le hz (by linarith only [hLn])
  have hlast : K * (z ^ (-s) * Real.Gamma s + z ^ (-(s + (L : ℝ))) *
      Real.Gamma (s + L)) ≤ K * (Real.Gamma s + Real.Gamma (s + L)) * z ^ (-s) := by
    calc
      _ ≤ K * (z ^ (-s) * Real.Gamma s + z ^ (-s) * Real.Gamma (s + L)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_right hp (Real.Gamma_pos_of_pos hsL).le))
          hK
      _ = _ := by ring
  have hfinal := h.trans hlast
  simpa only [s, K, neg_add, sub_eq_add_neg] using hfinal
/-- A concrete inverse-power bound for every finite U truncation. -/
theorem UIr_remainder_bound (a : Pos) (b : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z →
      ‖UIr a b z - uExpansion a.1 b N z‖ ≤ C * z ^ (-a.1 - (N : ℝ)) := by
  obtain ⟨C₀, L, hC₀, hrem⟩ := exists_powerTaylor_remainder_bound (b - a.1 - 1) N
  let C := (Real.Gamma a.1)⁻¹ * (C₀ * 2 ^ L *
    (Real.Gamma (a.1 + N) + Real.Gamma (a.1 + N + L)))
  have hs : 0 < a.1 + (N : ℝ) := add_pos_of_pos_of_nonneg a.2 (Nat.cast_nonneg N)
  have hsL : 0 < a.1 + (N : ℝ) + (L : ℝ) :=
    add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg L)
  have hC : 0 < C := mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos a.2))
    (mul_pos (mul_pos hC₀ (pow_pos (by norm_num) L))
      (add_pos (Real.Gamma_pos_of_pos hs) (Real.Gamma_pos_of_pos hsL)))
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hz0 := zero_lt_one.trans_le hz
  have hpol := integrableOn_gammaKernel_powerTaylor a (b - a.1 - 1) z hz0 N
  have hker := integrable_laplaceKernel a b z hz0
  have heq : UIr a b z - uExpansion a.1 b N z = (Real.Gamma a.1)⁻¹ *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(z * t)) * t ^ (a.1 - 1) *
        ((1 + t) ^ (b - a.1 - 1) - powerTaylor (b - a.1 - 1) N t) := by
    have hd := integral_sub hker hpol
    have he : (fun t : ℝ => Real.exp (-(z * t)) * t ^ (a.1 - 1) *
        ((1 + t) ^ (b - a.1 - 1) - powerTaylor (b - a.1 - 1) N t)) =
        (fun t => laplaceKernel a b z t -
          Real.exp (-(z * t)) * t ^ (a.1 - 1) * powerTaylor (b - a.1 - 1) N t) := by
      funext t
      simp only [laplaceKernel, laplaceKernelReal]
      ring
    rw [he, hd, integral_powerTaylor a b z hz0 N]
    change (Real.Gamma a.1)⁻¹ * _ - _ = _
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (Real.Gamma_pos_of_pos a.2).ne', one_mul]
  rw [heq, norm_mul, Real.norm_of_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos a.2)).le]
  have h := laplaceTaylor_remainder_bound a (b - a.1 - 1) N L C₀ hC₀.le hrem z hz
  exact (mul_le_mul_of_nonneg_left h (inv_pos.mpr (Real.Gamma_pos_of_pos a.2)).le).trans_eq
    (by dsimp only [C]; ring)
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
