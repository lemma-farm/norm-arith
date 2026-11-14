module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Analytic.Binomial

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v80cc261cd169.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The confluent hypergeometric power series

Literal real and complex series for Kummer M, with positive denominator parameter.
-/
@[expose] public noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- Positive real parameters. -/
abbrev Pos := {x : ℝ // 0 < x}
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.v80cc261cd169.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsTaylor ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Polynomially bounded Taylor remainder for a translated power

Analyticity controls the remainder at zero. A polynomial growth bound then extends it
to the entire nonnegative half-line, as required for domination of Laplace remainders.
-/
@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- Literal Taylor polynomial of the translated power, truncated before order N. -/
def powerTaylor (q : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, Ring.choose q n * t ^ n
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_b57828a87a3d9fdb5e34_UAsymptotics ====
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
set_option linter.unusedVariables false in
/-- A uniform polynomial majorant integrates to the required inverse argument power. -/
theorem laplaceTaylor_remainder_bound (a : Pos) (q : ℝ) (N L : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hrem : ∀ t : ℝ, 0 ≤ t →
      ‖(1 + t) ^ q - powerTaylor q N t‖ ≤ C * t ^ N * (1 + t) ^ L)
    (z : ℝ) (hz : 1 ≤ z) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel : ∀ (a z : ℝ),
      0 < a →
        0 < z →
          MeasureTheory.IntegrableOn (fun (t : ℝ) ↦ Real.exp (-(z * t)) * t ^ (a - 1)) (Set.Ioi 0)
            MeasureTheory.MeasureSpace.volume)
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_one_add_rpow_le_polynomial : ∀ (q : ℝ) (n : ℕ), q ≤ (↑n : ℝ) → ∀ (t : ℝ), 0 ≤ t → (1 + t) ^ q ≤ 2 ^ n * (1 + t ^ n))
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integral_gammaKernel : ∀ (a z : ℝ),
      0 < a →
        0 < z → ∫ (t : ℝ) in Set.Ioi 0, Real.exp (-(z * t)) * t ^ (a - 1) = z ^ (-a) * Real.Gamma a)
    :
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
  have hg := ((h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel s z hs hz0).add
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel (s + L) z hsL hz0)).const_mul K
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
      (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_one_add_rpow_le_polynomial (L : ℝ) L le_rfl t ht.le)
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
  have hadd := integral_add (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel s z hs hz0)
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel (s + L) z hsL hz0)
  rw [integral_const_mul] at h
  simp only [Pi.add_apply] at h
  rw [hadd, h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integral_gammaKernel s z hs hz0,
    h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integral_gammaKernel (s + L) z hsL hz0] at h
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
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
