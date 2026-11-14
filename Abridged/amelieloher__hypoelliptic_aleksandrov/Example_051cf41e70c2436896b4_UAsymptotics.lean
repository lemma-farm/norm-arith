module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Tactic
public import Mathlib.Analysis.Analytic.Binomial

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Series ====
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

/-- The rising factorial. -/
def poch (a : ℝ) (n : ℕ) : ℝ := (ascPochhammer ℝ n).eval a

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.IntegralKernel ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive Laplace kernels for the Kummer integral

This module develops the kernel on real parameters, independently of the series module.
Only positive integration variables and positive Laplace parameters are characterized.
-/
@[expose] public section
open Set MeasureTheory Real
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- Literal real Laplace kernel, before bundling the positive first parameter. -/
noncomputable def laplaceKernelReal (a b z t : ℝ) : ℝ :=
  Real.exp (-(z * t)) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Integral ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive integral definitions of Kummer U

`UI` has positive shape and argument. `UN` is the source transformation for the
negative shape interval. The real auxiliary formulae are only characterized at positive
arguments; their values outside that domain are never used as special-function values.
-/
@[expose] public noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- The Laplace kernel with positive first parameter. -/
def laplaceKernel (a : Pos) (b z t : ℝ) : ℝ := laplaceKernelReal a.1 b z t
def UIr (a : Pos) (b z : ℝ) : ℝ :=
  (Real.Gamma a.1)⁻¹ * ∫ t in Ioi (0 : ℝ), laplaceKernel a b z t

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsTaylor ====
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

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf33f9f71f919.HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.UAsymptoticsMoments ====
public section
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Gamma moments of the positive-axis expansion

This module evaluates the integral Taylor polynomial with the exact rising-factorial
coefficients of the source expansion.
-/
@[expose] public noncomputable section
open Set MeasureTheory
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
/-- Finite positive-axis U expansion in inverse powers of the argument. -/
def uExpansion (a b : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  z ^ (-a) * ∑ n ∈ Finset.range N,
    (-1 : ℝ) ^ n * poch a n * poch (a - b + 1) n /
      (n.factorial : ℝ) * z⁻¹ ^ n

end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer

end
end

-- ==== Examples.amelieloher__hypoelliptic_aleksandrov.Examples.Example_051cf41e70c2436896b4_UAsymptotics ====
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
/-- A concrete inverse-power bound for every finite U truncation. -/
theorem UIr_remainder_bound (a : Pos) (b : ℝ) (N : ℕ) 
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_laplaceTaylor_remainder_bound : ∀ (a : HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Pos) (q : ℝ) (N L : ℕ)
      (C : ℝ),
      0 ≤ C →
        (∀ (t : ℝ),
            0 ≤ t →
              ‖(1 + t) ^ q -
                    HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.powerTaylor q N
                      t‖ ≤
                C * t ^ N * (1 + t) ^ L) →
          ∀ (z : ℝ),
            1 ≤ z →
              ‖∫ (t : ℝ) in Set.Ioi 0,
                    Real.exp (-(z * t)) * t ^ ((↑a : ℝ) - 1) *
                      ((1 + t) ^ q -
                        HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.powerTaylor q N
                          t)‖ ≤
                C * 2 ^ L *
                    (Real.Gamma ((↑a : ℝ) + (↑N : ℝ)) + Real.Gamma ((↑a : ℝ) + (↑N : ℝ) + (↑L : ℝ))) *
                  z ^ (-(↑a : ℝ) - (↑N : ℝ)))
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrable_laplaceKernel : ∀ (a : HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Pos) (b z : ℝ),
      0 < z →
        MeasureTheory.IntegrableOn
          (HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.laplaceKernel a b z)
          (Set.Ioi 0) MeasureTheory.MeasureSpace.volume)
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_exists_powerTaylor_remainder_bound : ∀ (q : ℝ) (N : ℕ),
      ∃ (C : ℝ) (L : ℕ),
        0 < C ∧
          ∀ (t : ℝ),
            0 ≤ t →
              ‖(1 + t) ^ q -
                    HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.powerTaylor q N
                      t‖ ≤
                C * t ^ N * (1 + t) ^ L)
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel_powerTaylor : ∀ (a : HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Pos) (q z : ℝ),
      0 < z →
        ∀ (N : ℕ),
          MeasureTheory.IntegrableOn
            (fun (t : ℝ) ↦
              Real.exp (-(z * t)) * t ^ ((↑a : ℝ) - 1) *
                HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.powerTaylor q N t)
            (Set.Ioi 0) MeasureTheory.MeasureSpace.volume)
    (h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integral_powerTaylor : ∀ (a : HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.Pos) (b z : ℝ),
      0 < z →
        ∀ (N : ℕ),
          ∫ (t : ℝ) in Set.Ioi 0,
              Real.exp (-(z * t)) * t ^ ((↑a : ℝ) - 1) *
                HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.powerTaylor
                  (b - (↑a : ℝ) - 1) N t =
            Real.Gamma (↑a : ℝ) *
              HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer.uExpansion (↑a : ℝ) b N z)
    :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 1 ≤ z →
      ‖UIr a b z - uExpansion a.1 b N z‖ ≤ C * z ^ (-a.1 - (N : ℝ)) := by
  obtain ⟨C₀, L, hC₀, hrem⟩ := h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_exists_powerTaylor_remainder_bound (b - a.1 - 1) N
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
  have hpol := h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrableOn_gammaKernel_powerTaylor a (b - a.1 - 1) z hz0 N
  have hker := h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integrable_laplaceKernel a b z hz0
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
    rw [he, hd, h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_integral_powerTaylor a b z hz0 N]
    change (Real.Gamma a.1)⁻¹ * _ - _ = _
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ (Real.Gamma_pos_of_pos a.2).ne', one_mul]
  rw [heq, norm_mul, Real.norm_of_nonneg (inv_pos.mpr (Real.Gamma_pos_of_pos a.2)).le]
  have h := h_HypoellipticAleksandrov_KineticAleksandrov_Counterexample_Kummer_laplaceTaylor_remainder_bound a (b - a.1 - 1) N L C₀ hC₀.le hrem z hz
  exact (mul_le_mul_of_nonneg_left h (inv_pos.mpr (Real.Gamma_pos_of_pos a.2)).le).trans_eq
    (by dsimp only [C]; ring)
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Kummer
