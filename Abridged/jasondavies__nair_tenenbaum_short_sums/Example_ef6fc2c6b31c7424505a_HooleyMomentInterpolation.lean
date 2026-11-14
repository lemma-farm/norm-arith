module

public import Mathlib

-- ==== Examples.jasondavies__nair_tenenbaum_short_sums.Dependencies.v6c41c6ad715e.NairTenenbaum.Hooley.Hooley ====
public section
/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
set_option autoImplicit false
/-! # Hooley's divisor concentration function

The definition in §1 and the coprime multiplication bound used to place it in
the Nair–Tenenbaum class. Logarithmic windows are equivalent to the paper's
exponential windows for positive divisors.
-/
@[expose] public section
namespace NairTenenbaum
open Finset Real
/-- Number of divisors with logarithm in `(u,u+1]`. -/
noncomputable def divisorWindow (n : ℕ) (u : ℝ) : ℕ :=
  (n.divisors.filter fun d : ℕ => u < log d ∧ log d ≤ u + 1).card

end NairTenenbaum

end
end

-- ==== Examples.jasondavies__nair_tenenbaum_short_sums.Dependencies.v6c41c6ad715e.NairTenenbaum.Hooley.HooleyMoments ====
public section
/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
set_option autoImplicit false
/-! # Integral moments of Hooley's divisor windows

These moments are the analytic starting point of the weighted mean estimate
in Tenenbaum, *Sur une question d'Erdős et Schinzel, II*, Lemma 2.2.
Integrability is proved from the finite indicator representation, including
the convention at `n=0`.
-/
@[expose] public section
namespace NairTenenbaum
open Finset Real MeasureTheory
/-- The divisor count in a logarithmic window used to define Hooley's function. -/
noncomputable def hooleyWindow (n : ℕ) (u : ℝ) : ℝ := divisorWindow n u

/-- The moment `M_q(n)`; positive orders are the integrable ones used below. -/
noncomputable def hooleyMoment (q n : ℕ) : ℝ := ∫ u : ℝ, hooleyWindow n u ^ q

end NairTenenbaum

end
end

-- ==== Examples.jasondavies__nair_tenenbaum_short_sums.Examples.Example_ef6fc2c6b31c7424505a_HooleyMomentInterpolation ====
/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
set_option autoImplicit false
/-! # Interpolation of Hooley's integral moments

Weighted arithmetic-geometric means give the interpolation between `M₁=τ`
and `M_q`. This supplies the exponents of `τ` and `M_q` in the mixed-term
estimate used in the weighted mean proof.
-/
@[expose] public section
namespace NairTenenbaum
open Finset Real MeasureTheory

set_option linter.unusedVariables false in
theorem hooleyMoment_interpolation (n : ℕ) {j q : ℕ}
    (hq : 1 < q) (hj : 1 ≤ j) (hjq : j ≤ q) 
    (h_NairTenenbaum_hooleyMoment_nonneg : ∀ (q n : ℕ), 0 ≤ NairTenenbaum.hooleyMoment q n)
    (h_NairTenenbaum_hooleyMoment_at_zero : ∀ {q : ℕ}, 0 < q → NairTenenbaum.hooleyMoment q 0 = 0)
    (h_NairTenenbaum_moment_interpolation_pointwise : ∀ {x A B a b : ℝ} {j q : ℕ},
      0 ≤ x →
        0 < A →
          0 < B →
            0 ≤ a →
              0 ≤ b →
                a + b = 1 →
                  a + (↑q : ℝ) * b = (↑j : ℝ) →
                    0 < j → x ^ j ≤ A ^ a * B ^ b * (a * (x / A) + b * (x ^ q / B)))
    (h_NairTenenbaum_integral_hooleyWindow : ∀ (n : ℕ), ∫ (u : ℝ), NairTenenbaum.hooleyWindow n u = (↑n.divisors.card : ℝ))
    (h_NairTenenbaum_hooleyWindow_nonneg : ∀ (n : ℕ) (u : ℝ), 0 ≤ NairTenenbaum.hooleyWindow n u)
    (h_NairTenenbaum_hooleyMoment_pos : ∀ {n q : ℕ}, n ≠ 0 → 0 < q → 0 < NairTenenbaum.hooleyMoment q n)
    (h_NairTenenbaum_integrable_hooleyWindow : ∀ (n : ℕ), MeasureTheory.Integrable (NairTenenbaum.hooleyWindow n) MeasureTheory.MeasureSpace.volume)
    (h_NairTenenbaum_integrable_hooleyWindow_pow : ∀ (n : ℕ) {q : ℕ},
      0 < q →
        MeasureTheory.Integrable (fun (u : ℝ) ↦ NairTenenbaum.hooleyWindow n u ^ q)
          MeasureTheory.MeasureSpace.volume)
    :
    hooleyMoment j n ≤ (n.divisors.card : ℝ) ^ (((q : ℝ) - j) / ((q : ℝ) - 1)) *
      hooleyMoment q n ^ (((j : ℝ) - 1) / ((q : ℝ) - 1)) := by
  by_cases hn : n = 0
  · subst n
    rw [h_NairTenenbaum_hooleyMoment_at_zero (by omega : 0 < j)]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (h_NairTenenbaum_hooleyMoment_nonneg q 0) _)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjqR : (j : ℝ) ≤ q := by exact_mod_cast hjq
  let a : ℝ := ((q : ℝ) - j) / ((q : ℝ) - 1)
  let b : ℝ := ((j : ℝ) - 1) / ((q : ℝ) - 1)
  have ha : 0 ≤ a := div_nonneg (by linarith) (by linarith)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have hexp : a + (q : ℝ) * b = j := by dsimp [a, b]; field_simp; ring
  have hτ : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast (card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩ : 0 < n.divisors.card)
  have hM : 0 < hooleyMoment q n := h_NairTenenbaum_hooleyMoment_pos hn (by omega)
  have hi₁ := ((h_NairTenenbaum_integrable_hooleyWindow n).div_const (n.divisors.card : ℝ)).const_mul a
  have hi₂ := ((h_NairTenenbaum_integrable_hooleyWindow_pow n (show 0 < q by omega)).div_const
    (hooleyMoment q n)).const_mul b
  have H := integral_mono (h_NairTenenbaum_integrable_hooleyWindow_pow n (show 0 < j by omega))
    ((hi₁.add hi₂).const_mul ((n.divisors.card : ℝ) ^ a * hooleyMoment q n ^ b))
    (fun u => h_NairTenenbaum_moment_interpolation_pointwise (h_NairTenenbaum_hooleyWindow_nonneg n u) hτ hM ha hb hab hexp (by
      omega))
  simp only [Pi.add_apply] at H
  rw [integral_const_mul, integral_add hi₁ hi₂] at H
  simp only [integral_const_mul, integral_div, h_NairTenenbaum_integral_hooleyWindow] at H
  change hooleyMoment j n ≤ (n.divisors.card : ℝ) ^ a * hooleyMoment q n ^ b *
    (a * ((n.divisors.card : ℝ) / n.divisors.card) + b * (hooleyMoment q n / hooleyMoment q n)) at H
  simpa only [div_self hτ.ne', div_self hM.ne', mul_one, hab, a, b] using H

end NairTenenbaum
