module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.Combinatorics.Additive.CauchyDavenport
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Units
public import Mathlib.Logic.Equiv.Fin.Basic

-- ==== Examples.nihargargava__systole_bound.Dependencies.v0a5285bc13a6.CookMagyar.FiniteFourier ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarFiniteFourier
/-! # Finite Fourier expansion of the local cubic count

This file proves the exact finite-group identity underlying the local factors
in the Cook--Magyar circle method.  It contains no analytic estimate.
-/
variable {q : ℕ} [NeZero q]
/-- The reduction modulo `q` of the polynomial `X³ - X`. -/
def cubicResidue (x : ZMod q) : ZMod q := x ^ 3 - x

/-- The standard complex additive character on `ZMod q`. -/
noncomputable abbrev standardAdditiveCharacter : AddChar (ZMod q) ℂ :=
  ZMod.stdAddChar
/-- The one-variable complete exponential sum over the units modulo `q`. -/
noncomputable def unitCubicExponentialSum (a : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ,
    standardAdditiveCharacter (a * cubicResidue (u : ZMod q))

end CookMagyarFiniteFourier
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Dependencies.v0a5285bc13a6.CookMagyar.SingularSeries ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarFiniteFourier
/-! # Singular-series objects for the diagonal cubic

This file gives concrete definitions of the complete-sum coefficient
`B(T,q)`, its finite truncations, the full singular series, and the formal
prime local factors.  Convergence and the uniform Euler-tail bound are
subsequent theorems; no default value or abstract placeholder is hidden in
these definitions.
-/
/-- The complete-sum coefficient `B(T,q)` for a positive modulus.  The
outer frequency is restricted to units, exactly as in the classical
singular-series expansion. -/
noncomputable def singularSeriesCoefficient
    (q n T : ℕ) (hq : q ≠ 0) : ℂ := by
  letI : NeZero q := ⟨hq⟩
  exact ((Nat.totient q : ℂ)⁻¹) ^ n *
    ∑ a : (ZMod q)ˣ,
      unitCubicExponentialSum (a : ZMod q) ^ n *
        standardAdditiveCharacter (-((a : ZMod q) * (T : ZMod q)))
/-- The coefficient extended by zero at the non-modulus `q=0`. -/
noncomputable def singularSeriesTerm (n T q : ℕ) : ℂ :=
  if hq : q = 0 then 0 else singularSeriesCoefficient q n T hq

/-- The formal local factor at a prime `p`, written as
`1 + ∑_{k≥1} B(T,p^k)`. -/
noncomputable def primeLocalFactor (p n T : ℕ) : ℂ :=
  1 + ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 1))

end CookMagyarFiniteFourier
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Examples.Example_adeb3b8115761ec1c83a_LocalFactorBridge ====
@[expose] public section
/-!
# Prime local-factor decomposition

This file records the exact reindexing needed to combine the prime-modulus
estimate with the higher-prime-power tail.  The summability hypothesis is
explicit: later arithmetic modules must discharge it rather than hiding it in
an Euler-product assumption.
-/
namespace SystolicGrowth
namespace CookMagyarFiniteFourier
open scoped BigOperators


set_option linter.unusedVariables false in
theorem norm_primeLocalFactor_sub_one_le_large_prime
    {p n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p) (hn : 33 ≤ n) 
    (h_SystolicGrowth_CookMagyarPrimePower_summable_norm_singularSeriesTerm_higherPrimePower : ∀ {p n T : ℕ} [NeZero p],
      Nat.Prime p →
        5 ≤ p →
          33 ≤ n →
            Summable fun (k : ℕ) ↦
              ‖SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm n T (p ^ (k + 2))‖)
    (h_SystolicGrowth_CookMagyarFiniteFourier_primeLocalFactor_eq_prime_add_higherTail_of_large_prime : ∀ {p n T : ℕ} [NeZero p],
      Nat.Prime p →
        5 ≤ p →
          33 ≤ n →
            SystolicGrowth.CookMagyarFiniteFourier.primeLocalFactor p n T =
              1 + SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm n T p +
                ∑' (k : ℕ), SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm n T (p ^ (k + 2)))
    (h_SystolicGrowth_CookMagyarFiniteFourier_norm_singularSeriesTerm_prime_le_inv_pow : ∀ {p : ℕ} [NeZero p],
      Nat.Prime p →
        5 ≤ p →
          ∀ {n : ℕ},
            32 ≤ n →
              ∀ (T : ℕ),
                ‖SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm n T p‖ ≤
                  40 ^ 8 * (5 / 4) ^ n / (↑p : ℝ) ^ 7)
    (h_SystolicGrowth_CookMagyarPrimePower_tsum_norm_singularSeriesTerm_higherPrimePower_le : ∀ {p n T : ℕ} [NeZero p],
      Nat.Prime p →
        5 ≤ p →
          33 ≤ n →
            ∑' (k : ℕ), ‖SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm n T (p ^ (k + 2))‖ ≤
              2 ^ n * (5 / 4) ^ (n - 1) * (1 + (↑p : ℝ)) * (↑p : ℝ)⁻¹ ^ (n - 2) /
                (1 - (↑p : ℝ)⁻¹ ^ (n - 2)))
    :
    ‖primeLocalFactor p n T - 1‖ ≤
      (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
  have hsplit := h_SystolicGrowth_CookMagyarFiniteFourier_primeLocalFactor_eq_prime_add_higherTail_of_large_prime
    (p := p) (n := n) (T := T) hp hp5 hn
  have htailNorm :=
    h_SystolicGrowth_CookMagyarPrimePower_summable_norm_singularSeriesTerm_higherPrimePower
      (T := T) hp hp5 hn
  have hn32 : 32 ≤ n := by omega
  have hprime := h_SystolicGrowth_CookMagyarFiniteFourier_norm_singularSeriesTerm_prime_le_inv_pow hp hp5 hn32 T
  have htail :=
    h_SystolicGrowth_CookMagyarPrimePower_tsum_norm_singularSeriesTerm_higherPrimePower_le
      (T := T) hp hp5 hn
  rw [hsplit]
  calc
    ‖1 + singularSeriesTerm n T p +
        ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2)) - 1‖ =
        ‖singularSeriesTerm n T p +
          ∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ := by
            congr 1
            ring
    _ ≤ ‖singularSeriesTerm n T p‖ +
          ‖∑' k : ℕ, singularSeriesTerm n T (p ^ (k + 2))‖ := norm_add_le _ _
    _ ≤ ‖singularSeriesTerm n T p‖ +
          ∑' k : ℕ, ‖singularSeriesTerm n T (p ^ (k + 2))‖ := by
            gcongr
            exact norm_tsum_le_tsum_norm htailNorm
    _ ≤ (40 : ℝ) ^ 8 * ((5 : ℝ) / 4) ^ n / (p : ℝ) ^ 7 +
        ((2 : ℝ) ^ n * ((5 : ℝ) / 4) ^ (n - 1)) *
          (1 + (p : ℝ)) * ((p : ℝ)⁻¹) ^ (n - 2) /
            (1 - ((p : ℝ)⁻¹) ^ (n - 2)) := by
            exact add_le_add hprime htail
end CookMagyarFiniteFourier
end SystolicGrowth
