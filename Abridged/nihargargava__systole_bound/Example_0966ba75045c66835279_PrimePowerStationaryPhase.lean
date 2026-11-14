module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Tactic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Combinatorics.Additive.CauchyDavenport
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.ZMod.Units
public import Mathlib.Logic.Equiv.Fin.Basic

-- ==== Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.FiniteFourier ====
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

-- ==== Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.SingularSeries ====
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

end CookMagyarFiniteFourier
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Examples.Example_0966ba75045c66835279_PrimePowerStationaryPhase ====
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarPrimePower
/-! # Prime-power stationary-phase algebra

This file develops the finite algebra behind the prime-power tail of the
Cook--Magyar singular series.  The central reindexing writes a residue
modulo `M * R` uniquely as `x + M*y`, with `x` modulo `M` and `y` modulo
`R`.  For `M = p^m`, `R = p^d`, and `d ≤ m`, the quadratic Taylor
remainder of `X³-X` vanishes modulo `p^(m+d)`.  Orthogonality in `y`
then restricts the outer sum to residues for which the derivative vanishes
modulo `p^d`.
-/
open CookMagyarFiniteFourier 

/-! ## Taylor linearization on a half-size block -/


set_option linter.unusedVariables false in
/-- The stationary-phase estimate summed over all unit frequencies and
normalized as a singular-series coefficient. -/
theorem norm_singularSeriesTerm_primePower_block_le
    {p m d n T : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hd : 0 < d) (hdm : d ≤ m) 
    (h_SystolicGrowth_CookMagyarPrimePower_norm_unitCubicExponentialSum_primePower_block_le : ∀ {p m d : ℕ} [inst : NeZero p],
      Nat.Prime p →
        5 ≤ p →
          1 ≤ m →
            0 < d →
              d ≤ m →
                ∀ (a : ZMod (p ^ m * p ^ d)),
                  IsUnit a →
                    ‖SystolicGrowth.CookMagyarFiniteFourier.unitCubicExponentialSum a‖ ≤
                      2 * (↑p : ℝ) ^ m)
    (h_SystolicGrowth_CookMagyarFiniteFourier_singularSeriesTerm_of_pos : ∀ (n T : ℕ) {q : ℕ} (hq : 0 < q),
      SystolicGrowth.CookMagyarFiniteFourier.singularSeriesTerm n T q =
        SystolicGrowth.CookMagyarFiniteFourier.singularSeriesCoefficient q n T (LT.lt.ne' hq))
    :
    ‖singularSeriesTerm n T (p ^ m * p ^ d)‖ ≤
      ‖((Nat.totient (p ^ m * p ^ d) : ℂ)⁻¹)‖ ^ n *
        (Nat.totient (p ^ m * p ^ d) : ℝ) *
          (2 * (p : ℝ) ^ m) ^ n := by
  rw [h_SystolicGrowth_CookMagyarFiniteFourier_singularSeriesTerm_of_pos n T (by positivity)]
  unfold singularSeriesCoefficient
  rw [norm_mul, norm_pow]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    ‖∑ a : (ZMod (p ^ m * p ^ d))ˣ,
        unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
          standardAdditiveCharacter
            (-((a : ZMod (p ^ m * p ^ d)) *
              (T : ZMod (p ^ m * p ^ d))))‖ ≤
        ∑ a : (ZMod (p ^ m * p ^ d))ˣ,
          ‖unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
            standardAdditiveCharacter
              (-((a : ZMod (p ^ m * p ^ d)) *
                (T : ZMod (p ^ m * p ^ d))))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod (p ^ m * p ^ d))ˣ,
        (2 * (p : ℝ) ^ m) ^ n := by
      apply Finset.sum_le_sum
      intro a _ha
      have hsum := h_SystolicGrowth_CookMagyarPrimePower_norm_unitCubicExponentialSum_primePower_block_le
        hp hp5 hm hd hdm (a : ZMod (p ^ m * p ^ d)) a.isUnit
      calc
        ‖unitCubicExponentialSum (a : ZMod (p ^ m * p ^ d)) ^ n *
            standardAdditiveCharacter
              (-((a : ZMod (p ^ m * p ^ d)) *
                (T : ZMod (p ^ m * p ^ d))))‖ =
            ‖unitCubicExponentialSum
              (a : ZMod (p ^ m * p ^ d))‖ ^ n := by
                simp [norm_pow, AddChar.norm_apply]
        _ ≤ (2 * (p : ℝ) ^ m) ^ n :=
          pow_le_pow_left₀
            (norm_nonneg (unitCubicExponentialSum
              (a : ZMod (p ^ m * p ^ d)))) hsum n
    _ = (Nat.totient (p ^ m * p ^ d) : ℝ) *
        (2 * (p : ℝ) ^ m) ^ n := by
      simp [ZMod.card_units_eq_totient, nsmul_eq_mul]
end CookMagyarPrimePower
end SystolicGrowth
