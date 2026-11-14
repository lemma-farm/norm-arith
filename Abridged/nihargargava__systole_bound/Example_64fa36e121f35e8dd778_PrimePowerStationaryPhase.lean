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

-- ==== Examples.nihargargava__systole_bound.Dependencies.v67f76fdbbe1d.CookMagyar.LocalNonsingular ====
public section
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
@[expose] public section
open scoped BigOperators
namespace SystolicGrowth
namespace CookMagyarLocal
/-! # Nonsingular local solutions

The four-variable local-solubility theorem supplies the nonzero coordinates.
For five or more variables, an additional coordinate equal to `1` both leaves
the equation unchanged and makes the solution nonsingular: `1 ^ 3 - 1 = 0`,
whereas the derivative at `1` is `2`.
-/
/-- The derivative of the cubic map `x ↦ x ^ 3 - x`. -/
def cubicDerivative {q : ℕ} (x : ZMod q) : ZMod q :=
  3 * x ^ 2 - 1
end CookMagyarLocal
end SystolicGrowth

end
end

-- ==== Examples.nihargargava__systole_bound.Examples.Example_64fa36e121f35e8dd778_PrimePowerStationaryPhase ====
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
open CookMagyarFiniteFourier CookMagyarLocal

/-! ## Taylor linearization on a half-size block -/

/-- Exact stationary-phase decomposition of a unit-restricted complete
cubic sum over a prime-power block.  Orthogonality kills every low residue
whose phase derivative is nonzero modulo the high block. -/
axiom unitCubicExponentialSum_primePower_block
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hm : 1 ≤ m) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d)) :
    unitCubicExponentialSum a =
      ∑ x : ZMod (p ^ m), if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0

/-- Core.Reduction from `p^m` to `p^d` when `d ≤ m`. -/
def primePowerCast (p m d : ℕ) (hdm : d ≤ m) :
    ZMod (p ^ m) →+* ZMod (p ^ d) :=
  ZMod.castHom (pow_dvd_pow p hdm) (ZMod (p ^ d))

@[simp] axiom primePowerCast_cubicDerivative
    (p m d : ℕ) (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    primePowerCast p m d hdm (cubicDerivative x) =
      cubicDerivative (primePowerCast p m d hdm x)
/-- Low residues whose cubic derivative vanishes after reduction to
`p^d`. -/
def cubicDerivativeCastRootFinset
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) :
    Finset (ZMod (p ^ m)) :=
  Finset.univ.filter fun x ↦
    primePowerCast p m d hdm (cubicDerivative x) = 0

/-- For `p ≥ 5`, at most `2p^(m-d)` low residues are stationary modulo
`p^d`. -/
axiom card_cubicDerivativeCastRootFinset_le
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hd : 0 < d) (hdm : d ≤ m) :
    (cubicDerivativeCastRootFinset p m d hdm).card ≤
      2 * p ^ (m - d)
private axiom cast_cubicDerivative_natCast_eq_primePowerCast
    (p m d : ℕ) [NeZero p] (hdm : d ≤ m) (x : ZMod (p ^ m)) :
    ZMod.castHom (dvd_mul_left (p ^ d) (p ^ m)) (ZMod (p ^ d))
        (cubicDerivative (x.val : ZMod (p ^ m * p ^ d))) =
        primePowerCast p m d hdm (cubicDerivative x)
theorem norm_unitCubicExponentialSum_primePower_block_le
    {p m d : ℕ} [NeZero p] (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : 1 ≤ m) (hd : 0 < d) (hdm : d ≤ m)
    (a : ZMod (p ^ m * p ^ d)) (ha : IsUnit a) :
    ‖unitCubicExponentialSum a‖ ≤ 2 * (p : ℝ) ^ m := by
  classical
  let s := cubicDerivativeCastRootFinset p m d hdm
  let castHigh : ZMod (p ^ m * p ^ d) →+* ZMod (p ^ d) :=
    ZMod.castHom (dvd_mul_left (p ^ d) (p ^ m)) (ZMod (p ^ d))
  have haHigh : IsUnit (castHigh a) := ha.map castHigh
  have hcondition (x : ZMod (p ^ m)) :
      (((a * cubicDerivative
        (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0) ↔
          x ∈ s := by
    have hderiv := cast_cubicDerivative_natCast_eq_primePowerCast
      p m d hdm x
    change castHigh (cubicDerivative
      (x.val : ZMod (p ^ m * p ^ d))) =
        primePowerCast p m d hdm (cubicDerivative x) at hderiv
    change castHigh (a * cubicDerivative
      (x.val : ZMod (p ^ m * p ^ d))) = 0 ↔ x ∈ s
    rw [map_mul, hderiv]
    constructor
    · intro hzero
      have hderivzero : primePowerCast p m d hdm (cubicDerivative x) = 0 := by
        apply haHigh.mul_left_cancel
        simpa using hzero
      simpa [s, cubicDerivativeCastRootFinset] using hderivzero
    · intro hx
      have hderivzero : primePowerCast p m d hdm (cubicDerivative x) = 0 := by
        simpa [s, cubicDerivativeCastRootFinset] using hx
      rw [hderivzero, mul_zero]
  rw [unitCubicExponentialSum_primePower_block hp hm hdm a]
  calc
    ‖∑ x : ZMod (p ^ m), if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0‖ ≤
      ∑ x : ZMod (p ^ m), ‖if IsUnit x then
        standardAdditiveCharacter
            (a * CookMagyarFiniteFourier.cubicResidue
              (x.val : ZMod (p ^ m * p ^ d))) *
          (if (((a * cubicDerivative
              (x.val : ZMod (p ^ m * p ^ d))).cast : ZMod (p ^ d)) = 0)
            then (p ^ d : ℂ) else 0)
        else 0‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod (p ^ m),
        if x ∈ s then (p ^ d : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hxs : x ∈ s
      · have hc := (hcondition x).2 hxs
        by_cases hxunit : IsUnit x
        · rw [if_pos hxunit, if_pos hc]
          simp [hxs, AddChar.norm_apply]
        · rw [if_neg hxunit]
          simp [hxs]
      · have hc := (hcondition x).not.mpr hxs
        by_cases hxunit : IsUnit x
        · rw [if_pos hxunit, if_neg hc]
          simp [hxs]
        · rw [if_neg hxunit]
          simp [hxs]
    _ = ∑ _x ∈ s, (p ^ d : ℝ) :=
      Finset.sum_ite_mem_eq s (fun _x ↦ (p ^ d : ℝ))
    _ = (s.card : ℝ) * (p ^ d : ℝ) := by
      simp [nsmul_eq_mul]
    _ ≤ ((2 * p ^ (m - d) : ℕ) : ℝ) * (p ^ d : ℝ) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_cubicDerivativeCastRootFinset_le hp hp5 hd hdm
      · positivity
    _ = 2 * (p : ℝ) ^ m := by
      push_cast
      have hpowers : (p : ℝ) ^ (m - d) * (p : ℝ) ^ d =
          (p : ℝ) ^ m := by
        rw [← pow_add, Nat.sub_add_cancel hdm]
      rw [mul_assoc, hpowers]

end CookMagyarPrimePower
end SystolicGrowth
