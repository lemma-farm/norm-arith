module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.ArcGeometry
public import Examples.nihargargava__systole_bound.Dependencies.v55588d36833b.CookMagyar.FiniteFourier
@[expose] public section
open scoped ArithmeticFunction BigOperators
namespace SystolicGrowth
namespace CookMagyarMajorArc
open CookMagyarArcs CookMagyarCircle CookMagyarFiniteFourier
/-! # Exact arithmetic decomposition on a cubic major arc

Before invoking primes in arithmetic progressions, the von--Mangoldt sum at
`a/q + beta` splits exactly into residue-class sums modulo `q`.  The finite
cubic character is constant on each fiber.  This module proves that identity
without any asymptotic input.
-/
theorem cast_primeCubic_zmod {q : ℕ} [NeZero q] (x : ℕ) :
    (primeCubic x : ZMod q) = cubicResidue (x : ZMod q) := by
  unfold primeCubic cubicResidue
  rw [Nat.cast_sub (Nat.le_pow (by norm_num : 0 < 3))]
  push_cast
  ring
theorem addChar_add_real (alpha beta : ℝ) (k : ℕ) :
    addChar (alpha + beta) k = addChar alpha k * addChar beta k := by
  unfold addChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
/-- A real rational phase agrees exactly with the standard additive
character on `ZMod q`. -/
theorem addChar_rationalCenter
    {q : ℕ} [NeZero q] (a k : ℕ) :
    addChar (rationalCenter a q) k =
      standardAdditiveCharacter ((a : ZMod q) * (k : ZMod q)) := by
  unfold rationalCenter
  change addChar ((a : ℝ) / (q : ℝ)) k =
    ZMod.stdAddChar ((a : ZMod q) * (k : ZMod q))
  rw [show (a : ZMod q) * (k : ZMod q) =
      (((a * k : ℤ) : ZMod q)) by norm_num]
  rw [ZMod.stdAddChar_coe]
  unfold addChar
  push_cast
  congr 1
  field_simp [NeZero.ne q]
end CookMagyarMajorArc
end SystolicGrowth
