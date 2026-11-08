module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.MajorArcArithmetic
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.ArcGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.Floor
@[expose] public section
namespace SystolicGrowth.CookMagyarArcs
open CookMagyarCircle
/-! # Periodic cubic phases on wrapped major arcs

The Fourier characters have period one. A point in a circle-metric major arc
may lie across an endpoint of `[0,1]`; subtracting the nearest integer gives
a genuinely small real displacement from its rational center.
-/
/-- The additive character is trivial at integer frequencies. -/
theorem addChar_int (z : ℤ) (k : ℕ) :
    addChar (z : ℝ) k = 1 := by
  unfold addChar
  have h : 2 * Real.pi * Complex.I * (k : ℂ) * ((z : ℝ) : ℂ) =
      (((z * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]
/-- Real-frequency characters are unchanged by an integer shift. -/
theorem addChar_add_int (alpha : ℝ) (z : ℤ) (k : ℕ) :
    addChar (alpha + z) k = addChar alpha k := by
  rw [CookMagyarMajorArc.addChar_add_real]
  simp [addChar_int]
end SystolicGrowth.CookMagyarArcs
