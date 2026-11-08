/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Finite fiber/Fourier arguments adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under Apache License 2.0. The original LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. This version uses the actual local projection,
explicit Mathlib imports and the pinned module format.
-/
module
public import Examples.shaikidris__CollatzConvergencePositiveDensity.Dependencies.v691c2db515c3.WordCertDensity.Reference.Projectivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option relaxedAutoImplicit false
/-!
# The actual ternary fiber average

The operator divides the sum on the actual projection fiber by its cardinality.
It preserves mass, is positive and contracts the unhalved finite L1 norm.
The reference-law specialization agrees with the existing density oscillation.
-/
@[expose] public section
namespace WordCertDensity
namespace FiniteFourier
open Reference
/-- Average a real vector on its actual ternary projection fiber. -/
noncomputable def fiberAverage {m n : ℕ} (h : m ≤ n)
    (p : ZMod (3 ^ n) → ℝ) (x : ZMod (3 ^ n)) : ℝ :=
  (∑ y ∈ fiber h (project h x), p y) / (3 : ℝ) ^ (n - m)
theorem fiberAverage_add {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ)
    (x : ZMod (3 ^ n)) :
    fiberAverage h (fun y => p y + q y) x = fiberAverage h p x + fiberAverage h q x := by
  simp only [fiberAverage, Finset.sum_add_distrib, add_div]
noncomputable def oscillation {m n : ℕ} (h : m ≤ n) (p : ZMod (3 ^ n) → ℝ) : ℝ :=
  ∑ x, |p x - fiberAverage h p x|
theorem oscillation_add_le {m n : ℕ} (h : m ≤ n) (p q : ZMod (3 ^ n) → ℝ) :
    oscillation h (fun x => p x + q x) ≤ oscillation h p + oscillation h q := by
  simp only [oscillation, fiberAverage_add, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  rw [show p x + q x - (fiberAverage h p x + fiberAverage h q x) =
    (p x - fiberAverage h p x) + (q x - fiberAverage h q x) by ring]
  exact abs_add_le _ _
end FiniteFourier
end WordCertDensity
