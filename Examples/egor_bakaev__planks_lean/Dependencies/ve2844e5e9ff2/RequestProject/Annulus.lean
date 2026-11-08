module
public import Mathlib
/-!
# Bezdek's annulus theorem (reduction to the quantitative overlap theorem)

This file formalizes Section 7 ("From area stability to Bezdek's width theorem") of
`area_stability_formalization.tex`:

* planks, the hole `H(𝒫)`, the counting function `M_𝒫` and the excess-overlap cost `I(𝒫)`;
* the relative-width measure `dμ = dx / (2π √(1 - ‖x‖²))` on the unit disk and
  Lemma 7.1: `μ(P) = w(P)/2` for planks whose normal interval lies in `[-1, 1]`;
* Theorem 7.2 (Bezdek's annulus theorem), derived from the quantitative overlap theorem
  (Theorem 2.1), which enters as an explicit hypothesis.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)
/-- A planar plank `P(n,a,b) = {x : a ≤ ⟪x, n⟫ ≤ b}` with unit normal `n` and `a ≤ b`. -/
structure Plank where
  n : Plane
  norm_n : ‖n‖ = 1
  a : ℝ
  b : ℝ
  a_le_b : a ≤ b
namespace Plank
end Plank
end Annulus
end
