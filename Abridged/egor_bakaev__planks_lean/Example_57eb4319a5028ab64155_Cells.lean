module

public import Mathlib

-- ==== Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Annulus ====
public section
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

end
end

-- ==== Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Overlap.Basic ====
public section
/-!
# Basic planar geometry for the quantitative overlap theorem

Coordinates in the plane, the quarter-turn `J`, orthonormal frames (which are
measure preserving), elementary facts about planks (center line, angle), and indexed
families of planks with their counting function, hole and excess-overlap cost.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
/-! ### Numerical constants of the proof -/

/-- The quarter turn `J(x₀, x₁) = (-x₁, x₀)`. -/
def J (x : Plane) : Plane := WithLp.toLp 2 ![-x 1, x 0]

/-! ### Orthonormal frames -/
namespace Plank
/-- The offset `(a + b)/2` of the center line. -/
def mid (P : Plank) : ℝ := (P.a + P.b) / 2
/-- The center line `ℓ_P = {x : ⟪x, n⟫ = (a + b)/2}`. -/
def centerLine (P : Plank) : Set Plane := {x | inner ℝ x P.n = P.mid}
/-- The acute angle between the center lines of two planks (`0` if parallel). -/
def ang (P Q : Plank) : ℝ := Real.arccos |inner ℝ P.n Q.n|
set_option linter.unusedVariables false in
axiom _root_.Annulus.Plank.abs_inner_n_le : ∀ (P Q : Annulus.Plank), |Inner.inner ℝ P.n Q.n| ≤ 1
end Plank
/-! ### Indexed families of planks -/
section Families
variable {ι : Type*} [Fintype ι]
end Families
end Annulus
end

end
end

-- ==== Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Overlap.Geometry ====
public section
/-!
# Elementary planar geometry for the overlap theorem

Angle and sine facts for center lines, intersection of two lines, and the
distance from a point to a center line.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
/-! ### Unit vectors -/
namespace Plank

set_option linter.unusedVariables false in
axiom _root_.Annulus.Plank.sin_ang_pos : ∀ {P Q : Annulus.Plank}, P.ang Q ≠ 0 → 0 < |Inner.inner ℝ (Annulus.J P.n) Q.n|

def crossPt (P Q : Plank) : Plane :=
  P.mid • P.n + ((Q.mid - P.mid * inner ℝ P.n Q.n) / inner ℝ (J P.n) Q.n) • J P.n

end Plank
end Annulus
end

end
end

-- ==== Examples.egor_bakaev__planks_lean.Examples.Example_57eb4319a5028ab64155_Cells ====
/-!
# Cells of the final hole, greedy selection, and auxiliary plane geometry

* The final hole of a family of surviving planks `S` is partitioned by sign patterns
  `A ⊆ S` into the convex open *cells* `cell P S A`.
* An abstract greedy (Vitali-type) selection of pairwise disjoint sets.
* Small facts on coordinates and on crossing points of center lines.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
/-! ### Plane geometry -/

namespace Plank
set_option linter.unusedVariables false in
/-- A point close to two nonparallel center lines is close to their crossing point. -/
lemma norm_sub_crossPt_le {P Q : Plank} (h : P.ang Q ≠ 0) {x : Plane} {δ : ℝ}
    (hP : |inner ℝ x P.n - P.mid| ≤ δ) (hQ : |inner ℝ x Q.n - Q.mid| ≤ δ) 
    (h_Annulus_norm_J : ∀ (x : Annulus.Plane), ‖Annulus.J x‖ = ‖x‖)
    (h_Annulus_Plank_crossPt_mem_left : ∀ (P Q : Annulus.Plank), P.crossPt Q ∈ P.centerLine)
    (h_Annulus_Plank_crossPt_mem_right : ∀ {P Q : Annulus.Plank}, P.ang Q ≠ 0 → P.crossPt Q ∈ Q.centerLine)
    (h_Annulus_inner_decomp : ∀ {n : Annulus.Plane},
      ‖n‖ = 1 →
        ∀ (x q : Annulus.Plane),
          Inner.inner ℝ x q =
            Inner.inner ℝ x n * Inner.inner ℝ n q +
              Inner.inner ℝ x (Annulus.J n) * Inner.inner ℝ (Annulus.J n) q)
    (h_Annulus_decomp_frame : ∀ {e : Annulus.Plane},
      ‖e‖ = 1 →
        ∀ (x : Annulus.Plane), x = Inner.inner ℝ x e • e + Inner.inner ℝ x (Annulus.J e) • Annulus.J e)
    (h_Annulus_Plank_mem_centerLine : ∀ {P : Annulus.Plank} {x : Annulus.Plane}, x ∈ P.centerLine ↔ Inner.inner ℝ x P.n = P.mid)
    :
    ‖x - P.crossPt Q‖ ≤ δ + 2 * δ / |inner ℝ (J P.n) Q.n| := by
  have hs := P.sin_ang_pos h
  set c := P.crossPt Q
  set d := x - c
  have hdP : inner ℝ d P.n = inner ℝ x P.n - P.mid := by
    rw [inner_sub_left, h_Annulus_Plank_mem_centerLine.1 (h_Annulus_Plank_crossPt_mem_left P Q)]
  have hdQ : inner ℝ d Q.n = inner ℝ x Q.n - Q.mid := by
    rw [inner_sub_left, h_Annulus_Plank_mem_centerLine.1 (h_Annulus_Plank_crossPt_mem_right h)]
  have hdec := h_Annulus_inner_decomp P.norm_n d Q.n
  have hc : |inner ℝ P.n Q.n| ≤ 1 := P.abs_inner_n_le Q
  have h1 : |inner ℝ d (J P.n)| * |inner ℝ (J P.n) Q.n| ≤ 2 * δ := by
    rw [← abs_mul]
    have : inner ℝ d (J P.n) * inner ℝ (J P.n) Q.n =
        inner ℝ d Q.n - inner ℝ d P.n * inner ℝ P.n Q.n := by linarith
    rw [this]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, hdP, hdQ]
    have : |inner ℝ x P.n - P.mid| * |inner ℝ P.n Q.n| ≤ δ := by
      calc _ ≤ |inner ℝ x P.n - P.mid| * 1 := by gcongr
        _ ≤ δ := by linarith
    linarith
  have h2 : |inner ℝ d (J P.n)| ≤ 2 * δ / |inner ℝ (J P.n) Q.n| := by
    rw [le_div_iff₀ hs]; exact h1
  have h3 : ‖d‖ ≤ |inner ℝ d P.n| + |inner ℝ d (J P.n)| := by
    conv_lhs => rw [h_Annulus_decomp_frame P.norm_n d]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, P.norm_n, h_Annulus_norm_J, P.norm_n, mul_one, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs]
  rw [hdP] at h3
  linarith
end Plank
end Annulus
end
