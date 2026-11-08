module

public import SquaresInCircles.Common.Charts

/-!
# Charts of exterior squares in a disk

A sorted chart `(a, u)` of an exterior square whose far vertex lies in the
closed disk of squared radius `Q` has `1/2 ≤ a`, `0 ≤ u ≤ a` and `φ(a, u) ≤ Q`
(`ExteriorChart`). With a signed transverse coordinate `b`, `|b| = u`, the far
corner `(|a| + 1/2, |b| + 1/2)` lies in the disk and the centre `(a, b)` within
`√(Q - 1/4) - 1/2` of the disk centre.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-- The sorted chart `(a, u)` of an exterior square whose far vertex lies in the
closed disk of squared radius `Q`. -/
structure ExteriorChart (Q a u : ℝ) : Prop where
  half_le : 1/2 ≤ a
  u_nonneg : 0 ≤ u
  u_le : u ≤ a
  phi_le : phi a u ≤ Q

namespace ExteriorChart
variable {Q a u : ℝ} (h : ExteriorChart Q a u)
include h

lemma a_nonneg : 0 ≤ a := by linarith [h.half_le]

/-- `phi_le` with `φ` unfolded. -/
lemma containment : (a+1/2)^2+(u+1/2)^2 ≤ Q := h.phi_le

end ExteriorChart

/-- The far corner `(|a| + 1/2, |b| + 1/2)` lies in the disk. -/
lemma ExteriorChart.abs_box {Q a b : ℝ} (h : ExteriorChart Q a |b|) :
    (|a|+1/2)^2+(|b|+1/2)^2 ≤ Q := by
  rw [abs_of_nonneg h.a_nonneg]
  exact h.phi_le

/-- The centre `(a, b)` lies within `√(Q - 1/4) - 1/2` of the disk centre. -/
lemma ExteriorChart.center_sq_le {Q a b : ℝ} (h : ExteriorChart Q a |b|) :
    a^2+b^2 ≤ (Real.sqrt (Q-1/4)-1/2)^2 := by
  have hs := Real.sq_sqrt (show 0 ≤ Q-1/4 by nlinarith [h.containment,h.half_le,h.u_nonneg])
  rw [← sq_abs b]
  exact radial_sq_le_of_phi h.a_nonneg h.u_nonneg (h.phi_le.trans (by linarith))

/-- A sorted chart of an exterior square whose far vertex lies in the closed disk
of squared radius `Q` is an exterior chart. -/
lemma SquareChart.exteriorChart {S : UnitSquare} {o : Point} {Q : ℝ} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o) (hQ : phi (alpha S o) (beta S o) ≤ Q) :
    ExteriorChart Q C.a C.b :=
  ⟨C.exterior hsort hout,C.nonneg.2,hsort,chart_phi C hQ⟩

lemma signedB_abs {S : UnitSquare} {o : Point} (C : SquareChart S o) : |C.signedB|=C.b := by
  cases h : C.reversed <;> simp [SquareChart.signedB,h,abs_of_nonneg C.nonneg.2]

/-- `SquareChart.exteriorChart` with the signed transverse coordinate. -/
lemma SquareChart.exteriorChart_signed {S : UnitSquare} {o : Point} {Q : ℝ}
    (C : SquareChart S o) (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o)
    (hQ : phi (alpha S o) (beta S o) ≤ Q) : ExteriorChart Q C.a |C.signedB| := by
  rw [signedB_abs]
  exact C.exteriorChart hsort hout hQ

/-- The point of the closed square nearest to `o`, at the squared distance
`(max (a - 1/2) 0)² + (max (b - 1/2) 0)²`. -/
lemma chart_exists_clipped_point {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ∃ p : Point, closedSquare S p ∧
      normSq (sub p o)=(max (C.a-1/2) 0)^2+(max (C.b-1/2) 0)^2 :=
  C.transfer (fun a b => ∃ p : Point, closedSquare S p ∧
      normSq (sub p o)=(max (a-1/2) 0)^2+(max (b-1/2) 0)^2)
    (fun ⟨p,hp,hd⟩ => ⟨p,hp,by rw [hd,add_comm]⟩) (exists_clipped_point S o)

end SquaresInCircles
