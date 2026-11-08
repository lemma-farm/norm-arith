module

public import SquaresInCircles.Common.Sweep
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Charts

A chart of a square seen from the disk centre records a phase and a possible
reversal of orientation in which the square, on every circle about the disk
centre and slid along the ray through its centre, is the axis-parallel square
at `(a, b)` with `a, b ≥ 0`. The two coordinates can be sorted, `b ≤ a`, without
changing the square. In the Cartesian coordinates of the frame of the phase the
square sits at `(a, ±b)`, the sign recording the reversal
(`SquareChart.cartesian`); points in a rotated frame and polar coordinates
connect the two descriptions.
-/

@[expose] public section

noncomputable section
open Set
namespace SquaresInCircles

lemma frame_angle (S : UnitSquare) :
    ∃ t : ℝ, Real.cos t=S.cosine ∧ Real.sin t=S.sine := by
  have h : ‖(⟨S.cosine,S.sine⟩ : ℂ)‖=1 := by
    rw [Complex.norm_def,Complex.normSq_mk,← sq,← sq,S.unit,Real.sqrt_one]
  exact ⟨_,by simpa [h] using Complex.norm_mul_cos_arg ⟨S.cosine,S.sine⟩,
    by simpa [h] using Complex.norm_mul_sin_arg ⟨S.cosine,S.sine⟩⟩

lemma local_circle_shift (S : UnitSquare) (o : Point) (r θ t m : ℝ)
    (hc : Real.cos θ=S.cosine) (hs : Real.sin θ=S.sine) :
    localX S (sub (circlePoint o r ((θ:Direction)+(t:Direction)))
      (scale m (sub S.center o))) = r*Real.cos t-(1+m)*frameX S (sub S.center o) ∧
    localY S (sub (circlePoint o r ((θ:Direction)+(t:Direction)))
      (scale m (sub S.center o))) = r*Real.sin t-(1+m)*frameY S (sub S.center o) := by
  simp only [localX,localY,circlePoint,sub,scale,frameX,frameY,Real.Angle.cos_add,
    Real.Angle.sin_add,Real.Angle.cos_coe,Real.Angle.sin_coe,hc,hs]
  constructor
  · linear_combination r*Real.cos t*S.unit
  · linear_combination r*Real.sin t*S.unit

def chartAngle (phase : Direction) (rev : Bool) (t : ℝ) : Direction :=
  phase+((if rev then -t else t : ℝ) : Direction)

/-- Seen from `o` along `chartAngle phase rev`, the square slid by `m` along
the ray through its centre is the axis-parallel square at `(1+m)(a,b)`. -/
abbrev ChartCondition (S : UnitSquare) (o : Point) (phase : Direction) (rev : Bool) (a b : ℝ) :
    Prop :=
  ∀ r t m, openSquare S
    (sub (circlePoint o r (chartAngle phase rev t)) (scale m (sub S.center o))) ↔
    |r*Real.cos t-(1+m)*a| < 1/2 ∧ |r*Real.sin t-(1+m)*b| < 1/2

structure SquareChart (S : UnitSquare) (o : Point) where
  a : ℝ
  b : ℝ
  phase : Direction
  reversed : Bool
  coordinates : (a=alpha S o ∧ b=beta S o) ∨ (a=beta S o ∧ b=alpha S o)
  shifted_membership : ChartCondition S o phase reversed a b

lemma SquareChart.membership {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (r t : ℝ) : openSquare S (circlePoint o r (chartAngle C.phase C.reversed t)) ↔
      |r*Real.cos t-C.a| < 1/2 ∧ |r*Real.sin t-C.b| < 1/2 := by
  simpa [sub,scale] using C.shifted_membership r t 0

lemma SquareChart.ray_mem {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {r t : ℝ} (h : ∃ m : ℝ, 0 ≤ m ∧
      |r*Real.cos t-(1+m)*C.a| < 1/2 ∧ |r*Real.sin t-(1+m)*C.b| < 1/2) :
    circlePoint o r (chartAngle C.phase C.reversed t) ∈ openRay S o := by
  obtain ⟨m,hm,hx,hy⟩ := h
  refine ⟨m,hm,_,(C.shifted_membership r t m).mpr ⟨hx,hy⟩,?_⟩
  apply Prod.ext <;> dsimp [add,sub,scale] <;> ring

/-- A fact about the absolute centre coordinates that is symmetric in them
holds for the chart's coordinates. -/
lemma SquareChart.transfer {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (P : ℝ → ℝ → Prop) (hsymm : ∀ {a b}, P a b → P b a)
    (h : P (alpha S o) (beta S o)) : P C.a C.b := by
  rcases C.coordinates with ⟨ha,hb⟩ | ⟨ha,hb⟩ <;> rw [ha,hb]
  · exact h
  · exact hsymm h

lemma chart_phi {S : UnitSquare} {o : Point} (C : SquareChart S o)
    {K : ℝ} (h : phi (alpha S o) (beta S o) ≤ K) : phi C.a C.b ≤ K :=
  C.transfer (fun a b => phi a b ≤ K) (fun h => by unfold phi at *; linarith) h

lemma SquareChart.nonneg {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    0 ≤ C.a ∧ 0 ≤ C.b :=
  C.transfer (fun a b => 0 ≤ a ∧ 0 ≤ b) (fun h => ⟨h.2,h.1⟩)
    ⟨alpha_nonneg S o,beta_nonneg S o⟩

section ChartCondition

variable {S : UnitSquare} {o : Point} {φ : Direction} {rev : Bool} {a b : ℝ}

/-- In the frame of its first axis a square satisfies the chart condition at
the coordinates of its centre. -/
lemma frame_chart (S : UnitSquare) (o : Point) {θ : ℝ} (hc : Real.cos θ=S.cosine)
    (hs : Real.sin θ=S.sine) :
    ChartCondition S o θ false (frameX S (sub S.center o)) (frameY S (sub S.center o)) :=
  fun r t m => by
    simp only [openSquare,chartAngle,Bool.false_eq_true,ite_false,
      (local_circle_shift S o r θ t m hc hs).1,(local_circle_shift S o r θ t m hc hs).2]

/-- Reversing the orientation changes the sign of `b`. -/
lemma ChartCondition.reflect (h : ChartCondition S o φ rev a b) :
    ChartCondition S o φ (!rev) a (-b) := by
  intro r t m
  have he : chartAngle φ (!rev) t=chartAngle φ rev (-t) := by cases rev <;> simp [chartAngle]
  rw [he,h,Real.cos_neg,Real.sin_neg,
    show r*(-Real.sin t)-(1+m)*b=-(r*Real.sin t-(1+m)*(-b)) by ring,abs_neg]

/-- A half turn of the phase changes the signs of both coordinates. -/
lemma ChartCondition.turn (h : ChartCondition S o φ rev a b) :
    ChartCondition S o (φ+(Real.pi:Direction)) rev (-a) (-b) := by
  intro r t m
  have he : chartAngle (φ+(Real.pi:Direction)) rev t=chartAngle φ rev (t+Real.pi) := by
    cases rev <;> simp only [chartAngle,Bool.false_eq_true,ite_false,ite_true,Real.Angle.coe_add,
      Real.Angle.coe_neg,neg_add,Real.Angle.neg_coe_pi] <;> abel
  rw [he,h,Real.cos_add_pi,Real.sin_add_pi,
    show r*(-Real.cos t)-(1+m)*a=-(r*Real.cos t-(1+m)*(-a)) by ring,
    show r*(-Real.sin t)-(1+m)*b=-(r*Real.sin t-(1+m)*(-b)) by ring,abs_neg,abs_neg]

/-- A quarter turn of the phase, with the orientation reversed, exchanges the
two coordinates. -/
lemma ChartCondition.swap (h : ChartCondition S o φ rev a b) :
    ChartCondition S o (chartAngle φ rev (Real.pi/2)) (!rev) b a := by
  intro r t m
  have he : chartAngle (chartAngle φ rev (Real.pi/2)) (!rev) t =
      chartAngle φ rev (Real.pi/2-t) := by
    cases rev <;> simp only [chartAngle,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      ite_false,ite_true,Real.Angle.coe_sub,Real.Angle.coe_neg] <;> abel
  rw [he,h,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub]
  exact and_comm

end ChartCondition

/-- In the frame of the first axis, a reflection, a half turn or both make the
two coordinates nonnegative. -/
lemma square_chart (S : UnitSquare) (o : Point) : Nonempty (SquareChart S o) := by
  obtain ⟨θ,hcos,hsin⟩ := frame_angle S
  have h := frame_chart S o hcos hsin
  obtain ⟨φ,rev,h'⟩ : ∃ φ rev, ChartCondition S o φ rev
      |frameX S (sub S.center o)| |frameY S (sub S.center o)| := by
    rcases le_or_gt 0 (frameX S (sub S.center o)) with hx | hx <;>
      rcases le_or_gt 0 (frameY S (sub S.center o)) with hy | hy
    · exact ⟨_,_,by rwa [abs_of_nonneg hx,abs_of_nonneg hy]⟩
    · exact ⟨_,_,by rw [abs_of_nonneg hx,abs_of_neg hy]; exact h.reflect⟩
    · exact ⟨_,_,by rw [abs_of_neg hx,abs_of_nonneg hy]; simpa using h.turn.reflect⟩
    · exact ⟨_,_,by rw [abs_of_neg hx,abs_of_neg hy]; exact h.turn⟩
  exact ⟨⟨_,_,φ,rev,Or.inl ⟨abs_frame_centerX S o,abs_frame_centerY S o⟩,h'⟩⟩

lemma sorted_square_chart (S : UnitSquare) (o : Point) :
    ∃ C : SquareChart S o, C.b ≤ C.a := by
  obtain ⟨C⟩ := square_chart S o
  rcases le_total C.b C.a with h | h
  · exact ⟨C,h⟩
  · exact ⟨⟨C.b,C.a,_,_,C.coordinates.symm.imp (fun h => ⟨h.2,h.1⟩) (fun h => ⟨h.2,h.1⟩),
      C.shifted_membership.swap⟩,h⟩

lemma SquareChart.origin {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    openSquare S o ↔ C.a < 1/2 ∧ C.b < 1/2 :=
  C.transfer (fun a b => openSquare S o ↔ a < 1/2 ∧ b < 1/2) (fun h => h.trans and_comm) Iff.rfl

lemma SquareChart.exterior {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (hsort : C.b ≤ C.a) (hout : ¬ openSquare S o) : 1/2 ≤ C.a := by
  by_contra hn
  exact hout (C.origin.mpr ⟨lt_of_not_ge hn,lt_of_le_of_lt hsort (lt_of_not_ge hn)⟩)

/-- Build an arc from a chart-parameter interval, with either orientation. -/
lemma arcFromChartInterval (o : Point) (r : ℝ) (U : Set Point)
    (phase : Direction) (rev : Bool) (l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u, circlePoint o r (chartAngle phase rev t) ∈ U) :
    ∃ A : OpenArc o r U,
      A.halfWidth=(u-l)/2 ∧ A.center=chartAngle phase rev ((l+u)/2) := by
  cases rev
  · exact ⟨arcOfInterval o r U phase l u hlu hlen
      (fun t ht => by simpa [chartAngle] using hmem t ht),rfl,by simp [arcOfInterval,chartAngle]⟩
  · refine ⟨arcOfInterval o r U phase (-u) (-l) (by linarith) (by linarith)
      (fun t ht => by
        have hm := hmem (-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
        simpa only [chartAngle,ite_true,neg_neg] using hm),
      by dsimp [arcOfInterval]; ring,?_⟩
    show phase+(((-u+-l)/2:ℝ):Direction)=chartAngle phase true ((l+u)/2)
    rw [show (-u+-l)/2=-((l+u)/2) by ring]
    simp only [chartAngle,ite_true]

/-- An arc of a square from an interval of its chart parameter. -/
lemma SquareChart.arc {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (r l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u,
      |r*Real.cos t-C.a| < 1/2 ∧ |r*Real.sin t-C.b| < 1/2) :
    ∃ A : OpenArc o r {p | openSquare S p},
      A.halfWidth=(u-l)/2 ∧ A.center=chartAngle C.phase C.reversed ((l+u)/2) :=
  arcFromChartInterval o r _ C.phase C.reversed l u hlu hlen
    (fun t ht => (C.membership r t).mpr (hmem t ht))

/-- A square with `a = 1/2` holds the half of a small circle about `o` on its
side of the near edge. -/
lemma SquareChart.half_arc {S : UnitSquare} {o : Point} (C : SquareChart S o) {r : ℝ}
    (hr : 0 < r) (ha : C.a=1/2) (hb : C.b+r ≤ 1/2) :
    ∃ A : OpenArc o r {p | openSquare S p}, A.halfWidth=Real.pi/2 ∧ A.center=C.phase := by
  obtain ⟨A,hA,hc⟩ := C.arc r (-(Real.pi/2)) (Real.pi/2) (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos]) fun t ht => by
      have hc := Real.cos_pos_of_mem_Ioo ht
      have hs := Real.sin_sq_add_cos_sq t
      have hs1 : Real.sin t < 1 := by nlinarith
      have hs2 : -1 < Real.sin t := by nlinarith
      have hb0 := C.nonneg.2
      rw [ha]
      exact ⟨abs_lt.mpr ⟨by nlinarith,by nlinarith [Real.cos_le_one t]⟩,
        abs_lt.mpr ⟨by nlinarith,by nlinarith⟩⟩
  exact ⟨A,by rw [hA]; ring,by rw [hc]; simp [chartAngle]⟩

lemma pointInDirection_polar (o : Point) (phase : Direction) (r t : ℝ) :
    pointInDirection o phase (r*Real.cos t) (r*Real.sin t) =
      circlePoint o r (phase+(t:Direction)) := by
  apply Prod.ext <;>
    simp only [pointInDirection,circlePoint,Real.Angle.cos_add,Real.Angle.sin_add,
      Real.Angle.cos_coe,Real.Angle.sin_coe] <;> ring

lemma pointInDirection_norm (o : Point) (phase : Direction) (x y : ℝ) :
    normSq (sub (pointInDirection o phase x y) o)=x^2+y^2 := by
  simp only [normSq,sub,pointInDirection]
  linear_combination (x^2+y^2)*Real.Angle.cos_sq_add_sin_sq phase

/-- Polar coordinates, from the polar form of the complex number `x + iy`. -/
lemma plane_polar (x y : ℝ) :
    ∃ r t : ℝ, r*Real.cos t=x ∧ r*Real.sin t=y :=
  ⟨_,_,Complex.norm_mul_cos_arg ⟨x,y⟩,Complex.norm_mul_sin_arg ⟨x,y⟩⟩

/-- Reversal of a chart changes only the sign of its transverse center coordinate. -/
def SquareChart.signedB {S : UnitSquare} {o : Point} (C : SquareChart S o) : ℝ :=
  if C.reversed then -C.b else C.b

/-- Without the reversal, a chart holds at `(a, signedB)`. -/
lemma SquareChart.unreversed {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    ChartCondition S o C.phase false C.a C.signedB := by
  unfold SquareChart.signedB
  cases h : C.reversed
  · simpa [h] using C.shifted_membership
  · simpa [h] using C.shifted_membership.reflect

lemma SquareChart.cartesian {S : UnitSquare} {o : Point} (C : SquareChart S o)
    (x y : ℝ) :
    openSquare S (pointInDirection o C.phase x y) ↔
      |x-C.a| < 1/2 ∧ |y-C.signedB| < 1/2 := by
  obtain ⟨r,t,rfl,rfl⟩ := plane_polar x y
  rw [pointInDirection_polar]
  simpa [sub,scale,chartAngle] using C.unreversed r t 0

lemma pointInDirection_transition (o : Point) (φ ψ : Direction) (x y : ℝ) :
    pointInDirection o φ x y = pointInDirection o ψ
      ((ψ-φ).cos*x+(ψ-φ).sin*y)
      (-(ψ-φ).sin*x+(ψ-φ).cos*y) := by
  obtain ⟨δ,rfl⟩ : ∃ δ, φ=ψ-δ := ⟨ψ-φ,by abel⟩
  rw [sub_sub_cancel]
  simp only [pointInDirection,sub_eq_add_neg,Real.Angle.cos_add,Real.Angle.sin_add,
    Real.Angle.cos_neg,Real.Angle.sin_neg]
  apply Prod.ext <;> ring

end SquaresInCircles
