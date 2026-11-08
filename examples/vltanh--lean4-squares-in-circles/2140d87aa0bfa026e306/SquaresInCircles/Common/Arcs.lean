module

public import SquaresInCircles.Common.Separation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Arcs and the angular budget

Directions are `Real.Angle = AddCircle (2π)`, whose Haar measure has total mass
`2π`; a closed metric ball of radius `w ≤ π` has mass `2w`. An `OpenArc` is an
arc of a circle about the disk centre that lies in a planar region. Arcs in
pairwise disjoint regions have half-widths of total at most `π`: shrink every
arc by the same factor below 1 and measure the closed arcs
(`open_arc_budget`). The centres of two such arcs are at least the sum of their
half-widths apart (`OpenArc.centers_separated`), and three directions have
perimeter at most `2π`, which bounds the third distance of three arcs.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
open Set
namespace SquaresInCircles

local instance : Fact (0 < (2*Real.pi : ℝ)) := ⟨by positivity⟩

def circlePoint (o : Point) (r : ℝ) (θ : Direction) : Point :=
  (o.1+r*θ.cos, o.2+r*θ.sin)

lemma direction_norm (θ : Direction) : ‖θ‖ = |θ.toReal| := by
  conv_lhs => rw [← Real.Angle.coe_toReal θ]
  apply (AddCircle.norm_coe_eq_abs_iff (2*Real.pi) (by positivity)).2
  simpa only [abs_of_pos (show 0 < 2*Real.pi by positivity), mul_div_cancel_left₀ _
    (show (2:ℝ) ≠ 0 by norm_num)] using θ.abs_toReal_le_pi

lemma direction_dist (θ φ : Direction) : dist θ φ = |(θ-φ).toReal| := by
  rw [dist_eq_norm,direction_norm]

lemma direction_offset (θ φ : Direction) : θ = φ+((θ-φ).toReal : Direction) := by
  rw [Real.Angle.coe_toReal]
  abel

/-- A certified open angular interval contained in an actual planar region. -/
structure OpenArc (o : Point) (r : ℝ) (U : Set Point) where
  center : Direction
  halfWidth : ℝ
  positive : 0 < halfWidth
  atMostPi : halfWidth ≤ Real.pi
  inside : ∀ θ, dist θ center < halfWidth → circlePoint o r θ ∈ U

/-- The measure-theoretic core, independent of squares and their orientations.
It is stated on `AddCircle (2*pi)`, which carries the Haar measure; `Direction`
is definitionally the same circle with the same metric. -/
theorem closed_arc_budget {n : ℕ} (c : Fin n → AddCircle (2*Real.pi)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ Real.pi)
    (hd : Pairwise (fun i j => Disjoint
      (Metric.closedBall (c i) (w i)) (Metric.closedBall (c j) (w j)))) :
    ∑ i, w i ≤ Real.pi := by
  have hmu := sum_measure_le_measure_univ (μ := (volume : Measure (AddCircle (2*Real.pi))))
    (s := Finset.univ) (fun i _ => measurableSet_closedBall.nullMeasurableSet)
    (fun i _ j _ hij => (hd hij).aedisjoint)
  have hvol (i : Fin n) : volume (Metric.closedBall (c i) (w i))=ENNReal.ofReal (2*w i) := by
    rw [AddCircle.volume_closedBall,min_eq_right (by linarith [(hw i).2])]
  simp only [hvol,AddCircle.measure_univ] at hmu
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by linarith [(hw i).1]),
    ENNReal.ofReal_le_ofReal_iff (by positivity),← Finset.mul_sum] at hmu
  linarith

/-- The same budget for open arc witnesses, without boundary-measure assumptions:
shrink every arc by the same factor `t < 1` and close it. -/
theorem open_arc_budget {n : ℕ} {o : Point} {r : ℝ} {U : Fin n → Set Point}
    (A : ∀ i, OpenArc o r (U i)) (hd : Pairwise (fun i j => Disjoint (U i) (U j))) :
    ∑ i, (A i).halfWidth ≤ Real.pi := by
  refine bound_from_shrinks fun t ht0 ht1 => ?_
  have hw (i : Fin n) : t*(A i).halfWidth < (A i).halfWidth :=
    mul_lt_of_lt_one_left (A i).positive ht1
  rw [Finset.mul_sum]
  exact closed_arc_budget (fun i => (A i).center) _
    (fun i => ⟨mul_nonneg ht0 (A i).positive.le,(hw i).le.trans (A i).atMostPi⟩)
    fun i j hij => Set.disjoint_left.mpr fun θ hi hj => Set.disjoint_left.mp (hd hij)
      ((A i).inside θ (lt_of_le_of_lt hi (hw i))) ((A j).inside θ (lt_of_le_of_lt hj (hw j)))

/-- Arcs of half-width at least `π/n` on one circle, one of them more, cannot
belong to `n` disjoint sets. -/
theorem uniform_arc_excess {n : ℕ} {o : Point} {r : ℝ}
    {U : Fin n → Set Point} (A : ∀ i, OpenArc o r (U i))
    (hd : Pairwise (fun i j => Disjoint (U i) (U j)))
    (hle : ∀ i, Real.pi/n ≤ (A i).halfWidth)
    (hlt : ∃ i, Real.pi/n < (A i).halfWidth) : False := by
  obtain ⟨i,hi⟩ := hlt
  have hsum := Finset.sum_lt_sum (s := Finset.univ) (fun j _ => hle j) ⟨i,Finset.mem_univ _,hi⟩
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast i.pos.ne'
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_div_cancel₀ _ hn] at hsum
  exact (open_arc_budget A hd).not_gt hsum

/-- Convert a real parameter interval to an arc on the quotient circle.
The hypotheses contain *strict* planar membership throughout the interval. -/
def arcOfInterval (o : Point) (r : ℝ) (U : Set Point) (phase : Direction)
    (l u : ℝ) (hlu : l < u) (hlen : u-l ≤ 2*Real.pi)
    (hmem : ∀ t ∈ Ioo l u, circlePoint o r (phase+(t:Direction)) ∈ U) :
    OpenArc o r U where
  center := phase+(((l+u)/2 : ℝ) : Direction)
  halfWidth := (u-l)/2
  positive := by linarith
  atMostPi := by linarith
  inside := by
    intro θ hθ
    let s : ℝ := (θ-(phase+(((l+u)/2 : ℝ) : Direction))).toReal
    have hs : |s| < (u-l)/2 := by simpa only [direction_dist] using hθ
    have ht : (l+u)/2+s ∈ Ioo l u := by
      rcases abs_lt.mp hs with ⟨hs₀,hs₁⟩
      exact ⟨by linarith,by linarith⟩
    have he : θ=phase+(((l+u)/2+s : ℝ) : Direction) := by
      rw [Real.Angle.coe_add]
      have hh := direction_offset θ (phase+(((l+u)/2 : ℝ) : Direction))
      simpa only [add_assoc] using hh
    rw [he]
    exact hmem _ ht

lemma direction_coe_norm_le (t : ℝ) : ‖(t : Direction)‖ ≤ |t| := by
  have h := QuotientAddGroup.norm_mk_le_norm
    (S := AddSubgroup.zmultiples (2 * Real.pi)) (m := t)
  rw [Real.norm_eq_abs] at h
  exact h

lemma direction_diameter (a b : Direction) : dist a b ≤ Real.pi := by
  rw [direction_dist]
  exact (a-b).abs_toReal_le_pi

/-- Disjoint arcs have centres at least the sum of their half-widths apart:
otherwise the direction dividing the way between the centres in the ratio of
the half-widths lies in both arcs. -/
lemma OpenArc.centers_separated {o : Point} {r : ℝ} {U V : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (hUV : Disjoint U V) :
    A.halfWidth+B.halfWidth ≤ dist A.center B.center := by
  by_contra hn
  push Not at hn
  set d := (B.center-A.center).toReal
  have hd : |d| < A.halfWidth+B.halfWidth := by rwa [dist_comm,direction_dist] at hn
  have hH := add_pos A.positive B.positive
  set s := A.halfWidth/(A.halfWidth+B.halfWidth)
  have hs : 0 < s := div_pos A.positive hH
  have hsA : s*(A.halfWidth+B.halfWidth)=A.halfWidth := div_mul_cancel₀ _ hH.ne'
  have hB : A.center+((s*d:ℝ):Direction)-B.center=(((s-1)*d:ℝ):Direction) := by
    rw [show B.center=A.center+(d:Direction) from direction_offset _ _,sub_mul,one_mul,
      Real.Angle.coe_sub]
    abel
  refine Set.disjoint_left.mp hUV (A.inside (A.center+((s*d:ℝ):Direction)) ?_) (B.inside _ ?_)
  · rw [dist_eq_norm,add_sub_cancel_left]
    refine (direction_coe_norm_le _).trans_lt ?_
    rw [abs_mul,abs_of_pos hs]
    nlinarith
  · rw [dist_eq_norm,hB]
    refine (direction_coe_norm_le _).trans_lt ?_
    rw [abs_mul,abs_of_neg (by nlinarith [B.positive])]
    nlinarith [B.positive]

lemma direction_norm_wrapped {t : ℝ} (ht : |t| ≤ 2*Real.pi) :
    ‖(t:Direction)‖ ≤ 2*Real.pi-|t| := by
  rcases le_total 0 t with hs | hs
  · have he : ((t-2*Real.pi:ℝ):Direction)=(t:Direction) := by simp
    have hh := direction_coe_norm_le (t-2*Real.pi)
    rw [he,abs_of_nonpos (by rw [abs_of_nonneg hs] at ht; linarith)] at hh
    rw [abs_of_nonneg hs]
    linarith
  · have he : ((t+2*Real.pi:ℝ):Direction)=(t:Direction) := by simp
    have hh := direction_coe_norm_le (t+2*Real.pi)
    rw [he,abs_of_nonneg (by rw [abs_of_nonpos hs] at ht; linarith)] at hh
    rw [abs_of_nonpos hs]
    linarith

/-- Three geodesic distances on a circle of circumference `2*pi` sum to at most `2*pi`. -/
lemma direction_triangle_perimeter (x y z : Direction) :
    dist x y + dist y z + dist z x ≤ 2*Real.pi := by
  let a := (x-z).toReal
  let b := (y-z).toReal
  have ha : |a| ≤ Real.pi := (x-z).abs_toReal_le_pi
  have hb : |b| ≤ Real.pi := (y-z).abs_toReal_le_pi
  have hx : x=z+(a:Direction) := direction_offset _ _
  have hy : y=z+(b:Direction) := direction_offset _ _
  have he : x-y=((a-b:ℝ):Direction) := by
    rw [hx,hy,Real.Angle.coe_sub]; abel
  have hd : dist x y ≤ |a-b| := by
    rw [dist_eq_norm,he]; exact direction_coe_norm_le _
  have hd' : dist x y ≤ 2*Real.pi-|a-b| := by
    rw [dist_eq_norm,he]
    apply direction_norm_wrapped
    exact (abs_sub a b).trans (by linarith)
  have hxz : dist z x=|a| := by rw [dist_comm,direction_dist]
  have hyz : dist y z=|b| := by rw [direction_dist]
  rw [hxz,hyz]
  rcases le_total a 0 with ha0 | ha0 <;>
    rcases le_total b 0 with hb0 | hb0 <;>
    rcases le_total (a-b) 0 with hab | hab <;>
    simp_all only [abs_of_nonneg,abs_of_nonpos] <;> linarith

/-- Bounds for the third separation supplied by three disjoint arc witnesses. -/
lemma OpenArc.third_distance_bounds {o : Point} {r : ℝ} {U V W : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (C : OpenArc o r W)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    B.halfWidth+C.halfWidth ≤ dist B.center C.center ∧
      dist B.center C.center ≤
        2*Real.pi-2*A.halfWidth-B.halfWidth-C.halfWidth := by
  refine ⟨B.centers_separated C hVW,?_⟩
  have hab := A.centers_separated B hUV
  have hac := A.centers_separated C hUW
  have hp := direction_triangle_perimeter B.center C.center A.center
  rw [dist_comm C.center A.center] at hp
  linarith

lemma triple_arc_budget {o : Point} {r : ℝ} {U V W : Set Point}
    (A : OpenArc o r U) (B : OpenArc o r V) (C : OpenArc o r W)
    (hUV : Disjoint U V) (hUW : Disjoint U W) (hVW : Disjoint V W) :
    A.halfWidth+B.halfWidth+C.halfWidth ≤ Real.pi := by
  have h := A.third_distance_bounds B C hUV hUW hVW
  linarith [h.1,h.2]

lemma cos_sub_distance (φ ψ : Direction) : (ψ-φ).cos=Real.cos (dist φ ψ) := by
  have h := congrArg Real.Angle.cos (Real.Angle.coe_toReal (ψ-φ))
  rw [Real.Angle.cos_coe] at h
  rw [dist_comm,direction_dist,Real.cos_abs]
  exact h.symm

lemma cos_two_pi_thirds : Real.cos (2*Real.pi/3)= -(1/2:ℝ) := by
  rw [show 2*Real.pi/3=2*(Real.pi/3) by ring,Real.cos_two_mul,Real.cos_pi_div_three]
  norm_num

end SquaresInCircles
