module

public import SquaresInCircles.Common.Contacts
public import SquaresInCircles.Common.Angles
public import SquaresInCircles.Common.Trigonometry

/-!
# The separating-axis theorem

Strict overlap on the two edge axes of each of two squares implies overlap
along every normal. With `support_separator`, disjoint squares are separated
along one of their four edge axes (`SAT.separating_axes`). For two oriented
squares, the second turned by `d` from the first, the threshold is
`1/2 + angularWidth d` and the offset of the centres has explicit coordinates
in either frame (`oriented_separating_axes`).
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles.SAT

def axisInside (c s : ℝ) (d : Point) : Prop :=
  let H := (1+c+s)/2
  |d.1| < H ∧ |d.2| < H ∧ |c*d.1+s*d.2| < H ∧ |-s*d.1+c*d.2| < H

def octagonSupport (c s : ℝ) (n : Point) : ℝ :=
  (|n.1|+|n.2|+|c*n.1+s*n.2|+|-s*n.1+c*n.2|)/2

lemma octagon_first_quadrant {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) (d n : Point) (hd : axisInside c s d)
    (hx : 0 ≤ n.1) (hy : 0 ≤ n.2) (hn : 0 < n.1+n.2) :
    dot n d < octagonSupport c s n := by
  have hxD := (abs_lt.mp hd.1).2
  have hyD := (abs_lt.mp hd.2.1).2
  have hpD := (abs_lt.mp hd.2.2.1).2
  have hp : 0 ≤ c*n.1+s*n.2 := by positivity
  by_cases hs0 : s=0
  · have hc1 : c=1 := by nlinarith
    subst s; subst c
    have hh := weighted_strict hx hy hn hxD hyD
    simp only [dot,octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,one_mul,zero_mul,
      add_zero,zero_add,neg_zero] at hh ⊢
    linarith
  · have hsp : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    by_cases hw : -s*n.1+c*n.2 ≤ 0
    · let a := s*n.1-c*n.2
      have ha : 0 ≤ a := by dsimp [a]; linarith
      have hab : 0 < a+n.2 := by
        by_contra hh
        have hny : n.2=0 := by linarith
        have hnx : 0 < n.1 := by linarith
        have hh' := mul_pos hsp hnx
        dsimp [a] at *
        nlinarith
      have hlt := weighted_strict ha hy hab hxD hpD
      have he₁ : a*d.1+n.2*(c*d.1+s*d.2) = s*dot n d := by
        dsimp [a,dot]; ring
      have he₂ : (1+c+s)/2*(a+n.2) = s*octagonSupport c s n := by
        simp only [octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,
          abs_of_nonneg hp,abs_of_nonpos hw]
        dsimp [a]
        linear_combination -(n.2/2)*hunit
      rw [he₁,he₂] at hlt
      exact lt_of_mul_lt_mul_left hlt hsp.le
    · have hw0 : 0 ≤ -s*n.1+c*n.2 := le_of_lt (lt_of_not_ge hw)
      let b := c*n.2-s*n.1
      have hb : 0 ≤ b := by dsimp [b]; linarith
      have hab : 0 < n.1+b := by
        by_contra hh
        have hnx : n.1=0 := by linarith
        have hny : 0 < n.2 := by linarith
        have hh' := mul_pos hc hny
        dsimp [b] at *
        linarith
      have hlt := weighted_strict hx hb hab hpD hyD
      have he₁ : n.1*(c*d.1+s*d.2)+b*d.2 = c*dot n d := by
        dsimp [b,dot]; ring
      have he₂ : (1+c+s)/2*(n.1+b) = c*octagonSupport c s n := by
        simp only [octagonSupport,abs_of_nonneg hx,abs_of_nonneg hy,
          abs_of_nonneg hp,abs_of_nonneg hw0]
        dsimp [b]
        linear_combination -(n.1/2)*hunit
      rw [he₁,he₂] at hlt
      exact lt_of_mul_lt_mul_left hlt hc.le

/-- A quarter turn of both `n` and `d` keeps the octagon, its support function
and the pairing of `n` with `d`. -/
lemma turnPoint_facts (k : Fin 4) (c s : ℝ) (n d : Point) :
    (axisInside c s d → axisInside c s (turnPoint k d)) ∧
    octagonSupport c s (turnPoint k n) = octagonSupport c s n ∧
    dot (turnPoint k n) (turnPoint k d) = dot n d ∧
    normSq (turnPoint k n) = normSq n := by
  have h₁ (x y : ℝ) : |c*(-y)+s*x| = |-s*x+c*y| := by rw [← abs_neg]; ring_nf
  have h₂ (x y : ℝ) : |-s*(-y)+c*x| = |c*x+s*y| := by ring_nf
  have h₃ (x y : ℝ) : |c*y+s*(-x)| = |-s*x+c*y| := by ring_nf
  have h₄ (x y : ℝ) : |-s*y+c*(-x)| = |c*x+s*y| := by rw [← abs_neg]; ring_nf
  fin_cases k <;> simp only [turnPoint,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Matrix.cons_val,
    axisInside,octagonSupport,dot,normSq,abs_neg,h₁,h₂,h₃,h₄] <;>
    refine ⟨fun h => ?_,?_,?_,?_⟩ <;> first | trivial | ring1 | tauto

lemma octagon_strict {c s : ℝ} (hc : 0 < c) (hs : 0 ≤ s)
    (hunit : c^2+s^2=1) {d n : Point} (hd : axisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  obtain ⟨k,hx,hy⟩ := quarter_nonnegative n
  obtain ⟨hk,hsup,hdot,hnorm⟩ := turnPoint_facts k c s n d
  have hpos : 0 < (turnPoint k n).1+(turnPoint k n).2 := by
    have h := normSq_pos_of_ne hn
    rw [← hnorm,normSq] at h
    by_contra hh
    nlinarith
  rw [← hsup,← hdot]
  exact octagon_first_quadrant hc hs hunit _ _ (hk hd) hx hy hpos

def AxisInside (c s : ℝ) (d : Point) : Prop :=
  let H := (1+|c|+|s|)/2
  |d.1| < H ∧ |d.2| < H ∧ |c*d.1+s*d.2| < H ∧ |-s*d.1+c*d.2| < H

def reflect (p : Point) : Point := (p.1,-p.2)

lemma axis_neg_frame {c s : ℝ} {d : Point} (hd : AxisInside c s d) :
    AxisInside (-c) (-s) d := by
  have h1 : (-c)*d.1+(-s)*d.2 = -(c*d.1+s*d.2) := by ring
  have h2 : -(-s)*d.1+(-c)*d.2 = -(-s*d.1+c*d.2) := by ring
  simpa only [AxisInside,abs_neg,h1,h2] using hd

lemma support_neg_frame (c s : ℝ) (n : Point) :
    octagonSupport (-c) (-s) n = octagonSupport c s n := by
  have h1 : (-c)*n.1+(-s)*n.2 = -(c*n.1+s*n.2) := by ring
  have h2 : -(-s)*n.1+(-c)*n.2 = -(-s*n.1+c*n.2) := by ring
  simp only [octagonSupport,h1,h2,abs_neg]

lemma axis_reflect {c s : ℝ} {d : Point} (hd : AxisInside c s d) :
    AxisInside c (-s) (reflect d) := by
  have h1 : c*d.1+(-s)*(-d.2) = c*d.1+s*d.2 := by ring
  have h2 : -(-s)*d.1+c*(-d.2) = -(-s*d.1+c*d.2) := by ring
  simpa only [AxisInside,reflect,abs_neg,h1,h2] using hd

lemma support_reflect (c s : ℝ) (n : Point) :
    octagonSupport c (-s) (reflect n) = octagonSupport c s n := by
  have h1 : c*n.1+(-s)*(-n.2) = c*n.1+s*n.2 := by ring
  have h2 : -(-s)*n.1+c*(-n.2) = -(-s*n.1+c*n.2) := by ring
  simp only [octagonSupport,reflect,h1,h2,abs_neg]

lemma reflect_dot (n d : Point) : dot (reflect n) (reflect d) = dot n d := by
  dsimp [reflect,dot]
  ring

lemma reflect_ne {n : Point} (hn : n ≠ (0,0)) : reflect n ≠ (0,0) := by
  intro he
  apply hn
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext <;> dsimp [reflect] at * <;> linarith

lemma positive_cosine_strict {c s : ℝ} (hc : 0 < c) (hu : c^2+s^2=1)
    {d n : Point} (hd : AxisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  by_cases hs : 0 ≤ s
  · have hi : axisInside c s d := by
      simpa only [AxisInside,axisInside,abs_of_pos hc,abs_of_nonneg hs] using hd
    exact octagon_strict hc hs hu hi hn
  · have hs' : 0 ≤ -s := by linarith
    have hi := axis_reflect hd
    have hi' : axisInside c (-s) (reflect d) := by
      simpa only [AxisInside,axisInside,abs_of_pos hc,abs_of_nonneg hs'] using hi
    have hh := octagon_strict hc hs' (by linear_combination hu) hi' (reflect_ne hn)
    rw [reflect_dot,support_reflect] at hh
    exact hh

lemma zero_cosine_strict {s : ℝ} (hu : s^2=1)
    {d n : Point} (hd : AxisInside 0 s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport 0 s n := by
  have habs : |s|=1 := by nlinarith [sq_abs s,abs_nonneg s]
  have hdx : |d.1| < 1 := by simpa [AxisInside,abs_zero,habs] using hd.1
  have hdy : |d.2| < 1 := by simpa [AxisInside,abs_zero,habs] using hd.2.1
  have hsum : 0 < |n.1|+|n.2| := by
    by_contra he
    apply hn
    have hnx : n.1=0 := abs_eq_zero.mp (by linarith [abs_nonneg n.1,abs_nonneg n.2])
    have hny : n.2=0 := abs_eq_zero.mp (by linarith [abs_nonneg n.1,abs_nonneg n.2])
    exact Prod.ext hnx hny
  have hh := weighted_strict (abs_nonneg n.1) (abs_nonneg n.2) hsum hdx hdy
  have hx : n.1*d.1 ≤ |n.1| * |d.1| := by simpa only [abs_mul] using le_abs_self (n.1*d.1)
  have hy : n.2*d.2 ≤ |n.2| * |d.2| := by simpa only [abs_mul] using le_abs_self (n.2*d.2)
  have he : octagonSupport 0 s n = |n.1|+|n.2| := by
    simp only [octagonSupport,zero_mul,zero_add,add_zero,abs_mul,abs_neg,habs,one_mul]
    ring
  rw [he]
  dsimp [dot]
  linarith

/-- Strict overlap on all four edge axes implies overlap on every normal. -/
theorem all_normals_strict {c s : ℝ} (hu : c^2+s^2=1)
    {d n : Point} (hd : AxisInside c s d) (hn : n ≠ (0,0)) :
    dot n d < octagonSupport c s n := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have hi := axis_neg_frame hd
    have hh := positive_cosine_strict (show 0 < -c by linarith)
      (show (-c)^2+(-s)^2=1 by linear_combination hu) hi hn
    rw [support_neg_frame] at hh
    exact hh
  · subst c
    exact zero_cosine_strict (by linear_combination hu) hd hn
  · exact positive_cosine_strict hc hu hd hn

def threshold (S T : UnitSquare) : ℝ := (1+|relativeC S T|+|relativeS S T|)/2

/-- Ordinary non-overlap implies one of the four unsigned separating axes. -/
theorem separating_axes (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    threshold S T ≤ |frameX S (sub T.center S.center)| ∨
    threshold S T ≤ |frameY S (sub T.center S.center)| ∨
    threshold S T ≤ |frameX T (sub T.center S.center)| ∨
    threshold S T ≤ |frameY T (sub T.center S.center)| := by
  obtain ⟨e⟩ := support_separator S T hd
  let d : Point := (frameX S (sub T.center S.center),frameY S (sub T.center S.center))
  let n : Point := (frameX S e.normal,frameY S e.normal)
  have hn : n ≠ (0,0) := by
    intro he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    have hu := frame_norm S e.normal
    dsimp [n] at hx hy
    rw [hx,hy] at hu
    apply e.nonzero
    apply Prod.ext <;> dsimp [normSq] at hu ⊢ <;>
      nlinarith [sq_nonneg e.normal.1,sq_nonneg e.normal.2]
  by_contra hnot
  push Not at hnot
  have hi : AxisInside (relativeC S T) (relativeS S T) d := by
    dsimp [AxisInside,d]
    rw [← (relative_normal S T _).1,← (relative_normal S T _).2]
    exact hnot
  have hlt := all_normals_strict (relative_unit S T) hi hn
  have hdot : dot n d = dot e.normal (sub T.center S.center) := by
    exact frame_dot S _ _
  have hsup : octagonSupport (relativeC S T) (relativeS S T) n =
      width S e.normal+width T e.normal := by
    dsimp [octagonSupport,n]
    rw [← (relative_normal S T _).1,← (relative_normal S T _).2]
    dsimp [width]
    ring
  rw [hdot,hsup] at hlt
  exact (not_lt_of_ge e.separates) hlt

end SquaresInCircles.SAT

namespace SquaresInCircles

/-! ### Two oriented squares -/

/-- `(|cos t| + |sin t|)/2`, the half-width along a coordinate axis of a unit
square at angle `t`. -/
def angularWidth (t : ℝ) : ℝ := (|Real.cos t|+|Real.sin t|)/2

/-- The half-width of a square at an angle in `[0, π/2]`. -/
lemma angularWidth_eq {x : ℝ} (hx : 0 ≤ x ∧ x ≤ Real.pi/2) :
    angularWidth x=(Real.cos x+Real.sin x)/2 := by
  obtain ⟨hc,hs⟩ := cos_sin_nonneg hx
  simp only [angularWidth,abs_of_nonneg hc,abs_of_nonneg hs]

lemma angularWidth_neg (t : ℝ) : angularWidth (-t)=angularWidth t := by
  simp [angularWidth,Real.cos_neg,Real.sin_neg,abs_neg]

lemma angularWidth_pi_add (t : ℝ) : angularWidth (Real.pi+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg]

lemma angularWidth_half_pi_add (t : ℝ) : angularWidth (Real.pi/2+t)=angularWidth t := by
  simp [angularWidth,Real.cos_add,Real.sin_add,abs_neg,add_comm]

lemma angularWidth_half_pi_sub (t : ℝ) : angularWidth (Real.pi/2-t)=angularWidth t := by
  simp [angularWidth,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,add_comm]

lemma angularWidth_three_half_pi_add (t : ℝ) :
    angularWidth (3*Real.pi/2+t)=angularWidth t := by
  rw [show 3*Real.pi/2+t=Real.pi+(Real.pi/2+t) by ring,angularWidth_pi_add,
    angularWidth_half_pi_add]

/-- The half-width is at least the mean of `cos t` and `sin t`. -/
lemma angularWidth_lower (t : ℝ) : (Real.cos t+Real.sin t)/2 ≤ angularWidth t := by
  dsimp [angularWidth]
  linarith [le_abs_self (Real.cos t),le_abs_self (Real.sin t)]

lemma oriented_x_width (t a b : ℝ) : width (orientedSquare t a b) (1,0)=angularWidth t := by
  simp [width,frameX,frameY,orientedSquare,angularWidth,abs_neg]

lemma oriented_y_width (t a b : ℝ) : width (orientedSquare t a b) (0,1)=angularWidth t := by
  simp [width,frameX,frameY,orientedSquare,angularWidth,add_comm]

/-- Each coordinate of a point of the closed square is within `angularWidth t`
of that of the centre. -/
lemma closed_center_coordinate_bounds {t a b : ℝ} {p : Point}
    (hp : closedSquare (orientedSquare t a b) p) :
    (centerX t a b-angularWidth t ≤ p.1 ∧ p.1 ≤ centerX t a b+angularWidth t) ∧
    (centerY t a b-angularWidth t ≤ p.2 ∧ p.2 ≤ centerY t a b+angularWidth t) := by
  have hx := abs_le.mp (closed_dot_bound (orientedSquare t a b) (1,0) hp)
  have hy := abs_le.mp (closed_dot_bound (orientedSquare t a b) (0,1) hp)
  rw [oriented_x_width] at hx
  rw [oriented_y_width] at hy
  simp only [dot,sub,orientedSquare,one_mul,zero_mul,add_zero,zero_add] at hx hy
  exact ⟨⟨by dsimp [centerX]; linarith,by dsimp [centerX]; linarith⟩,
    ⟨by dsimp [centerY]; linarith,by dsimp [centerY]; linarith⟩⟩

lemma oriented_relativeC (t a b T A B : ℝ) :
    relativeC (orientedSquare t a b) (orientedSquare T A B)=Real.cos (T-t) := by
  simp only [relativeC,orientedSquare,Real.cos_sub]
  ring

lemma oriented_relativeS (t a b T A B : ℝ) :
    relativeS (orientedSquare t a b) (orientedSquare T A B)=Real.sin (T-t) := by
  simp only [relativeS,orientedSquare,Real.sin_sub]
  ring

/-- The threshold of two oriented squares, the second turned by `T - t` from the
first. -/
lemma oriented_pair_threshold (t a b T A B : ℝ) :
    SAT.threshold (orientedSquare t a b) (orientedSquare T A B)=1/2+angularWidth (T-t) := by
  rw [SAT.threshold,oriented_relativeC,oriented_relativeS]
  dsimp [angularWidth]
  ring

/-- The offset of the centres in the frame of the first square. -/
lemma pair_frameX_left (t a b T A B : ℝ) :
    frameX (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)=
      A*Real.cos (T-t)-B*Real.sin (T-t)-a := by
  dsimp [frameX,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination -a*(Real.sin_sq_add_cos_sq t)

lemma pair_frameY_left (t a b T A B : ℝ) :
    frameY (orientedSquare t a b)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)=
      A*Real.sin (T-t)+B*Real.cos (T-t)-b := by
  dsimp [frameY,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination -b*(Real.sin_sq_add_cos_sq t)

/-- The offset of the centres in the frame of the second square. -/
lemma pair_frameX_right (t a b T A B : ℝ) :
    frameX (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)=
      A-a*Real.cos (T-t)-b*Real.sin (T-t) := by
  dsimp [frameX,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination A*(Real.sin_sq_add_cos_sq T)

lemma pair_frameY_right (t a b T A B : ℝ) :
    frameY (orientedSquare T A B)
      (sub (orientedSquare T A B).center (orientedSquare t a b).center)=
      B+a*Real.sin (T-t)-b*Real.cos (T-t) := by
  dsimp [frameY,orientedSquare,sub]
  rw [Real.cos_sub,Real.sin_sub]
  linear_combination B*(Real.sin_sq_add_cos_sq T)

/-- Two oriented squares with disjoint interiors, the second turned by
`d = T - t` from the first, are separated along an axis of one of them: in the
frame of the first square or of the second, a coordinate of the offset of the
centres reaches the threshold `1/2 + angularWidth d` in absolute value. -/
theorem oriented_separating_axes {t a b T A B : ℝ}
    (hd : ∀ p, ¬ (openSquare (orientedSquare t a b) p ∧ openSquare (orientedSquare T A B) p)) :
    1/2+angularWidth (T-t) ≤ |A*Real.cos (T-t)-B*Real.sin (T-t)-a| ∨
    1/2+angularWidth (T-t) ≤ |A*Real.sin (T-t)+B*Real.cos (T-t)-b| ∨
    1/2+angularWidth (T-t) ≤ |A-a*Real.cos (T-t)-b*Real.sin (T-t)| ∨
    1/2+angularWidth (T-t) ≤ |B+a*Real.sin (T-t)-b*Real.cos (T-t)| := by
  simpa only [oriented_pair_threshold,pair_frameX_left,pair_frameY_left,pair_frameX_right,
    pair_frameY_right] using SAT.separating_axes _ _ hd

end SquaresInCircles
