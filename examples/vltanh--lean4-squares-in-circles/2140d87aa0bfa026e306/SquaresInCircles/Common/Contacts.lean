module

public import SquaresInCircles.Common.Congruence

/-!
# Contacts

Centres of interior-disjoint unit squares are at least 1 apart, and at distance
exactly 1 the squares are side-neighbours, by the supporting functional of
`support_separator`. Squares with parallel sides read in one frame; squares with
the same centre and the same axes are the same square.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

def relativeC (S T : UnitSquare) : ℝ := S.cosine*T.cosine+S.sine*T.sine
def relativeS (S T : UnitSquare) : ℝ := -S.sine*T.cosine+S.cosine*T.sine

def SameAxes (S T : UnitSquare) : Prop := relativeC S T=0 ∨ relativeS S T=0

lemma relative_unit (S T : UnitSquare) : (relativeC S T)^2+(relativeS S T)^2=1 := by
  simp only [relativeC,relativeS]
  linear_combination (T.cosine^2+T.sine^2)*S.unit+T.unit

lemma relative_normal (S T : UnitSquare) (n : Point) :
    frameX T n=relativeC S T*frameX S n+relativeS S T*frameY S n ∧
    frameY T n= -relativeS S T*frameX S n+relativeC S T*frameY S n := by
  simp only [frameX,frameY,relativeC,relativeS]
  constructor
  · linear_combination (-(T.cosine*n.1+T.sine*n.2))*S.unit
  · linear_combination (-(-T.sine*n.1+T.cosine*n.2))*S.unit

/-- Two squares that both have a side along the same nonzero vector have the
same axes. -/
lemma same_axes_from_normal (S T : UnitSquare) {n : Point} (hn : n ≠ (0,0))
    (hS : frameX S n*frameY S n=0) (hT : frameX T n*frameY T n=0) : SameAxes S T := by
  obtain ⟨hx,hy⟩ := relative_normal S T n
  have hpos := normSq_pos_of_ne hn
  rw [← frame_norm S n] at hpos
  rw [hx,hy] at hT
  have h : relativeC S T*relativeS S T*((frameY S n)^2-(frameX S n)^2)=0 := by
    linear_combination hT-(relativeC S T^2-relativeS S T^2)*hS
  have hne : (frameY S n)^2-(frameX S n)^2 ≠ 0 := by
    rcases mul_eq_zero.mp hS with h0 | h0 <;> rw [h0] at hpos ⊢
    · exact ne_of_gt (by nlinarith)
    · exact ne_of_lt (by nlinarith)
  exact mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hne)

lemma cardinal_box {c s X Y : ℝ} (hu : c^2+s^2=1) (hz : c=0 ∨ s=0) :
    (|c*X+s*Y| < 1/2 ∧ |-s*X+c*Y| < 1/2) ↔ (|X| < 1/2 ∧ |Y| < 1/2) := by
  rcases hz with rfl | rfl
  · have hs : |s|=1 := by simpa using (sq_eq_sq_iff_abs_eq_abs s 1).mp (by linarith)
    simp [abs_mul,hs,and_comm]
  · have hc : |c|=1 := by simpa using (sq_eq_sq_iff_abs_eq_abs c 1).mp (by linarith)
    simp [abs_mul,hc]

lemma same_axes_represents (S T : UnitSquare) (o : Point) (φ : Direction)
    (hc : φ.cos=S.cosine) (hs : φ.sin=S.sine) (haxes : SameAxes S T) :
    Represents T o φ (frameX S (sub T.center o),frameY S (sub T.center o)) := by
  intro x y
  have heX : localX T (pointInDirection o φ x y)=
      relativeC S T*(x-frameX S (sub T.center o))+
      relativeS S T*(y-frameY S (sub T.center o)) := by
    simp only [localX,pointInDirection,relativeC,relativeS,frameX,frameY,sub,hc,hs]
    linear_combination (T.cosine*(T.center.1-o.1)+T.sine*(T.center.2-o.2))*S.unit
  have heY : localY T (pointInDirection o φ x y)=
      -relativeS S T*(x-frameX S (sub T.center o))+
      relativeC S T*(y-frameY S (sub T.center o)) := by
    simp only [localY,pointInDirection,relativeC,relativeS,frameX,frameY,sub,hc,hs]
    linear_combination (T.cosine*(T.center.2-o.2)-T.sine*(T.center.1-o.1))*S.unit
  simp only [openSquare,heX,heY]
  exact cardinal_box (relative_unit S T) haxes

lemma self_represents (S : UnitSquare) (o : Point) (φ : Direction)
    (hc : φ.cos=S.cosine) (hs : φ.sin=S.sine) :
    Represents S o φ (frameX S (sub S.center o),frameY S (sub S.center o)) := by
  apply same_axes_represents S S o φ hc hs
  right
  dsimp [relativeS]; ring

/-- Two squares with the same centre and the same axes have the same interior. -/
lemma same_axes_open {S T : UnitSquare} (hc : T.center=S.center) (h : SameAxes S T)
    (p : Point) : openSquare T p ↔ openSquare S p := by
  obtain ⟨hx,hy⟩ := relative_normal S T (sub p S.center)
  change |frameX T (sub p T.center)| < 1/2 ∧ |frameY T (sub p T.center)| < 1/2 ↔
    |frameX S (sub p S.center)| < 1/2 ∧ |frameY S (sub p S.center)| < 1/2
  rw [hc,hx,hy]
  exact cardinal_box (relative_unit S T) h

lemma centers_distance_sq_ge_one (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    1 ≤ normSq (sub T.center S.center) := by
  by_contra hn
  let m : Point := scale (1/2) (add S.center T.center)
  have heS : normSq (sub m S.center)=normSq (sub T.center S.center)/4 := by
    dsimp [m,scale,add,sub,normSq]; ring
  have heT : normSq (sub m T.center)=normSq (sub T.center S.center)/4 := by
    dsimp [m,scale,add,sub,normSq]; ring
  exact hd m ⟨small_disk_in_openSquare S (by rw [heS]; linarith),
    small_disk_in_openSquare T (by rw [heT]; linarith)⟩

/-- A unit vector with a zero coordinate is one of the four cardinal vectors. -/
lemma cardinal_of_mul_eq_zero {x y : ℝ} (h1 : x^2+y^2=1) (h0 : x*y=0) :
    (x=1 ∧ y=0) ∨ (x=0 ∧ y=1) ∨ (x= -1 ∧ y=0) ∨ (x=0 ∧ y= -1) := by
  rcases mul_eq_zero.mp h0 with rfl | rfl
  · rcases sq_eq_one_iff.mp (by linarith : y^2=1) with rfl | rfl <;> simp
  · rcases sq_eq_one_iff.mp (by linarith : x^2=1) with rfl | rfl <;> simp

/-- Equality of center distance forces parallel axes and a cardinal displacement. -/
lemma unit_contact (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hunit : normSq (sub T.center S.center)=1) :
    SameAxes S T ∧
      ((frameX S (sub T.center S.center)=1 ∧ frameY S (sub T.center S.center)=0) ∨
       (frameX S (sub T.center S.center)=0 ∧ frameY S (sub T.center S.center)=1) ∨
       (frameX S (sub T.center S.center)= -1 ∧ frameY S (sub T.center S.center)=0) ∨
       (frameX S (sub T.center S.center)=0 ∧ frameY S (sub T.center S.center)= -1)) := by
  obtain ⟨e⟩ := support_separator S T hd
  set n := e.normal
  set d := sub T.center S.center
  set r := Real.sqrt (normSq n)
  have hr : 0 < r := Real.sqrt_pos.mpr (normSq_pos_of_ne e.nonzero)
  have hr2 : r^2=normSq n := Real.sq_sqrt (normSq_nonneg n)
  -- `r ≤ width S n + width T n ≤ dot n d ≤ r`, so all three are equalities
  have hdot : dot n d ≤ r := by nlinarith [cauchy_sq n d]
  have hsep := e.separates
  have hS := width_lower S n
  have hT := width_lower T n
  unfold width at hsep
  -- so `n` is along a side of each square
  have hside (U : UnitSquare) (hU : |frameX U n|+|frameY U n|=r) :
      frameX U n*frameY U n=0 := by
    have hu := frame_norm U n
    refine abs_eq_zero.mp ?_
    rw [abs_mul]
    nlinarith [sq_abs (frameX U n),sq_abs (frameY U n)]
  have hnS := hside S (by linarith)
  refine ⟨same_axes_from_normal S T e.nonzero hnS (hside T (by linarith)),
    cardinal_of_mul_eq_zero (by rw [frame_norm]; exact hunit) ?_⟩
  -- and parallel to `d`: `(p y - q x)^2 = |n|^2 |d|^2 - (n·d)^2 = 0`
  have hn := frame_norm S n
  have hdd := frame_norm S d
  have hnd := frame_dot S n d
  rw [hunit] at hdd
  have hD : dot n d=r := by linarith
  have hlag : (frameX S n*frameY S d-frameY S n*frameX S d)^2=0 := by
    linear_combination (frameX S d^2+frameY S d^2)*hn+normSq n*hdd-
      (frameX S n*frameX S d+frameY S n*frameY S d+dot n d)*hnd-hr2-(r+dot n d)*hD
  have hpy := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hlag)
  have hN : 0 < normSq n := normSq_pos_of_ne e.nonzero
  rcases mul_eq_zero.mp hnS with h0 | h0 <;> rw [h0] at hn hpy
  · have hq : frameY S n ≠ 0 := fun hq => by rw [hq] at hn; linarith
    rw [(mul_eq_zero.mp (by linarith : frameY S n*frameX S d=0)).resolve_left hq,zero_mul]
  · have hp : frameX S n ≠ 0 := fun hp => by rw [hp] at hn; linarith
    rw [(mul_eq_zero.mp (by linarith : frameX S n*frameY S d=0)).resolve_left hp,mul_zero]

end SquaresInCircles
