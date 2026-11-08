module

public import SquaresInCircles.Common.Basic
public import Mathlib.Analysis.LocallyConvex.Separation

/-!
# A supporting functional for two squares with disjoint interiors

Open squares are convex and open, so the geometric Hahn--Banach theorem
separates two squares with disjoint interiors by a nonzero linear functional
`dot n`. `support_separator` sharpens this to the exact support bound
`width S n + width T n ≤ dot n (sub T.center S.center)` by testing the
functional on shrunk support vertices, which lie in the open squares.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

lemma weighted_strict {a b u v H : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : 0 < a+b) (hu : u < H) (hv : v < H) :
    a*u+b*v < H*(a+b) := by
  rcases ha.lt_or_eq with ha | rfl
  · nlinarith [mul_le_mul_of_nonneg_left hv.le hb]
  · nlinarith

lemma abs_affine_lt {a b u v r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) (hu : |u| < r) (hv : |v| < r) : |a*u+b*v| < r := by
  have h := weighted_strict ha hb (by linarith) hu hv
  rw [hab,mul_one] at h
  calc |a*u+b*v| ≤ |a*u|+|b*v| := abs_add_le _ _
    _ = a*|u|+b*|v| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
    _ < r := h

/-- Local coordinates are affine. -/
lemma local_affine (S : UnitSquare) (p q : Point) {a b : ℝ} (hab : a+b=1) :
    localX S (a • p+b • q)=a*localX S p+b*localX S q ∧
    localY S (a • p+b • q)=a*localY S p+b*localY S q := by
  obtain rfl : b=1-a := by linarith
  constructor <;> simp only [localX,localY,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    smul_eq_mul] <;> ring

lemma openSquare_convex (S : UnitSquare) : Convex ℝ {p | openSquare S p} := by
  intro p hp q hq a b ha hb hab
  obtain ⟨hx,hy⟩ := local_affine S p q hab
  exact ⟨by rw [hx]; exact abs_affine_lt ha hb hab hp.1 hq.1,
    by rw [hy]; exact abs_affine_lt ha hb hab hp.2 hq.2⟩

/-- A point of the closed square moved towards the centre, short of the full
way, lies in the open square. -/
lemma shrink_open (S : UnitSquare) {p : Point} (hp : closedSquare S p)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    openSquare S ((1-t) • S.center+t • p) := by
  obtain ⟨hx,hy⟩ := local_affine S S.center p (sub_add_cancel 1 t)
  have h0 : localX S S.center=0 ∧ localY S S.center=0 := by simp [localX,localY]
  rw [h0.1,mul_zero,zero_add] at hx
  rw [h0.2,mul_zero,zero_add] at hy
  constructor
  · rw [hx,abs_mul,abs_of_nonneg ht0]; nlinarith [hp.1,abs_nonneg (localX S p)]
  · rw [hy,abs_mul,abs_of_nonneg ht0]; nlinarith [hp.2,abs_nonneg (localY S p)]

lemma openSquare_isOpen (S : UnitSquare) : IsOpen {p | openSquare S p} := by
  have hX : Continuous (localX S) := by unfold localX; fun_prop
  have hY : Continuous (localY S) := by unfold localY; fun_prop
  exact (isOpen_lt hX.abs continuous_const).inter
    (isOpen_lt hY.abs continuous_const)

lemma center_in_openSquare (S : UnitSquare) : openSquare S S.center := by
  norm_num [openSquare,localX,localY]

/-- Half the width of a square in the direction `n`, in units of `|n|`. -/
def width (S : UnitSquare) (n : Point) : ℝ :=
  (|frameX S n|+|frameY S n|)/2

lemma width_neg (S : UnitSquare) (n : Point) :
    width S (scale (-1) n) = width S n := by
  have h₁ : frameX S (scale (-1) n) = -frameX S n := by dsimp [frameX,scale]; ring
  have h₂ : frameY S (scale (-1) n) = -frameY S n := by dsimp [frameY,scale]; ring
  simp only [width,h₁,h₂,abs_neg]

/-- Shrunk support vertices lie in the open square, even when a coefficient is zero. -/
lemma support_point (S : UnitSquare) (n : Point) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∃ p : Point, openSquare S p ∧
      dot n p = dot n S.center+t*width S n := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (frameX S n) (c := 1/2) (by norm_num)
  obtain ⟨v,hv,hyv⟩ := exists_signed (frameY S n) (c := 1/2) (by norm_num)
  refine ⟨_,shrink_open S (p := add S.center (rotate S (u,v)))
    ⟨by rw [localX_rotated,hu],by rw [localY_rotated,hv]⟩ ht0 ht1,?_⟩
  simp only [dot,add,rotate,width,frameX,frameY,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
    Prod.smul_snd,smul_eq_mul] at hxu hyv ⊢
  linear_combination t*hxu+t*hyv

/-- A scalar endpoint is obtained from all strict convex combinations. -/
lemma affine_endpoint_le {A B D : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t < 1 → (1-t)*A+t*B ≤ D) : B ≤ D := by
  have hA : A ≤ D := by simpa using h 0 le_rfl one_pos
  by_contra hn
  have hBA : 0 < B-A := by linarith
  set t := (D-A+(B-A))/(2*(B-A))
  have ht : t*(B-A)=(D-A+(B-A))/2 := by simp only [t]; field_simp
  have h1 := h t (div_nonneg (by linarith) (by linarith))
    (by rw [div_lt_one (by linarith)]; linarith)
  linarith

lemma bound_from_shrinks {H D : ℝ}
    (h : ∀ t : ℝ, 0 ≤ t → t < 1 → t*H ≤ D) : H ≤ D :=
  affine_endpoint_le (A := 0) fun t h0 h1 => by simpa using h t h0 h1

/-- A nonzero functional that separates two squares by their full widths. -/
structure Separation (S T : UnitSquare) where
  normal : Point
  nonzero : normal ≠ (0,0)
  separates : width S normal+width T normal ≤ dot normal (sub T.center S.center)

/-- A nonzero supporting functional for two squares with disjoint open interiors. -/
theorem support_separator (S T : UnitSquare)
    (hdisj : ∀ p, ¬ (openSquare S p ∧ openSquare T p)) :
    Nonempty (Separation S T) := by
  have hd : Disjoint {p | openSquare S p} {p | openSquare T p} :=
    Set.disjoint_left.mpr fun p hp hq => hdisj p ⟨hp,hq⟩
  obtain ⟨f,u,hS,hT⟩ := geometric_hahn_banach_open_open
    (openSquare_convex S) (openSquare_isOpen S)
    (openSquare_convex T) (openSquare_isOpen T) hd
  let n : Point := (f (1,0), f (0,1))
  have hf (p : Point) : f p = dot n p := by
    have he : p = p.1 • (1,0) + p.2 • (0,1) := by ext <;> simp
    conv_lhs => rw [he]
    simp only [map_add,map_smul,smul_eq_mul]
    dsimp [dot,n]
    ring
  have hn : n ≠ (0,0) := by
    intro hn
    have hh := lt_trans (hS _ (center_in_openSquare S))
      (hT _ (center_in_openSquare T))
    rw [hf,hf,hn] at hh
    norm_num [dot] at hh
  refine ⟨⟨n,hn,bound_from_shrinks ?_⟩⟩
  intro t ht0 ht1
  obtain ⟨p,hp,hpval⟩ := support_point S n ht0 ht1
  obtain ⟨q,hq,hqval⟩ := support_point T (scale (-1) n) ht0 ht1
  have hsep := lt_trans (hS p hp) (hT q hq)
  rw [hf,hf,hpval] at hsep
  rw [width_neg] at hqval
  simp only [dot,scale,neg_one_mul] at hqval
  dsimp [dot,sub] at hsep ⊢
  linarith

lemma frame_abs_sum_pos (S : UnitSquare) {n : Point} (hn : n ≠ (0,0)) :
    0 < |frameX S n|+|frameY S n| := by
  have hp := normSq_pos_of_ne hn
  rw [← frame_norm S n,← sq_abs (frameX S n),← sq_abs (frameY S n)] at hp
  by_contra h
  nlinarith [abs_nonneg (frameX S n),abs_nonneg (frameY S n)]

lemma dot_open_bound_of_ne (S : UnitSquare) {n : Point} (hn : n ≠ (0,0))
    {p : Point} (hp : openSquare S p) : |dot n (sub p S.center)| < width S n := by
  have hh := weighted_strict (abs_nonneg (frameX S n)) (abs_nonneg (frameY S n))
    (frame_abs_sum_pos S hn) hp.1 hp.2
  rw [← frame_dot S]
  change |frameX S n*localX S p+frameY S n*localY S p| < width S n
  have ha := abs_add_le (frameX S n*localX S p) (frameY S n*localY S p)
  rw [abs_mul,abs_mul] at ha
  dsimp [width]
  linarith

lemma closed_dot_bound (S : UnitSquare) (n : Point) {p : Point}
    (hp : closedSquare S p) : |dot n (sub p S.center)| ≤ width S n := by
  rw [← frame_dot S]
  change |frameX S n*localX S p+frameY S n*localY S p| ≤ width S n
  have ha := abs_add_le (frameX S n*localX S p) (frameY S n*localY S p)
  rw [abs_mul,abs_mul] at ha
  have hx := mul_le_mul_of_nonneg_left hp.1 (abs_nonneg (frameX S n))
  have hy := mul_le_mul_of_nonneg_left hp.2 (abs_nonneg (frameY S n))
  dsimp [width]
  linarith

lemma closed_open_disjoint (S T : UnitSquare)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    {p : Point} (hS : closedSquare S p) : ¬ openSquare T p := by
  obtain ⟨e⟩ := support_separator S T hd
  intro hT
  have h₁ := (abs_le.mp (closed_dot_bound S e.normal hS)).2
  have h₂ := (abs_lt.mp (dot_open_bound_of_ne T e.nonzero hT)).1
  have hsep := e.separates
  simp only [dot_sub_right] at *
  linarith

end SquaresInCircles
