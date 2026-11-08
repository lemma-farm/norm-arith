module

public import SquaresInCircles.Geometry

/-!
# Frames, interior-disjointness and the farthest-vertex bound

Vector operations, a square's frame and vertices, and the squared distance
`phi` from a point to the farthest vertex of a square: the closed square lies
in a closed disk about the point exactly when `phi` is at most the squared
radius, and `phi` bounds the distance of the centre. Distances always use
`normSq`; the product-space norm on `ℝ × ℝ` is the maximum norm.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

def dot (p q : Point) : ℝ := p.1 * q.1 + p.2 * q.2
def add (p q : Point) : Point := (p.1 + q.1, p.2 + q.2)
def scale (t : ℝ) (p : Point) : Point := (t * p.1, t * p.2)

lemma normSq_nonneg (p : Point) : 0 ≤ normSq p :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

lemma normSq_pos_of_ne {v : Point} (hv : v ≠ (0,0)) : 0 < normSq v := by
  rcases v with ⟨x,y⟩
  have h : x ≠ 0 ∨ y ≠ 0 := by
    by_contra! h
    exact hv (by rw [h.1,h.2])
  unfold normSq
  rcases h with h | h <;> positivity

lemma sub_ne_origin {p q : Point} (h : p ≠ q) : sub p q ≠ (0,0) := fun hh =>
  h (Prod.ext (sub_eq_zero.mp (congrArg Prod.fst hh)) (sub_eq_zero.mp (congrArg Prod.snd hh)))

lemma dot_add_right (v p q : Point) : dot v (add p q) = dot v p + dot v q := by
  dsimp [dot, add]; ring
lemma dot_sub_right (v p q : Point) : dot v (sub p q) = dot v p - dot v q := by
  dsimp [dot, sub]; ring
lemma dot_scale_right (v : Point) (t : ℝ) (p : Point) :
    dot v (scale t p) = t * dot v p := by dsimp [dot, scale]; ring

/-- The Cauchy–Schwarz inequality, squared. -/
lemma cauchy_sq (u v : Point) : (dot u v)^2 ≤ normSq u*normSq v := by
  have h := sq_nonneg (u.1*v.2-u.2*v.1)
  dsimp [dot,normSq]
  linarith

/-- Non-overlap, without a containing disk or any lower-bound assumption. -/
def InteriorDisjoint {ι : Type*} (S : ι → UnitSquare) : Prop :=
  ∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p)

lemma Packing.disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) : InteriorDisjoint S := hp.2.2

lemma InteriorDisjoint.pairwise {ι : Type*} {S : ι → UnitSquare}
    (hd : InteriorDisjoint S) :
    Pairwise (fun i j => Disjoint {p | openSquare (S i) p} {p | openSquare (S j) p}) :=
  fun i j hij => Set.disjoint_left.mpr fun p hi hj => hd i j hij p ⟨hi,hj⟩

/-- The coordinates of a vector in a square's frame; `localX S p` is
`frameX S (sub p S.center)`. -/
def frameX (S : UnitSquare) (v : Point) : ℝ := S.cosine*v.1 + S.sine*v.2
def frameY (S : UnitSquare) (v : Point) : ℝ := -S.sine*v.1 + S.cosine*v.2

lemma frame_norm (S : UnitSquare) (v : Point) :
    (frameX S v)^2 + (frameY S v)^2 = normSq v := by
  simp only [frameX,frameY,normSq]; linear_combination (v.1^2+v.2^2)*S.unit

lemma frame_dot (S : UnitSquare) (v w : Point) :
    frameX S v * frameX S w + frameY S v * frameY S w = dot v w := by
  simp only [frameX,frameY,dot]; linear_combination (v.1*w.1+v.2*w.2)*S.unit

/-- The coordinates of a vector in the frame of a square have absolute values
adding up to at least its length. -/
lemma width_lower (S : UnitSquare) (n : Point) :
    Real.sqrt (normSq n) ≤ |frameX S n|+|frameY S n| := by
  rw [Real.sqrt_le_left (by positivity),← frame_norm S n]
  nlinarith [sq_abs (frameX S n),sq_abs (frameY S n),abs_nonneg (frameX S n),
    abs_nonneg (frameY S n)]

lemma frame_distance (S : UnitSquare) (p o : Point) :
    (localX S p - localX S o)^2 + (localY S p - localY S o)^2 = normSq (sub p o) := by
  rw [← frame_norm]; simp only [localX,localY,frameX,frameY,sub]; ring

/-- The vector with coordinates `p` in the frame of `S`. -/
def rotate (S : UnitSquare) (p : Point) : Point :=
  (S.cosine * p.1 - S.sine * p.2,
   S.sine * p.1 + S.cosine * p.2)

lemma localX_rotated (S : UnitSquare) (p : Point) :
    localX S (add S.center (rotate S p)) = p.1 := by
  simp only [localX,add,rotate]; linear_combination p.1*S.unit

lemma localY_rotated (S : UnitSquare) (p : Point) :
    localY S (add S.center (rotate S p)) = p.2 := by
  simp only [localY,add,rotate]; linear_combination p.2*S.unit

/-- Nonnegative absolute coordinates of the tested point in a square's frame. -/
def alpha (S : UnitSquare) (o : Point) : ℝ := |localX S o|
def beta (S : UnitSquare) (o : Point) : ℝ := |localY S o|

lemma alpha_nonneg (S : UnitSquare) (o : Point) : 0 ≤ alpha S o := abs_nonneg _
lemma beta_nonneg (S : UnitSquare) (o : Point) : 0 ≤ beta S o := abs_nonneg _

lemma abs_frame_centerX (S : UnitSquare) (o : Point) :
    |frameX S (sub S.center o)| = alpha S o := by
  rw [alpha,← abs_neg]; congr 1; simp only [frameX,sub,localX]; ring

lemma abs_frame_centerY (S : UnitSquare) (o : Point) :
    |frameY S (sub S.center o)| = beta S o := by
  rw [beta,← abs_neg]; congr 1; simp only [frameY,sub,localY]; ring

lemma local_center_norm (S : UnitSquare) (o : Point) :
    normSq (sub S.center o)=(alpha S o)^2+(beta S o)^2 := by
  rw [← frame_norm,← abs_frame_centerX,← abs_frame_centerY,sq_abs,sq_abs]

/-- Squared distance to the farthest vertex in local absolute coordinates. -/
def phi (a b : ℝ) : ℝ := (a + 1/2)^2 + (b + 1/2)^2

/-- A number of absolute value `c` with the sign of `x`. -/
lemma exists_signed (x : ℝ) {c : ℝ} (hc : 0 ≤ c) : ∃ u : ℝ, |u|=c ∧ x*u=c*|x| := by
  rcases abs_cases x with ⟨hx,-⟩ | ⟨hx,-⟩
  · exact ⟨c,abs_of_nonneg hc,by rw [hx]; ring⟩
  · exact ⟨-c,by rw [abs_neg,abs_of_nonneg hc],by rw [hx]; ring⟩

/-- The vertex across both axes from `o` is at squared distance `phi` from it. -/
lemma phi_le_of_contained (S : UnitSquare) (o : Point) (R : ℝ)
    (h : ∀ p, closedSquare S p → inDisk o R p) :
    phi (alpha S o) (beta S o) ≤ R^2 := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (localX S o) (c := 1/2) (by norm_num)
  obtain ⟨v,hv,hyv⟩ := exists_signed (localY S o) (c := 1/2) (by norm_num)
  have hh := h (add S.center (rotate S (-u,-v))) (by
    simp only [closedSquare,localX_rotated,localY_rotated,abs_neg,hu,hv,le_refl,and_self])
  rw [inDisk,← frame_distance S,localX_rotated,localY_rotated] at hh
  have hu2 : u^2=1/4 := by rw [← sq_abs,hu]; norm_num
  have hv2 : v^2=1/4 := by rw [← sq_abs,hv]; norm_num
  unfold phi alpha beta
  nlinarith [sq_abs (localX S o),sq_abs (localY S o)]

lemma Packing.phi_le {n : ℕ} {S : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (hp : Packing S o R) (i : Fin n) :
    phi (alpha (S i) o) (beta (S i) o) ≤ R^2 :=
  phi_le_of_contained _ _ _ (hp.2.1 i)

/-- The converse of the farthest-vertex bound: if `φ(α, β) ≤ R²`, the closed
square lies in the closed disk of radius `R` about `o`. -/
lemma inDisk_of_phi_le {S : UnitSquare} {o : Point} {R : ℝ}
    (hphi : phi (alpha S o) (beta S o) ≤ R^2) {p : Point} (hp : closedSquare S p) :
    inDisk o R p := by
  have hx : |localX S p-localX S o| ≤ alpha S o+1/2 := by
    unfold alpha; linarith [abs_sub (localX S p) (localX S o),hp.1]
  have hy : |localY S p-localY S o| ≤ beta S o+1/2 := by
    unfold beta; linarith [abs_sub (localY S p) (localY S o),hp.2]
  rw [inDisk,← frame_distance S,← sq_abs (localX S p-_),← sq_abs (localY S p-_)]
  exact (add_le_add (pow_le_pow_left₀ (abs_nonneg _) hx 2)
    (pow_le_pow_left₀ (abs_nonneg _) hy 2)).trans hphi

/-- If `a, b ≥ 0` and `φ(a, b) ≤ ρ² + ρ + 1/2`, then `a² + b² ≤ ρ²`: a square
whose farthest vertex is within `√(ρ² + ρ + 1/2)` of `o` has its centre within
`ρ` of `o`. -/
lemma radial_sq_le_of_phi {a b ρ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : phi a b ≤ ρ^2+ρ+1/2) : a^2+b^2 ≤ ρ^2 := by
  by_contra! hr
  have hsum : a+b < ρ := by unfold phi at h; nlinarith
  nlinarith [mul_pos (sub_pos.mpr hsum) (show 0 < ρ+a+b by linarith),mul_nonneg ha hb]

/-- If `b ≥ 0` and `φ(a, b) ≤ Q`, then `a ≤ √(Q - 1/4) - 1/2`. -/
lemma coordinate_le_of_phi {a b Q : ℝ} (hb : 0 ≤ b) (h : phi a b ≤ Q) :
    a ≤ Real.sqrt (Q-1/4)-1/2 := by
  have hs := Real.le_sqrt_of_sq_le (show (a+1/2)^2 ≤ Q-1/4 by unfold phi at h; nlinarith)
  linarith

private lemma clipped_distance {x v : ℝ} (hv : |v|=min |x| (1/2))
    (hprod : x*v=min |x| (1/2)*|x|) : (v-x)^2=(max (|x|-1/2) 0)^2 := by
  have hv2 : v^2=(min |x| (1/2))^2 := by rw [← sq_abs v,hv]
  have hx2 := sq_abs x
  rcases le_total |x| (1/2) with h | h
  · rw [min_eq_left h] at hv2 hprod
    rw [max_eq_right (by linarith : |x|-1/2 ≤ 0)]
    nlinarith
  · rw [min_eq_right h] at hv2 hprod
    rw [max_eq_left (by linarith : 0 ≤ |x|-1/2)]
    nlinarith

/-- A point of the closed square at squared distance
`(max (α - 1/2) 0)² + (max (β - 1/2) 0)²` from `o`. -/
lemma exists_clipped_point (S : UnitSquare) (o : Point) :
    ∃ p : Point, closedSquare S p ∧
      normSq (sub p o)=(max (alpha S o-1/2) 0)^2+(max (beta S o-1/2) 0)^2 := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (localX S o) (c := min |localX S o| (1/2))
    (le_min (abs_nonneg _) (by norm_num))
  obtain ⟨v,hv,hyv⟩ := exists_signed (localY S o) (c := min |localY S o| (1/2))
    (le_min (abs_nonneg _) (by norm_num))
  refine ⟨add S.center (rotate S (u,v)),⟨?_,?_⟩,?_⟩
  · rw [localX_rotated,hu]; exact min_le_right _ _
  · rw [localY_rotated,hv]; exact min_le_right _ _
  · rw [← frame_distance S,localX_rotated,localY_rotated,clipped_distance hu hxu,
      clipped_distance hv hyv]
    rfl

/-- The disk given by the nearer side of a containing square is really inside it. -/
lemma inscribed_disk_mem (S : UnitSquare) (o : Point) {a p : ℝ}
    (hp : 0 < p) (hpa : a+p=1/2)
    (hx : alpha S o ≤ a) (hy : beta S o ≤ a) {z : Point}
    (hz : normSq (sub z o) < p^2) : openSquare S z := by
  have hu := frame_norm S (sub z o)
  have hX := abs_lt_of_sq_lt_sq (a := frameX S (sub z o))
    (by nlinarith [sq_nonneg (frameY S (sub z o))]) hp.le
  have hY := abs_lt_of_sq_lt_sq (a := frameY S (sub z o))
    (by nlinarith [sq_nonneg (frameX S (sub z o))]) hp.le
  have heX : localX S z=frameX S (sub z o)+localX S o := by simp only [localX,frameX,sub]; ring
  have heY : localY S z=frameY S (sub z o)+localY S o := by simp only [localY,frameY,sub]; ring
  exact ⟨by rw [heX]; linarith [abs_add_le (frameX S (sub z o)) (localX S o),
      show |localX S o| ≤ a from hx],
    by rw [heY]; linarith [abs_add_le (frameY S (sub z o)) (localY S o),
      show |localY S o| ≤ a from hy]⟩

lemma small_disk_in_openSquare (S : UnitSquare) {p : Point}
    (hp : normSq (sub p S.center) < 1/4) : openSquare S p :=
  inscribed_disk_mem S S.center (a := 0) (p := 1/2) (by norm_num) (by norm_num)
    (by simp [alpha,localX]) (by simp [beta,localY]) (by linarith)

def halfDiagonal : ℝ := Real.sqrt 2/2

lemma halfDiagonal_pos : 0 < halfDiagonal := by unfold halfDiagonal; positivity
lemma halfDiagonal_sq : halfDiagonal^2=1/2 := by
  rw [halfDiagonal,div_pow,Real.sq_sqrt (by norm_num)]; norm_num

end SquaresInCircles
