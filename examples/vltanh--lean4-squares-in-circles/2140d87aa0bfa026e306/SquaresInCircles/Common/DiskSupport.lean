module

public import SquaresInCircles.Common.Contacts
public import SquaresInCircles.Common.Trigonometry

/-!
# Supports of a square in a disk

Cauchy–Schwarz (`cauchy_sq`) bounds a linear form on the disk `X² + Y² ≤ Q`
(`dot_ge`, `dot_gt`, `dot_le_radius`). Some vertex of a square lies `width S n`
beyond its centre along `n`, so a square in the closed disk of radius `R` about
the origin has `⟨n, c⟩ ≤ R |n| - width S n` (`center_le_vertexSupport`); in the
frame of the square, with the far corner `(|a| + 1/2, |b| + 1/2)` in the disk,
the force `(U, V)` does work at most `R |(U, V)| - (|U| + |V|)/2` on the centre
`(a, b)` (`box_vertex_support`). The support function `support a b z` of the
closed axis-parallel square at `(a, b)` bounds the projection of each of its
points (`point_le_support`), and is at least `1/2 - ρ` when the centre is within
`ρ` of the origin (`support_ge`).
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-! ### Cauchy–Schwarz on a disk -/

/-- Cauchy–Schwarz on the disk `X² + Y² ≤ Q`. -/
lemma dot_sq_le {X Y p r Q : ℝ} (h : X^2+Y^2 ≤ Q) : (p*X+r*Y)^2 ≤ Q*(p^2+r^2) :=
  (cauchy_sq (p,r) (X,Y)).trans
    ((mul_le_mul_of_nonneg_left h (normSq_nonneg (p,r))).trans_eq (mul_comm _ _))

/-- Cauchy–Schwarz on the disk of squared radius `Q`: a linear form whose squared
norm is at most `c²/Q` is at least `-c` there. -/
lemma dot_ge {X Y p r Q c : ℝ} (h : X^2+Y^2 ≤ Q) (hc : 0 ≤ c)
    (hpr : Q*(p^2+r^2) ≤ c^2) : -c ≤ p*X+r*Y :=
  (abs_le_of_sq_le_sq' ((dot_sq_le h).trans hpr) hc).1

lemma dot_gt {X Y p r Q c : ℝ} (h : X^2+Y^2 ≤ Q) (hc : 0 ≤ c)
    (hpr : Q*(p^2+r^2) < c^2) : -c < p*X+r*Y :=
  (abs_lt_of_sq_lt_sq' ((dot_sq_le h).trans_lt hpr) hc).1

/-- The length of a vector. -/
def vectorLength (v : Point) : ℝ := Real.sqrt (normSq v)

lemma vectorLength_nonneg (v : Point) : 0 ≤ vectorLength v := Real.sqrt_nonneg _

lemma vectorLength_sq (v : Point) : vectorLength v^2=normSq v := Real.sq_sqrt (normSq_nonneg v)

/-- A point `p` of the closed disk of radius `R` about the origin has
`⟨v, p⟩ ≤ R |v|`. -/
lemma dot_le_radius {v p : Point} {R : ℝ} (hR : 0 ≤ R) (hp : normSq p ≤ R^2) :
    dot v p ≤ R*vectorLength v := by
  refine (abs_le_of_sq_le_sq' ?_ (mul_nonneg hR (vectorLength_nonneg v))).2
  rw [mul_pow,vectorLength_sq]
  exact dot_sq_le hp

/-! ### The far vertex -/

/-- The far-vertex support `R |v| - width S v`. -/
def vertexSupport (R : ℝ) (S : UnitSquare) (v : Point) : ℝ :=
  R*vectorLength v-width S v

/-- Some vertex of the square lies `width S n` beyond its centre along `n`. -/
lemma exists_support_vertex (S : UnitSquare) (n : Point) :
    ∃ p, closedSquare S p ∧ dot n p=dot n S.center+width S n := by
  obtain ⟨u,hu,hxu⟩ := exists_signed (frameX S n) (c := 1/2) (by norm_num)
  obtain ⟨v,hv,hyv⟩ := exists_signed (frameY S n) (c := 1/2) (by norm_num)
  refine ⟨add S.center (rotate S (u,v)),⟨by rw [localX_rotated,hu],by rw [localY_rotated,hv]⟩,?_⟩
  simp only [dot,add,rotate,width,frameX,frameY] at hxu hyv ⊢
  linear_combination hxu+hyv

/-- A square in the closed disk of radius `R` about the origin has
`⟨n, c⟩ ≤ R |n| - width S n` for every `n`. -/
theorem center_le_vertexSupport {S : UnitSquare} {R : ℝ}
    (hR : 0 ≤ R) (hcontain : ∀ p, closedSquare S p → inDisk (0,0) R p) (n : Point) :
    dot n S.center ≤ vertexSupport R S n := by
  obtain ⟨p,hp,he⟩ := exists_support_vertex S n
  have hb := dot_le_radius (v := n) hR (by simpa [inDisk,sub] using hcontain p hp)
  dsimp [vertexSupport]
  linarith

/-- The far-vertex support in the frame of a square: if the far corner
`(|a| + 1/2, |b| + 1/2)` lies in the disk of radius `R`, the force `(U, V)` does
work at most `R |(U, V)| - (|U| + |V|)/2` on the centre `(a, b)`. -/
lemma box_vertex_support {R a b : ℝ} (hR : 0 ≤ R) (hbox : (|a|+1/2)^2+(|b|+1/2)^2 ≤ R^2)
    (U V : ℝ) : U*a+V*b ≤ R*Real.sqrt (U^2+V^2)-(|U|+|V|)/2 := by
  have hC := dot_le_radius (v := (|U|,|V|)) (p := (|a|+1/2,|b|+1/2)) hR hbox
  simp only [vectorLength,normSq,dot,sq_abs] at hC
  have hA : U*a ≤ |U| * |a| := by rw [← abs_mul]; exact le_abs_self _
  have hB : V*b ≤ |V| * |b| := by rw [← abs_mul]; exact le_abs_self _
  linarith

/-! ### The support function of an axis-parallel square -/

/-- The support function of the closed axis-parallel unit square centred at
`(a, b)`: its largest projection on the direction `z`. -/
def support (a b z : ℝ) : ℝ :=
  a*Real.cos z+b*Real.sin z+(|Real.cos z|+|Real.sin z|)/2

lemma point_le_support {a b x y : ℝ} (hx : |x-a| ≤ 1/2) (hy : |y-b| ≤ 1/2) (z : ℝ) :
    x*Real.cos z+y*Real.sin z ≤ support a b z := by
  have h1 : (x-a)*Real.cos z ≤ 1/2*|Real.cos z| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  have h2 : (y-b)*Real.sin z ≤ 1/2*|Real.sin z| :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hy (abs_nonneg _))
  unfold support
  linarith

/-- If the centre is within `ρ` of the origin, the support is at least `1/2 - ρ`
in every direction. -/
lemma support_ge {a b ρ : ℝ} (hρ : 0 ≤ ρ) (h : a^2+b^2 ≤ ρ^2) (z : ℝ) :
    1/2-ρ ≤ support a b z := by
  have hd := dot_ge (p := Real.cos z) (r := Real.sin z) h hρ
    (by rw [Real.cos_sq_add_sin_sq,mul_one])
  have hw := one_le_abs_cos_add_abs_sin z
  unfold support
  linarith

end SquaresInCircles
