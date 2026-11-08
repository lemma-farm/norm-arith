module

public import SquaresInCircles.Common.Charts
public import SquaresInCircles.Common.Constructions

/-!
# Congruence to a model

A configuration is congruent to a model when, in one frame at the disk centre
and after a relabelling, every square is the corresponding model square, both
as an open and as a closed set. It compares point sets, since a quarter-turn
of a frame describes the same square. `Represents`
places one square at an axis-parallel slot of the frame, and
`congruent_of_slots` turns an assignment of slots into congruence.
`modelSquare o φ c` is the square at `c` in the frame `φ` at `o`, and
`orientedSquare t a b` the one at `(a, b)` in the frame `t` at the origin.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-- The actual square, expressed in one common positively oriented frame. -/
def Represents (S : UnitSquare) (o : Point) (φ : Direction) (c : Point) : Prop :=
  ∀ x y, openSquare S (pointInDirection o φ x y) ↔ openAxisSquare c x y

/-- A rigid motion with its inverse written in coordinates. -/
def frameEquiv (o : Point) (φ : Direction) : Point ≃ Point where
  toFun p := pointInDirection o φ p.1 p.2
  invFun p := (φ.cos*(p.1-o.1)+φ.sin*(p.2-o.2),
    -φ.sin*(p.1-o.1)+φ.cos*(p.2-o.2))
  left_inv := by
    intro p
    have hu := Real.Angle.cos_sq_add_sin_sq φ
    apply Prod.ext <;> dsimp [pointInDirection]
    · linear_combination p.1*hu
    · linear_combination p.2*hu
  right_inv := by
    intro p
    have hu := Real.Angle.cos_sq_add_sin_sq φ
    apply Prod.ext <;> dsimp [pointInDirection]
    · linear_combination (p.1-o.1)*hu
    · linear_combination (p.2-o.2)*hu

@[simp] lemma frameEquiv_apply (o : Point) (φ : Direction) (p : Point) :
    frameEquiv o φ p = pointInDirection o φ p.1 p.2 := rfl

lemma frameEquiv_zero (o : Point) (φ : Direction) : frameEquiv o φ (0,0)=o := by
  simp [pointInDirection]

lemma frameEquiv_distance (o : Point) (φ : Direction) (p q : Point) :
    normSq (sub (frameEquiv o φ p) (frameEquiv o φ q))=normSq (sub p q) := by
  simp only [frameEquiv_apply,pointInDirection,normSq,sub]
  linear_combination ((p.1-q.1)^2+(p.2-q.2)^2)*Real.Angle.cos_sq_add_sin_sq φ

lemma abs_endpoint_le {A B : ℝ} (h : ∀ t : ℝ, 0 ≤ t → t < 1 → |(1-t)*A+t*B| < 1/2) :
    |B| ≤ 1/2 := by
  refine abs_le.mpr ⟨?_,affine_endpoint_le fun t h0 h1 => (abs_lt.mp (h t h0 h1)).2.le⟩
  have := affine_endpoint_le (A := -A) (B := -B) (D := 1/2) fun t h0 h1 => by
    linarith [(abs_lt.mp (h t h0 h1)).1]
  linarith

/-- Equality of open squares implies equality of their closed square sets. -/
lemma same_open_same_closed (S T : UnitSquare)
    (h : ∀ p, openSquare S p ↔ openSquare T p) :
    ∀ p, closedSquare S p ↔ closedSquare T p := by
  have oneWay (S T : UnitSquare) (hh : ∀ p, openSquare S p → openSquare T p)
      (p : Point) (hp : closedSquare S p) : closedSquare T p := by
    have hm (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) := hh _ (shrink_open S hp h0 h1)
    have he (t : ℝ) := local_affine T S.center p (sub_add_cancel 1 t)
    exact ⟨abs_endpoint_le fun t h0 h1 => (he t).1 ▸ (hm t h0 h1).1,
      abs_endpoint_le fun t h0 h1 => (he t).2 ▸ (hm t h0 h1).2⟩
  exact fun p => ⟨oneWay S T (fun q => (h q).mp) p,oneWay T S (fun q => (h q).mpr) p⟩

def modelSquare (o : Point) (φ : Direction) (c : Point) : UnitSquare where
  center := pointInDirection o φ c.1 c.2
  cosine := φ.cos
  sine := φ.sin
  unit := Real.Angle.cos_sq_add_sin_sq φ

lemma modelSquare_local (o : Point) (φ : Direction) (c : Point) (x y : ℝ) :
    localX (modelSquare o φ c) (pointInDirection o φ x y)=x-c.1 ∧
    localY (modelSquare o φ c) (pointInDirection o φ x y)=y-c.2 := by
  have hu := Real.Angle.cos_sq_add_sin_sq φ
  constructor <;> dsimp [localX,localY,modelSquare,pointInDirection]
  · linear_combination (x-c.1)*hu
  · linear_combination (y-c.2)*hu

/-- The unit square with frame angle `t` whose centre has the coordinates
`(a, b)` in that frame. -/
def orientedSquare (t a b : ℝ) : UnitSquare where
  center := (a*Real.cos t-b*Real.sin t,a*Real.sin t+b*Real.cos t)
  cosine := Real.cos t
  sine := Real.sin t
  unit := Real.cos_sq_add_sin_sq t

/-- The first coordinate of the centre of `orientedSquare t a b`. -/
def centerX (t a b : ℝ) : ℝ := a*Real.cos t-b*Real.sin t
/-- The second coordinate of the centre of `orientedSquare t a b`. -/
def centerY (t a b : ℝ) : ℝ := a*Real.sin t+b*Real.cos t

lemma orientedSquare_localX (t a b : ℝ) (p : Point) :
    localX (orientedSquare t a b) p=p.1*Real.cos t+p.2*Real.sin t-a := by
  dsimp [localX,orientedSquare]
  linear_combination -a*(Real.sin_sq_add_cos_sq t)

lemma orientedSquare_localY (t a b : ℝ) (p : Point) :
    localY (orientedSquare t a b) p= -p.1*Real.sin t+p.2*Real.cos t-b := by
  dsimp [localY,orientedSquare]
  linear_combination -b*(Real.sin_sq_add_cos_sq t)

@[simp] lemma orientedSquare_alpha (t a b : ℝ) : alpha (orientedSquare t a b) (0,0)=|a| := by
  simp [alpha,orientedSquare_localX]

@[simp] lemma orientedSquare_beta (t a b : ℝ) : beta (orientedSquare t a b) (0,0)=|b| := by
  simp [beta,orientedSquare_localY]

/-- In its own frame, the centre of `orientedSquare t a b` has first coordinate
`a`. -/
lemma oriented_frame_centerX (t a b : ℝ) :
    frameX (orientedSquare t a b) (sub (orientedSquare t a b).center (0,0))=a := by
  dsimp [frameX,orientedSquare,sub]
  linear_combination a*(Real.sin_sq_add_cos_sq t)

/-- At the phase `0` the oriented square is axis-parallel. -/
lemma orientedSquare_zero (a b : ℝ) : orientedSquare 0 a b=axisSquare (a,b) := by
  simp [orientedSquare,axisSquare]

lemma orientedSquare_eq_modelSquare (t a b : ℝ) :
    orientedSquare t a b=modelSquare (0,0) (t : Direction) (a,b) := by
  unfold orientedSquare modelSquare
  congr 1
  simp only [pointInDirection,Real.Angle.cos_coe,Real.Angle.sin_coe]
  ext <;> ring

lemma Represents.closed {S : UnitSquare} {o : Point} {φ : Direction} {c : Point}
    (h : Represents S o φ c) (x y : ℝ) :
    closedSquare S (pointInDirection o φ x y) ↔ closedAxisSquare c x y := by
  have hopen : ∀ p, openSquare S p ↔ openSquare (modelSquare o φ c) p := by
    intro p
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    have hm := modelSquare_local o φ c q.1 q.2
    rw [frameEquiv_apply]
    simp only [openSquare,hm.1,hm.2]
    exact h q.1 q.2
  have hc := same_open_same_closed S (modelSquare o φ c) hopen
  simpa only [closedSquare,(modelSquare_local o φ c x y).1,
    (modelSquare_local o φ c x y).2] using hc (pointInDirection o φ x y)

/-- Non-overlap turns any assignment to the model's slots into a permutation:
the configuration is congruent to the axis-parallel squares at the slots. -/
lemma congruent_of_slots {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    {φ : Direction} {c : Fin n → Point} (hd : InteriorDisjoint S)
    (h : ∀ i, ∃ j, Represents (S i) o φ (c j)) :
    Congruent S o (fun i => axisSquare (c i)) := by
  classical
  choose f hf using h
  have hi : Function.Injective f := by
    intro i j hij
    by_contra hne
    let z := pointInDirection o φ (c (f i)).1 (c (f i)).2
    have hz₁ : openSquare (S i) z := (hf i _ _).mpr (by simp [openAxisSquare])
    have hz₂ : openSquare (S j) z := (hf j _ _).mpr (by rw [← hij]; simp [openAxisSquare])
    exact hd i j hne z ⟨hz₁,hz₂⟩
  let e := Equiv.ofBijective f hi.bijective_of_finite
  refine ⟨φ,e.symm,?_⟩
  intro i p
  have hh : Represents (S (e.symm i)) o φ (c i) := by
    simpa only [show f (e.symm i)=i from e.apply_symm_apply i] using hf (e.symm i)
  rw [axisSquare_open,axisSquare_closed]
  exact ⟨hh p.1 p.2,hh.closed p.1 p.2⟩

/-- A configuration congruent to a packing of the disk of radius `R` about the
origin packs the disk of radius `R` about its own centre. -/
theorem Congruent.packing {n : ℕ} {S M : Fin n → UnitSquare} {o : Point} {R : ℝ}
    (h : Congruent S o M) (hM : Packing M (0,0) R) : Packing S o R := by
  obtain ⟨φ,σ,hφ⟩ := h
  refine ⟨hM.1,fun j p hj => ?_,fun j k hjk p hp => ?_⟩
  · obtain ⟨i,rfl⟩ := σ.surjective j
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    have hd := frameEquiv_distance o φ q (0,0)
    rw [frameEquiv_zero] at hd
    change normSq _ ≤ R^2
    rw [hd]
    exact hM.2.1 i q ((hφ i q).2.mp hj)
  · obtain ⟨i,rfl⟩ := σ.surjective j
    obtain ⟨l,rfl⟩ := σ.surjective k
    obtain ⟨q,rfl⟩ := (frameEquiv o φ).surjective p
    exact hM.2.2 i l (fun h => hjk (by rw [h])) q ⟨(hφ i q).1.mp hp.1,(hφ l q).1.mp hp.2⟩

/-- Congruence, with its frame replaced by an explicit isometry of the plane. -/
lemma Congruent.rigid_witness {n : ℕ} {S M : Fin n → UnitSquare} {o : Point}
    (h : Congruent S o M) :
    ∃ (e : Point ≃ Point) (σ : Equiv.Perm (Fin n)), e (0,0)=o ∧
      (∀ p q, normSq (sub (e p) (e q))=normSq (sub p q)) ∧
      (∀ i p, (openSquare (S (σ i)) (e p) ↔ openSquare (M i) p) ∧
        (closedSquare (S (σ i)) (e p) ↔ closedSquare (M i) p)) := by
  obtain ⟨φ,σ,hφ⟩ := h
  exact ⟨frameEquiv o φ,σ,frameEquiv_zero o φ,frameEquiv_distance o φ,hφ⟩

lemma chart_represents {S : UnitSquare} {o : Point} (C : SquareChart S o) :
    Represents S o C.phase (C.a,C.signedB) := C.cartesian

end SquaresInCircles
