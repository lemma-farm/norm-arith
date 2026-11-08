module

public import SquaresInCircles.Common.Basic

/-!
# Axis-parallel squares

Axis-parallel unit squares centred at given points: membership, and the
disjointness and disk-containment tests of the optimal models.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

/-- `(x, y)` lies in the open, or the closed, axis-parallel unit square at `c`. -/
abbrev openAxisSquare (c : Point) (x y : ℝ) : Prop :=
  |x - c.1| < 1 / 2 ∧ |y - c.2| < 1 / 2
abbrev closedAxisSquare (c : Point) (x y : ℝ) : Prop :=
  |x - c.1| ≤ 1 / 2 ∧ |y - c.2| ≤ 1 / 2

lemma axisSquare_open (c p : Point) :
    openSquare (axisSquare c) p ↔ openAxisSquare c p.1 p.2 := by
  simp [axisSquare,openSquare,openAxisSquare,localX,localY]

lemma axisSquare_closed (c p : Point) :
    closedSquare (axisSquare c) p ↔ closedAxisSquare c p.1 p.2 := by
  simp [axisSquare,closedSquare,closedAxisSquare,localX,localY]

def AxisSeparated (p q : Point) : Prop :=
  p.1+1 ≤ q.1 ∨ q.1+1 ≤ p.1 ∨ p.2+1 ≤ q.2 ∨ q.2+1 ≤ p.2

lemma axis_disjoint {p q : Point} (hs : AxisSeparated p q) :
    ∀ x, ¬ (openSquare (axisSquare p) x ∧ openSquare (axisSquare q) x) := by
  rintro x ⟨hp,hq⟩
  simp only [axisSquare_open,openAxisSquare,abs_lt] at hp hq
  rcases hs with h | h | h | h <;> linarith [hp.1.1,hp.1.2,hp.2.1,hp.2.2,
    hq.1.1,hq.1.2,hq.2.1,hq.2.2]

/-- Axis-parallel unit squares at pairwise separated centres, each inside the
disk of radius `R` about the origin, form a packing. -/
lemma axis_packing {n : ℕ} {c : Fin n → Point} {R : ℝ} (hR : 0 ≤ R)
    (hsep : ∀ i j, i ≠ j → AxisSeparated (c i) (c j))
    (hin : ∀ i, (|(c i).1|+1/2)^2+(|(c i).2|+1/2)^2 ≤ R^2) :
    Packing (fun i => axisSquare (c i)) (0,0) R :=
  ⟨hR,fun i _ => inDisk_of_phi_le (by simpa [phi,alpha,beta,localX,localY,axisSquare] using hin i),
    fun i j hij => axis_disjoint (hsep i j hij)⟩

end SquaresInCircles
