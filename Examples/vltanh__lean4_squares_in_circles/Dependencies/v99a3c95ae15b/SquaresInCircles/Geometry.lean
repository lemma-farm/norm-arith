module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
/-!
# The statement: squares, disks, packings, congruence and the optimal models

Everything the main theorems (`SquaresInCircles.lean`) state: unit squares, each
with its own position and rotation; packings in a closed disk; congruence to a
model given about the origin; and the optimal radius and models of each case.
`Packing` asks only that the closed squares lie in the disk and that no point
lie in two open squares (`openSquare`, with strict inequalities).

`Challenge.lean` restates this file word for word, and Comparator checks that
the two elaborate identically. That needs every definition here, in this
order: Lean names the auxiliary lemmas inside a definition, such as the proof
of `Nat.AtLeastTwo 2` behind the real numeral `2`, after the first definition
in the file that needs them. Edit here only:
`scripts/verify-comparator.sh --write` copies the definitions into
`Challenge.lean`.
-/
@[expose] public section
noncomputable section
namespace SquaresInCircles
/-! ### Squares, disks, packings and congruence -/
/-- A point of the plane, by its two real coordinates. -/
abbrev Point := ℝ × ℝ
/-- The squared Euclidean length `x ^ 2 + y ^ 2` of `p = (x, y)`. -/
def normSq (p : Point) : ℝ := p.1 ^ 2 + p.2 ^ 2
/-- The difference `p - q`, coordinate by coordinate. -/
def sub (p q : Point) : Point := (p.1 - q.1, p.2 - q.2)
/-- A unit square, by its centre and the orthonormal frame formed by the
columns `(cosine,sine)` and `(-sine,cosine)`: the square is turned by the angle
whose cosine is `cosine` and whose sine is `sine`. -/
structure UnitSquare where
  center : Point
  cosine : ℝ
  sine : ℝ
  unit : cosine ^ 2 + sine ^ 2 = 1
/-- The first coordinate of `p` in the frame of `S`, measured from its centre. -/
def localX (S : UnitSquare) (p : Point) : ℝ :=
  S.cosine * (p.1 - S.center.1) + S.sine * (p.2 - S.center.2)
/-- The second coordinate of `p` in the frame of `S`, measured from its centre. -/
def localY (S : UnitSquare) (p : Point) : ℝ :=
  -S.sine * (p.1 - S.center.1) + S.cosine * (p.2 - S.center.2)
/-- `p` lies in the closed unit square `S`: both of its coordinates in the frame
of `S` are in `[-1/2, 1/2]`. -/
def closedSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| ≤ 1 / 2 ∧ |localY S p| ≤ 1 / 2
/-- `p` lies in the interior of `S`: both of its coordinates in the frame of `S`
are in `(-1/2, 1/2)`. -/
def openSquare (S : UnitSquare) (p : Point) : Prop :=
  |localX S p| < 1 / 2 ∧ |localY S p| < 1 / 2
/--
Membership in the closed disk of centre `o` and radius `R`, intended for
`0 ≤ R`. The squared form means `inDisk o R p` and `inDisk o (-R) p` agree, so
for negative `R` this is the disk of radius `|R|` rather than an empty set.
Every use here goes through `Packing`, whose first conjunct supplies `0 ≤ R`.
-/
def inDisk (o : Point) (R : ℝ) (p : Point) : Prop :=
  normSq (sub p o) ≤ R ^ 2
/-- `n` unit squares packed in the closed disk of centre `o` and radius `R`:
the radius is nonnegative, every closed square lies in the closed disk, and no
point is interior to two different squares. -/
def Packing {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (R : ℝ) : Prop :=
  0 ≤ R ∧
  (∀ i p, closedSquare (S i) p → inDisk o R p) ∧
  (∀ i j, i ≠ j → ∀ p, ¬ (openSquare (S i) p ∧ openSquare (S j) p))
/-- A direction in the plane: an angle modulo `2 * π`. -/
abbrev Direction := Real.Angle
namespace One
end One
namespace Two
end Two
namespace Three
end Three
namespace Four
end Four
namespace Five
end Five
namespace Six
end Six
namespace Seven
end Seven
end SquaresInCircles
