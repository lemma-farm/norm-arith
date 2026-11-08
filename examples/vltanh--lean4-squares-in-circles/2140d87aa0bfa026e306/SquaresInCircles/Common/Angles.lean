module

public import SquaresInCircles.Common.Congruence
public import SquaresInCircles.Common.Arcs
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Directions on the circle

Sorted as reals `p 0 ≤ … ≤ p n`, `n+1` directions pairwise at least `g` apart
have neighbours at least `g` apart, and so are `p n` and `p 0+2π`; so `p i-i*g`
increases and ends at most `2π-(n+1)g` above where it starts. Hence
`(n+1)g ≤ 2π`, and if `(n+1)g = 2π` then `p i-i*g` is constant: the directions
form a regular polygon. Two directions at least `π` apart are
opposite, so disjoint half circles have opposite centres. A quarter turn of the
frame turns the centre of a square by a quarter turn.
-/

@[expose] public section

noncomputable section
namespace SquaresInCircles

lemma angle_ext {φ ψ : Direction} (hc : φ.cos=ψ.cos) (hs : φ.sin=ψ.sin) : φ=ψ := by
  induction φ using Real.Angle.induction_on
  induction ψ using Real.Angle.induction_on
  exact Real.Angle.cos_sin_inj hc hs

lemma antipodal_of_distance {φ ψ : Direction} (h : dist φ ψ=Real.pi) :
    ψ=φ+(Real.pi:Direction) := by
  rw [dist_comm,direction_dist,abs_eq Real.pi_pos.le] at h
  have he := Real.Angle.toReal_eq_pi_iff.1 (h.resolve_right (Real.Angle.neg_pi_lt_toReal _).ne')
  rw [← he]
  abel

/-- Disjoint arcs of half-width `π/2` on one circle have opposite centres. -/
lemma OpenArc.opposite {o : Point} {r : ℝ} {U V : Set Point} (A : OpenArc o r U)
    (B : OpenArc o r V) (hUV : Disjoint U V) (hA : A.halfWidth=Real.pi/2)
    (hB : B.halfWidth=Real.pi/2) : B.center=A.center+(Real.pi:Direction) := by
  refine antipodal_of_distance (le_antisymm ?_ ?_)
  · rw [direction_dist]; exact Real.Angle.abs_toReal_le_pi _
  · linarith [A.centers_separated B hUV]

/-- `n+1` directions pairwise at least `g` apart, sorted as reals
`p 0 ≤ … ≤ p n`: neighbours are at least `g` apart, and so are `p n` and
`p 0 + 2π`. -/
lemma sorted_directions {n : ℕ} {g : ℝ} (c : Fin (n+1) → Direction) (hg : g ≤ 2*Real.pi)
    (hsep : ∀ i j, i ≠ j → g ≤ dist (c i) (c j)) :
    ∃ (σ : Equiv.Perm (Fin (n+1))) (p : Fin (n+1) → ℝ), (∀ i, (p i : Direction)=c (σ i)) ∧
      (∀ i : Fin n, p i.castSucc+g ≤ p i.succ) ∧ p (Fin.last n)+g ≤ p 0+2*Real.pi := by
  let r : Fin (n+1) → ℝ := fun i => (c i).toReal
  let σ := Tuple.sort r
  let p : Fin (n+1) → ℝ := fun i => r (σ i)
  have hp : Monotone p := Tuple.monotone_sort r
  have hrepr (i : Fin (n+1)) : (p i : Direction)=c (σ i) := Real.Angle.coe_toReal _
  have hd {i j} (hij : i < j) : g ≤ p j-p i ∧ g ≤ 2*Real.pi-(p j-p i) := by
    have h := (hsep (σ j) (σ i) (σ.injective.ne hij.ne')).trans_eq (dist_eq_norm _ _)
    rw [← hrepr,← hrepr,← Real.Angle.coe_sub] at h
    have h0 : 0 ≤ p j-p i := sub_nonneg.mpr (hp hij.le)
    have h1 := direction_coe_norm_le (p j-p i)
    have h2 := direction_norm_wrapped (t := p j-p i) (by
      rw [abs_of_nonneg h0]
      linarith [(c (σ i)).neg_pi_lt_toReal,(c (σ j)).toReal_le_pi])
    rw [abs_of_nonneg h0] at h1 h2
    exact ⟨h.trans h1,h.trans h2⟩
  refine ⟨σ,p,hrepr,fun i => by linarith [(hd i.castSucc_lt_succ).1],?_⟩
  rcases (Fin.zero_le (Fin.last n)).lt_or_eq with h | h
  · linarith [(hd h).2]
  · rw [← h]
    linarith

/-- `n+1` directions pairwise at least `g` apart need `(n+1)g ≤ 2π`. -/
theorem directions_budget {n : ℕ} {g : ℝ} (c : Fin (n+1) → Direction) (hg : g ≤ 2*Real.pi)
    (hsep : ∀ i j, i ≠ j → g ≤ dist (c i) (c j)) : (n+1)*g ≤ 2*Real.pi := by
  obtain ⟨σ,p,-,hstep,hlast⟩ := sorted_directions c hg hsep
  have hq : Monotone fun i : Fin (n+1) => p i-i.val*g := Fin.monotone_iff_le_succ.2 fun i => by
    simp only [Fin.val_succ,Fin.val_castSucc,Nat.cast_succ]
    linarith [hstep i]
  have h := hq (Fin.zero_le (Fin.last n))
  simp only [Fin.val_last,Fin.val_zero,Nat.cast_zero,zero_mul,sub_zero] at h
  linarith

/-- If `(n+1)g = 2π`, then `n+1` directions pairwise at least `g` apart form a
regular polygon. -/
theorem regular_polygon {n : ℕ} {g : ℝ} (c : Fin (n+1) → Direction) (hg : (n+1)*g=2*Real.pi)
    (hsep : ∀ i j, i ≠ j → g ≤ dist (c i) (c j)) :
    ∃ (φ : Direction) (σ : Equiv.Perm (Fin (n+1))),
      ∀ i, c (σ i)=φ+(((i.val : ℝ)*g : ℝ) : Direction) := by
  obtain ⟨σ,p,hrepr,hstep,hlast⟩ := sorted_directions c
    (by nlinarith [Real.pi_pos,show (0:ℝ) ≤ n by positivity]) hsep
  let q : Fin (n+1) → ℝ := fun i => p i-i.val*g
  have hq : Monotone q := Fin.monotone_iff_le_succ.2 fun i => by
    simp only [q,Fin.val_succ,Fin.val_castSucc,Nat.cast_succ]
    linarith [hstep i]
  have hlast' : q (Fin.last n) ≤ q 0 := by
    simp only [q,Fin.val_last,Fin.val_zero,Nat.cast_zero,zero_mul,sub_zero]
    linarith
  refine ⟨c (σ 0),σ,fun i => ?_⟩
  have hi : q i=q 0 := le_antisymm ((hq (Fin.le_last i)).trans hlast') (hq (Fin.zero_le i))
  simp only [q,Fin.val_zero,Nat.cast_zero,zero_mul,sub_zero] at hi
  rw [← hrepr,eq_add_of_sub_eq hi,Real.Angle.coe_add,hrepr]

def quarterShift : Fin 4 → Direction :=
  ![0,((Real.pi/2:ℝ):Direction),(Real.pi:Direction),((-Real.pi/2:ℝ):Direction)]
def turnPoint : Fin 4 → Point → Point :=
  ![(fun p => p),(fun p => (-p.2,p.1)),(fun p => (-p.1,-p.2)),(fun p => (p.2,-p.1))]

/-- Some quarter turn takes a point to the closed first quadrant. -/
lemma quarter_nonnegative (c : Point) :
    ∃ k : Fin 4, 0 ≤ (turnPoint k c).1 ∧ 0 ≤ (turnPoint k c).2 := by
  rcases le_or_gt 0 c.1 with hx | hx <;> rcases le_or_gt 0 c.2 with hy | hy
  · exact ⟨0,by simpa [turnPoint] using And.intro hx hy⟩
  · exact ⟨1,by simpa [turnPoint] using And.intro (neg_nonneg.mpr hy.le) hx⟩
  · exact ⟨3,by simpa [turnPoint] using And.intro hy (neg_nonneg.mpr hx.le)⟩
  · exact ⟨2,by simpa [turnPoint] using And.intro (neg_nonneg.mpr hx.le) (neg_nonneg.mpr hy.le)⟩

lemma represents_quarter {S : UnitSquare} {o : Point} {φ : Direction} {c : Point}
    (k : Fin 4) (h : Represents S o (φ+quarterShift k) c) :
    Represents S o φ (turnPoint k c) := by
  intro x y
  rw [pointInDirection_transition o φ (φ+quarterShift k),h,add_sub_cancel_left]
  fin_cases k <;>
    simp [quarterShift,turnPoint,openAxisSquare,neg_div,Real.Angle.cos_coe,Real.Angle.sin_coe] <;>
    constructor <;> rintro ⟨h1,h2⟩ <;>
    obtain ⟨h1a,h1b⟩ := abs_lt.mp h1 <;> obtain ⟨h2a,h2b⟩ := abs_lt.mp h2 <;>
    exact ⟨abs_lt.mpr ⟨by linarith,by linarith⟩,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

lemma represents_cardinal {S : UnitSquare} {o : Point} {φ ψ : Direction} {c : Point}
    (h : Represents S o φ c) (k : Fin 4)
    (hc : (φ-ψ).cos=(quarterShift k).cos)
    (hs : (φ-ψ).sin=(quarterShift k).sin) :
    Represents S o ψ (turnPoint k c) := by
  have he : φ-ψ=quarterShift k := angle_ext hc hs
  have he' : φ=ψ+quarterShift k := by rw [← he]; abel
  rw [he'] at h
  exact represents_quarter k h

end SquaresInCircles
