module

public import SquaresInCircles.Common.Separation
public import SquaresInCircles.Common.Arcs

/-!
# The radial sweep

The radial sweep of a square is the union of its translates along the ray from
the disk centre through its centre. If the centres of two squares with disjoint
interiors are within distance 1 of the disk centre, the separating functional of
`support_separator` keeps the sweep of either square away from the other
(`safe_openRay_of_disjoint`): along every direction, the disk centre is within
the sum of the two widths of each centre. Of two or more disjoint squares at
most one contains the disk centre, and in the angular budget it can be replaced
by its sweep (`ray_budget_impossible`).
-/

@[expose] public section

noncomputable section
open Set
namespace SquaresInCircles

/-- If the centre of `S` is within distance 1 of `o`, then in every direction
`n` the disk centre is within the sum of the widths of `S` and of any `T` from
`c_S`. -/
lemma dot_center_le (S T : UnitSquare) (o n : Point) (h : normSq (sub S.center o) ≤ 1) :
    |dot n (sub S.center o)| ≤ width S n+width T n := by
  have hn := Real.abs_le_sqrt ((cauchy_sq n (sub S.center o)).trans
    (mul_le_of_le_one_right (normSq_nonneg n) h))
  have hS := width_lower S n
  have hT := width_lower T n
  unfold width
  linarith

/-- Union of translates of the *open* square along the ray away from `o`. -/
def openRay (S : UnitSquare) (o : Point) : Set Point :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ ∃ q, openSquare S q ∧
    p = add q (scale t (sub S.center o))}

lemma Separation.center_signs {S T : UnitSquare} (e : Separation S T) (o : Point)
    (hS : normSq (sub S.center o) ≤ 1) (hT : normSq (sub T.center o) ≤ 1) :
    dot e.normal (sub S.center o) ≤ 0 ∧ 0 ≤ dot e.normal (sub T.center o) := by
  have h₁ := dot_center_le S T o e.normal hS
  have h₂ := dot_center_le T S o e.normal hT
  have hsep := e.separates
  rcases abs_le.mp h₁ with ⟨h₁a,h₁b⟩
  rcases abs_le.mp h₂ with ⟨h₂a,h₂b⟩
  simp only [dot_sub_right] at *
  exact ⟨by linarith,by linarith⟩

/-- The radial sweep of `S` misses a square `T` with a disjoint interior when both
centres are within distance 1 of `o`. -/
theorem safe_openRay_of_disjoint (S T : UnitSquare) (o : Point)
    (hd : ∀ p, ¬ (openSquare S p ∧ openSquare T p))
    (hS : normSq (sub S.center o) ≤ 1) (hT : normSq (sub T.center o) ≤ 1) :
    Disjoint (openRay S o) {p | openSquare T p} := by
  obtain ⟨e⟩ := support_separator S T hd
  rw [Set.disjoint_left]
  rintro p ⟨t,ht,q,hq,rfl⟩ hp
  have hsign := e.center_signs o hS hT
  have hmove := mul_nonpos_of_nonneg_of_nonpos ht hsign.1
  have hqB := (abs_lt.mp (dot_open_bound_of_ne S e.nonzero hq)).2
  have hpB := (abs_lt.mp (dot_open_bound_of_ne T e.nonzero hp)).1
  have hsep := e.separates
  simp only [dot_sub_right,dot_add_right,dot_scale_right] at *
  linarith

/-- Of two or more disjoint squares, some square does not contain `o`. -/
lemma exists_exterior {n : ℕ} (hn : 2 ≤ n) {S : Fin n → UnitSquare} (hd : InteriorDisjoint S)
    (o : Point) : ∃ i, ¬ openSquare (S i) o := by
  by_contra h
  push Not at h
  exact hd ⟨0,by omega⟩ ⟨1,by omega⟩ (by simp [Fin.ext_iff]) o ⟨h _,h _⟩

/-- The radial sweep of a square containing `o`, and any other square itself. -/
def rayRegions {n : ℕ} (S : Fin n → UnitSquare) (o : Point) (i : Fin n) : Set Point :=
  by
    classical
    exact if openSquare (S i) o then openRay (S i) o else {p | openSquare (S i) p}

lemma rayRegions_disjoint {n : ℕ} {S : Fin n → UnitSquare} {o : Point}
    (hd : InteriorDisjoint S) (hc : ∀ i, normSq (sub (S i).center o) ≤ 1) :
    Pairwise (fun i j => Disjoint (rayRegions S o i) (rayRegions S o j)) := by
  classical
  intro i j hij
  by_cases hi : openSquare (S i) o <;> by_cases hj : openSquare (S j) o <;>
    simp only [rayRegions,hi,hj,ite_true,ite_false]
  · exact False.elim (hd i j hij o ⟨hi,hj⟩)
  · exact safe_openRay_of_disjoint (S i) (S j) o (hd i j hij) (hc i) (hc j)
  · exact (safe_openRay_of_disjoint (S j) (S i) o (hd j i hij.symm) (hc j) (hc i)).symm
  · exact hd.pairwise hij

/-- `n ≥ 2` disjoint squares with centres within distance 1 of `o` cannot all
hold arcs of half-width at least `π/n` in their regions, strictly more for the
squares that do not contain `o`. -/
theorem ray_budget_impossible {n : ℕ} (hn : 2 ≤ n) {S : Fin n → UnitSquare} {o : Point}
    {r : ℝ} (hd : InteriorDisjoint S) (hc : ∀ i, normSq (sub (S i).center o) ≤ 1)
    (hin : ∀ i, openSquare (S i) o →
      ∃ A : OpenArc o r (openRay (S i) o), Real.pi/n ≤ A.halfWidth)
    (hex : ∀ i, ¬ openSquare (S i) o →
      ∃ A : OpenArc o r {p | openSquare (S i) p}, Real.pi/n < A.halfWidth) : False := by
  classical
  have harcs : ∀ i, ∃ A : OpenArc o r (rayRegions S o i), Real.pi/n ≤ A.halfWidth ∧
      (¬ openSquare (S i) o → Real.pi/n < A.halfWidth) := by
    intro i
    by_cases hi : openSquare (S i) o
    · rw [show rayRegions S o i = openRay (S i) o from ite_eq_left hi]
      obtain ⟨A,hA⟩ := hin i hi
      exact ⟨A,hA,fun h => (h hi).elim⟩
    · rw [show rayRegions S o i = {p | openSquare (S i) p} from ite_eq_right hi]
      obtain ⟨A,hA⟩ := hex i hi
      exact ⟨A,hA.le,fun _ => hA⟩
  choose A hA hstrict using harcs
  obtain ⟨i,hi⟩ := exists_exterior hn hd o
  exact uniform_arc_excess A (rayRegions_disjoint hd hc) hA ⟨i,hstrict i hi⟩

end SquaresInCircles
