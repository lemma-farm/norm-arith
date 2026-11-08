module
public import Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Annulus
public import Mathlib
/-!
# Basic planar geometry for the quantitative overlap theorem

Coordinates in the plane, the quarter-turn `J`, orthonormal frames (which are
measure preserving), elementary facts about planks (center line, angle), and indexed
families of planks with their counting function, hole and excess-overlap cost.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
/-! ### Numerical constants of the proof -/
lemma inner_eq_coord (x y : Plane) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring
lemma norm_sq_eq_coord (x : Plane) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]
lemma norm_eq_coord (x : Plane) : ‖x‖ = √(x 0 ^ 2 + x 1 ^ 2) := by
  rw [← norm_sq_eq_coord, Real.sqrt_sq (norm_nonneg _)]
/-- The quarter turn `J(x₀, x₁) = (-x₁, x₀)`. -/
def J (x : Plane) : Plane := WithLp.toLp 2 ![-x 1, x 0]
@[simp] lemma J_apply_zero (x : Plane) : J x 0 = -x 1 := by simp [J]
@[simp] lemma J_apply_one (x : Plane) : J x 1 = x 0 := by simp [J]
lemma ext_coord {x y : Plane} (h0 : x 0 = y 0) (h1 : x 1 = y 1) : x = y := by
  ext i; fin_cases i <;> simp [h0, h1]
lemma inner_J_self (x : Plane) : inner ℝ (J x) x = 0 := by
  rw [inner_eq_coord]; simp; ring
lemma norm_J (x : Plane) : ‖J x‖ = ‖x‖ := by
  rw [norm_eq_coord, norm_eq_coord]; simp [add_comm]
/-- In the plane, `⟪x,y⟫² + ⟪Jx,y⟫² = ‖x‖²‖y‖²`. -/
lemma inner_sq_add_inner_J_sq (x y : Plane) :
    inner ℝ x y ^ 2 + inner ℝ (J x) y ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rw [inner_eq_coord, inner_eq_coord, norm_sq_eq_coord, norm_sq_eq_coord]; simp; ring
/-- Decomposition of a vector in the orthonormal frame `(e, Je)`. -/
lemma decomp_frame {e : Plane} (he : ‖e‖ = 1) (x : Plane) :
    x = inner ℝ x e • e + inner ℝ x (J e) • J e := by
  have h := norm_sq_eq_coord e
  rw [he] at h
  apply ext_coord
  · simp [inner_eq_coord]; linear_combination (x 0) * h
  · simp [inner_eq_coord]; linear_combination (x 1) * h
/-! ### Orthonormal frames -/
namespace Plank
/-- The offset `(a + b)/2` of the center line. -/
def mid (P : Plank) : ℝ := (P.a + P.b) / 2
/-- The center line `ℓ_P = {x : ⟪x, n⟫ = (a + b)/2}`. -/
def centerLine (P : Plank) : Set Plane := {x | inner ℝ x P.n = P.mid}
/-- The acute angle between the center lines of two planks (`0` if parallel). -/
def ang (P Q : Plank) : ℝ := Real.arccos |inner ℝ P.n Q.n|
lemma abs_inner_n_le (P Q : Plank) : |inner ℝ P.n Q.n| ≤ 1 := by
  have := abs_real_inner_le_norm P.n Q.n
  rwa [P.norm_n, Q.norm_n, mul_one] at this
end Plank
/-! ### Indexed families of planks -/
section Families
variable {ι : Type*} [Fintype ι]
end Families
end Annulus
end
