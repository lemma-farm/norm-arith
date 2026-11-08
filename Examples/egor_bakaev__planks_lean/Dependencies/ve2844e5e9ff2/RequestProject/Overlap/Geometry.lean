module
public import Examples.egor_bakaev__planks_lean.Dependencies.ve2844e5e9ff2.RequestProject.Overlap.Defs
public import Mathlib
/-!
# Elementary planar geometry for the overlap theorem

Angle and sine facts for center lines, intersection of two lines, and the
distance from a point to a center line.
-/
@[expose] public section
open MeasureTheory Set Metric Real
open scoped ENNReal
noncomputable section
namespace Annulus
/-! ### Unit vectors -/
namespace Plank
lemma inner_sq_add (P Q : Plank) : inner ℝ P.n Q.n ^ 2 + inner ℝ (J P.n) Q.n ^ 2 = 1 := by
  have h := inner_sq_add_inner_J_sq P.n Q.n
  rwa [P.norm_n, Q.norm_n, one_pow, one_mul] at h
lemma ang_ne_zero_iff (P Q : Plank) : P.ang Q ≠ 0 ↔ inner ℝ (J P.n) Q.n ≠ 0 := by
  have h1 := P.abs_inner_n_le Q
  have h2 := P.inner_sq_add Q
  rw [ang, Ne, Real.arccos_eq_zero]
  constructor
  · intro h h'
    apply h
    rw [h'] at h2
    have : |inner ℝ P.n Q.n| ^ 2 = 1 := by rw [sq_abs]; linarith
    nlinarith [abs_nonneg (inner ℝ P.n Q.n)]
  · intro h h'
    apply h
    have : |inner ℝ P.n Q.n| = 1 := le_antisymm h1 h'
    have h3 : inner ℝ P.n Q.n ^ 2 = 1 := by rw [← sq_abs, this, one_pow]
    have : inner ℝ (J P.n) Q.n ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
lemma sin_ang_pos {P Q : Plank} (h : P.ang Q ≠ 0) : 0 < |inner ℝ (J P.n) Q.n| :=
  abs_pos.2 ((P.ang_ne_zero_iff Q).1 h)
lemma mem_centerLine {P : Plank} {x : Plane} : x ∈ P.centerLine ↔ inner ℝ x P.n = P.mid :=
  Iff.rfl
def crossPt (P Q : Plank) : Plane :=
  P.mid • P.n + ((Q.mid - P.mid * inner ℝ P.n Q.n) / inner ℝ (J P.n) Q.n) • J P.n
lemma crossPt_mem_left (P Q : Plank) : P.crossPt Q ∈ P.centerLine := by
  have h1 : inner ℝ P.n P.n = 1 := by rw [real_inner_self_eq_norm_sq, P.norm_n]; norm_num
  simp only [mem_centerLine, crossPt, inner_add_left, inner_smul_left, h1, inner_J_self,
    RCLike.conj_to_real]
  ring
lemma crossPt_mem_right {P Q : Plank} (h : P.ang Q ≠ 0) : P.crossPt Q ∈ Q.centerLine := by
  have hs := (P.ang_ne_zero_iff Q).1 h
  simp only [mem_centerLine, crossPt, inner_add_left, inner_smul_left, RCLike.conj_to_real]
  field_simp
  ring
end Plank
end Annulus
end
