module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Cardinal.Strong.ArctanQuadrature
public import Mathlib
@[expose] public section
/-! Executable rational arctangent values with uniform certified precision.
Every value below is a finite rational calculation; its error against the
ACTUAL arctangent is proved rather than supplied by an approximation oracle.
-/
namespace MeyerGeneralProblem.StrongParity
/-- The literal finite rational left endpoint quadrature. -/
def rationalArctanQuadrature (q : ℚ) (N : ℕ) : ℚ :=
  q / N * ∑ i ∈ Finset.range N, 1 / (1 + (q / N * i) ^ 2)
/-- A definite positive grid size, scaling precision by the actual numerator. -/
def rationalArctanGridSize (q : ℚ) (p : ℕ) : ℕ := (q.num.natAbs + 1) * 2 ^ p
/-- The executable rational arctangent approximation at binary precision `p`. -/
def rationalArctanApprox (q : ℚ) (p : ℕ) : ℚ :=
  rationalArctanQuadrature q (rationalArctanGridSize q p)
noncomputable section
theorem rationalArctanQuadrature_cast (q : ℚ) (N : ℕ) :
    (rationalArctanQuadrature q N : ℝ) = arctanQuadratureLeft q N := by
  dsimp [rationalArctanQuadrature, arctanQuadratureLeft, arctanGridIntegrand]
  push_cast
  rfl
theorem rationalArctanGridSize_pos (q : ℚ) (p : ℕ) : 0 < rationalArctanGridSize q p := by
  dsimp [rationalArctanGridSize]
  positivity
/-- The actual numerator gives a definite arithmetic magnitude bound. -/
theorem rational_abs_le_numerator_size (q : ℚ) :
    |(q : ℝ)| ≤ ((q.num.natAbs + 1 : ℕ) : ℝ) := by
  have hd : 0 < (q.den : ℝ) := Nat.cast_pos.mpr q.den_pos
  have hd1 : 1 ≤ (q.den : ℝ) := by exact_mod_cast q.den_pos
  have hn : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [Rat.cast_def, abs_div, abs_of_pos hd, hn]
  apply (div_le_iff₀ hd).mpr
  push_cast
  have hm := Nat.cast_nonneg (α := ℝ) q.num.natAbs
  nlinarith
/-- Uniform actual error for EVERY signed rational input and requested precision. -/
theorem rationalArctanApprox_error (q : ℚ) (p : ℕ) :
    |(rationalArctanApprox q p : ℝ) - Real.arctan (q : ℝ)| ≤ 1 / (2 : ℝ) ^ p := by
  rw [rationalArctanApprox, rationalArctanQuadrature_cast]
  have hN := rationalArctanGridSize_pos q p
  have hNR : 0 < (rationalArctanGridSize q p : ℝ) := Nat.cast_pos.mpr hN
  have hM : (q.num.natAbs + 1 : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ |(q : ℝ)| / rationalArctanGridSize q p := arctanQuadratureLeft_error _ hN
    _ ≤ ((q.num.natAbs + 1 : ℕ) : ℝ) / rationalArctanGridSize q p :=
      div_le_div_of_nonneg_right (rational_abs_le_numerator_size q) hNR.le
    _ = _ := by
      dsimp [rationalArctanGridSize]
      push_cast
      field_simp [hM]
end
end MeyerGeneralProblem.StrongParity
