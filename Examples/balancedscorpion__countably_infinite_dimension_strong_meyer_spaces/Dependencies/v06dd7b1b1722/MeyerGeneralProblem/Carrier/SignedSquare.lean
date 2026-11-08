module
public import Examples.balancedscorpion__countably_infinite_dimension_strong_meyer_spaces.Dependencies.v06dd7b1b1722.MeyerGeneralProblem.Carrier.StrictSubcritical
public import Mathlib
@[expose] public section
/-!
# Signed-square coordinates

The change of variables `s = x |x|` converts the subcritical density inequality
into uniform tail separation. Elementary lemmas are kept explicit so that the
negative-tail ratio split cannot be hidden in an asymptotic assertion.
-/
namespace MeyerGeneralProblem
/-- The odd, strictly increasing signed-square coordinate. -/
def signedSquare (x : ℝ) : ℝ := x * |x|
@[simp]
theorem abs_signedSquare (x : ℝ) : |signedSquare x| = |x| ^ 2 := by
  unfold signedSquare
  rw [abs_mul, abs_abs]
  ring
end MeyerGeneralProblem
