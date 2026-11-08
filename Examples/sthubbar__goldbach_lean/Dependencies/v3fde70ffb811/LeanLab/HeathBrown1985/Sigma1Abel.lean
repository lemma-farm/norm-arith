module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v3fde70ffb811.LeanLab.HeathBrown1985.Section3
/-!
P0096 Heath-Brown 1985, page 54: the inner sum of S₁ for fixed m and c, rewritten with
n = m - c r as a sum over n ≤ x, n ≡ m mod c, of Δ_Q(n) log((m - n)/c), and bounded by
discrete partial summation against the antitone nonnegative weight log((m - n)/c).
PROVED here: abel_antitone, inner_S1_eq, abs_inner_S1_le.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
end LeanLab.HeathBrown1985
