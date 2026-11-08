module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Sigma1Abel
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Sigma2
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.DivMoments
/-!
P0096 Heath-Brown 1985, page 54, the bound 3.2: Σ₁ ≪ x² L⁶ Q⁻¹ for Q = L^B.
PROVED here: bound3_2_of, Bound3_2 from Lemma 1, 2.7, alone, and bound3_2_of_siegelWalfisz.
Route: partial summation in Sigma1Abel.lean reduces each inner sum to the progression sums
of Δ_Q up to t ≤ x; these are bounded by 2.7 for t > √x and trivially for t ≤ √x; the sum
over m of (c, m) is at most 2x d(c), and Σ_{c ≤ Q} d(c)²/c ≤ (1 + log Q)⁴ from DivMoments.lean.
Lemma 1 is used with A = 2B + 5; the range 2 ≤ x ≤ X0 is handled by a crude bound.
AI-written Lean code, Claude, run 20261017T0303Z-29152. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset Filter
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
end LeanLab.HeathBrown1985
