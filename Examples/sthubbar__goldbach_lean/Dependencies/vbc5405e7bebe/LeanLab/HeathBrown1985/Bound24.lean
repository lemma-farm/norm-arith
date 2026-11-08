module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.HeathBrown1985.Lemma1
/-!
P0096 Heath-Brown 1985, 2.4 from the Siegel-Walfisz theorem 1.1, as on page 48.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Real Finset
open scoped ArithmeticFunction.vonMangoldt Nat
attribute [local instance] Classical.propDecidable
end LeanLab.HeathBrown1985
