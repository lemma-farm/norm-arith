module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Section3
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Lemma2
public import Examples.sthubbar__goldbach_lean.Dependencies.v3565c12e4b5c.LeanLab.HeathBrown1985.Bound24
/-!
P0096 Heath-Brown 1985, page 54: `Σ₂ ≪ L x Σ_{k ≤ uv} k⁻¹ δ₁(x, k, Q)`, hence by Lemma 2
`Σ₂ ≪ x² Q^{-1/2} L⁸`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
end LeanLab.HeathBrown1985
