module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.HeathBrown1985.Vaughan
public import Examples.sthubbar__goldbach_lean.Dependencies.vbc5405e7bebe.LeanLab.HeathBrown1985.Statements
/-!
P0096 Heath-Brown 1985, section 3, pages 53 to 55: the sum
`Σ = Σ_{2x < m ≤ 3x} |Σ_{n ≤ x} Δ_Q(n) Λ(m - n)|` split by Vaughan's identity 3.1 with
`N = 3x`, `u = Q`, `v = x Q⁻²`, `f(n) = Δ_Q(m - n)` for `m - x ≤ n < m`, else `0`.
PROVED here: `Σ ≤ Σ₁ + Σ₂ + Σ₃`. STATED: the bounds (3.2) for Σ₁ and the bound for Σ₂.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable
def mRange (x : ℝ) : Finset ℕ := (Icc 1 ⌊3 * x⌋₊).filter (fun m => 2 * x < (m : ℝ))
end LeanLab.HeathBrown1985
