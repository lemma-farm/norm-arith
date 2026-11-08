module
public import Mathlib
/-!
P0096 Heath-Brown 1985, Vaughan's identity 3.1 on page 53:
for `u, v ≥ 1`, `Σ_{v < n ≤ N} f(n) Λ(n) = S₁ - S₂ - S₃`. Here `u, v` are read as integers
`U, V ≥ 1`; for real `u, v` take `U = ⌊u⌋`, `V = ⌊v⌋`, every condition `c ≤ u` being `c ≤ ⌊u⌋`.
AI-written Lean code, Claude, run 20261017T0003Z-10827. Checked only by the Lean kernel.
-/
@[expose] public section
noncomputable section
namespace LeanLab.HeathBrown1985
open Finset
open ArithmeticFunction (coe_mul_zeta_apply one_apply_ne coe_moebius_mul_coe_zeta intCoe_apply
  vonMangoldt_mul_zeta log)
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ArithmeticFunction.zeta
attribute [local instance] Classical.propDecidable
end LeanLab.HeathBrown1985
