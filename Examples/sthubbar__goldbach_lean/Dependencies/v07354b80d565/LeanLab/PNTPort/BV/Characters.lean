module
public import Mathlib
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.HeathBrown1985.Statements
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.LargeSieve.Multiplicative
/-!
# From residue classes to primitive characters

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `psi_orth`: `φ(q) ψ(x; q, a) = ∑_χ conj(χ a) ψ(x, χ)` for `(a, q) = 1`.
* `abs_psi_sub_le`: `|ψ(x; q, a) - x/φ(q)| ≤ (‖ψ(x, χ₀) - x‖ + ∑_{χ ≠ χ₀} ‖ψ(x, χ)‖) / φ(q)`.
* `norm_psiChi_sub_primitive`: `‖ψ(x, χ) - ψ(x, χ*)‖ ≤ ∑_{n ≤ x, (n, q) > 1} Λ(n)`, `χ*` the
  primitive character inducing `χ`, and the same bound for `‖ψ(x, χ₀) - ψ(x)‖`.
-/
@[expose] public section
namespace LeanLab.PNTPort.BV
open Finset Real ArithmeticFunction
end LeanLab.PNTPort.BV
