module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.BV.Vaughan
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.BV.Characters
/-!
# Vaughan's decomposition of ψ(x, χ)

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

`psiChi_decomp`: `ψ(x, χ) = S₁ - S₂ + S₃ - S₄` with the four Vaughan sums below, for any
Dirichlet character `χ` and any `u`, `v ≥ 1`.
-/
@[expose] public section
namespace LeanLab.PNTPort.BV
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius
variable {q : ℕ} (x : ℝ) (u v : ℕ) (χ : DirichletCharacter ℂ q)
/-- The truncated Möbius sum `g_v(k) = ∑_{d ∣ k, d ≤ v} μ(d)`. -/
noncomputable def gV (v k : ℕ) : ℝ := ∑ d ∈ k.divisors, (if d ≤ v then (μ d : ℝ) else 0)
end LeanLab.PNTPort.BV
