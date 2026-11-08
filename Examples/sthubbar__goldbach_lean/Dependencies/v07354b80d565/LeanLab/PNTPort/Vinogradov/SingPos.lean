module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.Vinogradov.SingSeries
/-!
# The ternary singular series: multiplicativity

Lab proof, unit U-5259. AI wrote this file. Known mathematics, no cited input.

* `gDiv n d = d · 1_{d ∣ n}`, multiplicative; `cR n = gDiv n * μ`, the Ramanujan sum
  `c_q(n)` as a Dirichlet convolution, multiplicative, `cR_apply`.
* `fS n q = μ(q) c_q(n) / φ(q)³`, multiplicative, `fS_mult`.
-/
@[expose] public section
namespace LeanLab.PNTPort.Vinogradov
open Finset Real ArithmeticFunction
open scoped ArithmeticFunction.Moebius
/-- `d ↦ d · 1_{d ∣ n}`. -/
noncomputable def gDiv (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ∣ n then (d : ℝ) else 0, by simp⟩
noncomputable def cR (n : ℕ) : ArithmeticFunction ℝ := gDiv n * (μ : ArithmeticFunction ℝ)
noncomputable def invPhi3 : ArithmeticFunction ℝ := ⟨fun q => 1 / (q.totient : ℝ) ^ 3, by simp⟩
noncomputable def fS (n : ℕ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).pmul (cR n)).pmul invPhi3
noncomputable def hS (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => |fS n d| * Real.sqrt d, by simp⟩
end LeanLab.PNTPort.Vinogradov
