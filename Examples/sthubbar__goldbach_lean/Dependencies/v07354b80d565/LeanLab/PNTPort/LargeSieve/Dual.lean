module
public import Examples.sthubbar__goldbach_lean.Dependencies.v07354b80d565.LeanLab.PNTPort.LargeSieve.Basic
/-!
# The large sieve inequality, dual form and main form

Lab proof, unit U-5000. AI wrote this file. Known mathematics, no cited input.

* `dual_large_sieve`: `∑_{M<n≤M+N} ‖∑_r b_r e(n α_r)‖² ≤ (N + 2/δ) ∑_r ‖b_r‖²`.
* `large_sieve`: `∑_r ‖∑_{M<n≤M+N} a_n e(n α_r)‖² ≤ (N + 2/δ) ∑_n ‖a_n‖²`.

Both for points `α_r` that are `δ`-spaced modulo one, `Spaced s α δ`, with `δ > 0`.
-/
@[expose] public section
namespace LeanLab.PNTPort.LargeSieve
open Complex Finset Real
variable {ι : Type*} [DecidableEq ι]
noncomputable def G (m : ℕ) (θ : ℝ) : ℂ := ∑ k ∈ range m, e (k * θ)
end LeanLab.PNTPort.LargeSieve
