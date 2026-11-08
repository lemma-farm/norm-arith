import Examples.jconorgrogan__prime_minor_arcs_2_15.Dependencies.v6c9d842eb95c.ShiuFoundation
import Mathlib.Data.Nat.Choose.Bounds
/-!
# Kernel-checked analytic hypotheses for the divisor-square weight

This file proves elementary growth facts which are genuine hypotheses in
Shiu's theorem.  It does not postulate or claim the progression estimate or
Mertens' theorem.
-/
namespace ShiuAnalyticLayer
open ArithmeticFunction MixedMellinCert ShiuFoundation
open scoped ArithmeticFunction.zeta BigOperators
noncomputable section
def primeReciprocalSum (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (p : ℝ)⁻¹
end
end ShiuAnalyticLayer
