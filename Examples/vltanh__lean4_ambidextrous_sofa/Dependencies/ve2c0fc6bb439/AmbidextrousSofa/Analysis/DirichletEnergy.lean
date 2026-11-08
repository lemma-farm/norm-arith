module
public import Examples.vltanh__lean4_ambidextrous_sofa.Dependencies.ve2c0fc6bb439.AmbidextrousSofa.ExactConstant
set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
@[expose] public section
/-!
# An elementary Dirichlet energy estimate

For a function vanishing at both endpoints, Cauchy--Schwarz on the two
subintervals gives the pointwise weight `t * (L - t) / L`. Its integral
yields the constant `L² / 6`. At `L = π / 2` this is already sufficient
for strict fixed-width concavity of the adaptive functional; a sharp
Poincaré constant is unnecessary.

The hypotheses retain actual derivatives and square integrability. No
existence, maximization, or sofa-area conclusion is assumed.
-/
noncomputable section
open Set MeasureTheory
namespace AmbidextrousSofa.Analysis
theorem integral_quadratic_tail_kernel (a b : ℝ) :
    (∫ t in a..b, (t - a) * (b - t)) = (b - a) ^ 3 / 6 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => (b - a) * (t - a) ^ 2 / 2 - (t - a) ^ 3 / 3)
      ((x - a) * (b - x)) x := by
    have hx := (hasDerivAt_id' x).sub_const a
    convert (((hx.pow 2).const_mul (b - a)).div_const 2).sub ((hx.pow 3).div_const 3) using 1
    push_cast
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    ((by fun_prop : Continuous fun t : ℝ => (t - a) * (b - t)).intervalIntegrable a b)]
  ring
end AmbidextrousSofa.Analysis
