/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.DiscreteConvolution
public import Examples.scottnarmstrong__Critical2DKPZ.Dependencies.v7f4d42540cee.Critical2DKPZ.WalkTails.Hypergeometric
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! # Log-concavity and finite walk-law convolution

Repeated convolution with the coefficient sequence of `1+x` gives the binomial coefficients.
Nonnegative Toeplitz minors are preserved by this convolution and imply log-concavity of the
squared-binomial laws.
-/
@[expose] public section
noncomputable section
namespace Critical2DKPZ.WalkTails
def hypergeometricIntWeight (m : ℕ) (z : ℤ) : ℝ :=
  (LatticeProb.binomZ m z) ^ 2 / (Nat.choose (2 * m) m : ℝ)
theorem hypergeometricIntWeight_eq_nat (m j : ℕ) :
    hypergeometricIntWeight m (j : ℤ) = hypergeometricWeight m j := by
  rw [hypergeometricIntWeight, LatticeProb.binomZ_natCast]
  rfl
end Critical2DKPZ.WalkTails
end
