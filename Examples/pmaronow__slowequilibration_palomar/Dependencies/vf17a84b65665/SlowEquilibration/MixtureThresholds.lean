-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.MixtureCurvature
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vf17a84b65665.SlowEquilibration.Thresholds
set_option autoImplicit false
@[expose] public section
/-!
# Threshold calculus for canonical finite mixtures

Instantiates the scalar threshold theorems for the actual covariance polynomial
of every canonical finite nonzero mixture. In particular, the threshold ordering
requires no unverified mixture regularity or boundedness premise.
-/
namespace SlowEquilibration.FiniteMixture
variable (μ : FiniteMixture)
end SlowEquilibration.FiniteMixture
