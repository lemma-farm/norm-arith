module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vec5f25f17267.HypoellipticAleksandrov.Parabolic.Dirichlet.TimeDistribution
public import Mathlib
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Reverse-time distributional derivative kernel

This module proves that an integrable scalar function on the literal
reverse-time interval with vanishing pairings against all test derivatives is
almost everywhere constant.
-/
@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.Dirichlet
open Function MeasureTheory Set
open scoped ENNReal Interval
end HypoellipticAleksandrov.Parabolic.Dirichlet
