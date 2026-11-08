-- SPDX-License-Identifier: Apache-2.0
module
public import Examples.pmaronow__slowequilibration_palomar.Dependencies.vdd13bda0b125.SlowEquilibration.LogEnclosure
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Tactic.Positivity
set_option autoImplicit false
/-!
# The scalar strict one-step certificate for the degree 4 / degree 12 example

All parameters are the manuscript's actual logarithmic parameters. The
first-variation function is defined by its interval integral, rather than by
assuming the contact equations or its sign.
-/
@[expose] public section
namespace SlowEquilibration.NonconvexCertificate
open MeasureTheory Set Filter
open Certificate LogEnclosure
noncomputable section
abbrev t : ℝ := exampleParameter
def Q : ℝ := 9 / 10
def x : ℝ := 5 / 9
def C : ℝ := 3 / 5
def b : ℝ := t * (10 / 9 : ℝ) ^ 8
def betaSq : ℝ := 15 / (Q ^ 3 * (4 + 12 * t))
def xi (r : ℝ) : ℝ := r ^ 4 + b * r ^ 12
def xHat (r : ℝ) : ℝ := if r ≤ Q then C - x * r else 1 - r
def V (r : ℝ) : ℝ := (∫ v in (0 : ℝ)..r, (r - v) / (xHat v) ^ 2) - betaSq * xi r
end
end SlowEquilibration.NonconvexCertificate
