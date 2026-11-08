module
/-
Copyright (c) 2026.
Released under Apache 2.0 license.

The elementary major/minor-arc decomposition in this file is adapted from
Gershon Bialer's `ternary-goldbach-lean`, in particular
`MathExtras.NumberTheory.Vinogradov.CircleMethod` and
`Math.Problems.TernaryGoldbach.CircleMethodDecomposition.Core`
(Apache-2.0).  The cubic scaling and arbitrary-power integrand are specific
to the Cook--Magyar specialization developed here.
-/
public import Examples.nihargargava__systole_bound.Dependencies.v202de269f286.CookMagyar.CircleMethod
public import Mathlib.Analysis.Normed.Group.AddCircle
@[expose] public section
open MeasureTheory
namespace SystolicGrowth
namespace CookMagyarArcs
open CookMagyarCircle
/-! # Major and minor arcs for the cubic Cook--Magyar sum

For a cutoff `Q`, the major-arc centers are the reduced fractions `a / q`
with `0 <= a < q <= Q`.  At cubic scale `N`, each arc has radius
`Q / N^3`, as in the one-equation specialization of Cook--Magyar.  All arcs
are clipped to the fixed fundamental interval `[0, 1]`; the minor arcs are
the relative complement there.

This file only establishes the exact decomposition and its elementary
analytic prerequisites.  Estimates on the two pieces belong in subsequent
modules.
-/
noncomputable def rationalCenter (a q : ℕ) : ℝ :=
  (a : ℝ) / (q : ℝ)
end CookMagyarArcs
end SystolicGrowth
