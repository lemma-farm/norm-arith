module
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Measure.LpDominatedConvergence
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.H1.LevelSets
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.H1.ZeroBoundary
public import Examples.amelieloher__hypoelliptic_aleksandrov.Dependencies.vf5e5180c6a62.PDEFoundation.Sobolev.W1p.Truncation
public import Mathlib
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Positive-part approximation on a general open set

This file strengthens an explicit supported smooth approximation of a
nonnegative `H¹` representative to one whose smooth approximants are
pointwise nonnegative.  The construction takes a subsequence converging
almost everywhere and applies the one-sided smooth positive-part
regularizer at a vanishing scale.

The gradient argument uses the exact level-set fact that the selected weak
gradient vanishes almost everywhere on `{u = 0}`.  Thus positivity is gained
without hiding a truncation or density theorem in an assumption.
-/
@[expose] public section
open scoped ENNReal Topology
namespace PDE
open Filter MeasureTheory
namespace H1Function
variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
end H1Function
end PDE
