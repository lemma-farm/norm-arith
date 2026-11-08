/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Examples.cenozoic_works__rhone_theory.Dependencies.v9a411977d6de.Rhone.Statistics.DependenceBudget.Transfer
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option warningAsError true
/-! # Finite iid experiments for the paired tests -/
@[expose] public section
open scoped BigOperators
namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]
end Rhone.Statistics.DependentPairedTest
