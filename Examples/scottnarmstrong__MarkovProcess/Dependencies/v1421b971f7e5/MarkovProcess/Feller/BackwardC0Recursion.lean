/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Feller.FiniteTimeKernelContinuity
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.Kernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Backward `C₀` recursion for finite Feller transitions

An ordered nonempty family of one-coordinate `C₀` factors determines a backward semigroup
recursion: evolve the last factors relative to the first time, multiply by the first factor, and
then evolve from the starting state to the first time.  The recursion varies continuously in the
`C₀` norm when every ordered observation time converges.

This file contains only the analytic recursion and its continuity.  Its identification with an
integral against a finite-time kernel is in `Feller/BackwardC0Integral.lean`; no statement about
path space is proved here.
-/
open Filter Topology
open scoped NNReal ZeroAtInfty
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
end SubMarkovKernelSemigroup
end MarkovProcess
