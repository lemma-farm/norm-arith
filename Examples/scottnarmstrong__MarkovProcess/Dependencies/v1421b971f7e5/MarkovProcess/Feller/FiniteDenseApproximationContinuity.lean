/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Feller.FiniteTimeCompactTestContinuity
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Time.FiniteDenseApproximationOrdered
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.FiniteTime.FiniteSetKernelCompactTestTransport
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Feller continuity of finite dense approximations

This file proves compact-test convergence of the finite laws obtained by simultaneously
approximating a finite set of nonnegative-real times by dense times. Both the approximating and
limiting kernels are transported through the same ordered-coordinate homeomorphism, after which
the finite-time Feller continuity theorem applies directly.

This is finite-dimensional infrastructure. No path-space Markov property is asserted here; the
Markov and strong Markov statements are in `MarkovProcess/Main.lean`.
-/
open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal CompactlySupported
namespace MarkovProcess.SubMarkovKernelSemigroup
variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
end MarkovProcess.SubMarkovKernelSemigroup
