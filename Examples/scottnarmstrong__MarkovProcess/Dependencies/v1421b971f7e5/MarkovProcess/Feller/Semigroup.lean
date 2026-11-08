/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Kernel.C0
import Examples.scottnarmstrong__MarkovProcess.Dependencies.v1421b971f7e5.MarkovProcess.Semigroup.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# Strongly continuous `C₀` semigroups from kernels

This file isolates continuity in time as an explicit hypothesis on the `C₀` kernel operators and
packages those operators as a strongly continuous contraction semigroup. Spatial preservation of
`C₀`, continuity of its time orbits, and conservativity of the kernels remain separate properties.
No stochastic process or Hunt process is constructed here.
-/
open Topology
open scoped ZeroAtInfty
namespace MarkovProcess
namespace SubMarkovKernelSemigroup
variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
variable (P : SubMarkovKernelSemigroup α) (hC0 : P.MapsC0)
section Feller
variable [LocallyCompactSpace α] [T2Space α]
end Feller
end SubMarkovKernelSemigroup
end MarkovProcess
