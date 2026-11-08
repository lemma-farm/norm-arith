/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module
public import Examples.shaikidris__kkp_asymptotic_spectral_bound.Dependencies.v273bec15eda8.BN.Basic.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Topology.Instances.Matrix
@[expose] public section
/-!
# Nonnegative Perron vector for a symmetric nonnegative matrix

A real symmetric entrywise-nonnegative matrix has a nonnegative unit maximizer of the
Rayleigh quotient, and that maximizer is an eigenvector for `lambdaMax`.
-/
namespace BN
open Matrix Module.End Metric WithLp
open scoped InnerProductSpace
set_option linter.unusedSectionVars false
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {B : Matrix n n ℝ}
end BN
