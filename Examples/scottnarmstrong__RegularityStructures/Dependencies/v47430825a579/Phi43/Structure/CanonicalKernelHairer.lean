/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Structure.CanonicalModelData
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Causal
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.RegularityStructures.Analysis.Heat.Kernel
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The truncated Hairer kernel in the canonical lift

For `N`, the singular part of Hairer's causal kernel is the actual function
`K_N = ∑ n, annShellC N n`.  This module installs that kernel in the finite
canonical data used by `CanonicalModelData`: convolution is convolution by
`K_N`, and the Taylor data are, by definition, the value and spatial gradient
of that convolution.  The pointwise decomposition is Hairer [Hai14, Lemma 5.5]
and the Taylor convention is [Hai14, (5.12), (8.20)].

The analytic convergence and model estimates are deliberately kept separate:
the annShell decomposition supplies the exact singular kernel here, while the
abstract Schauder layer supplies the pairing estimates for Q-distributions.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
open RegularityStructures
local notation "E" => ParabolicSpace
/-- The singular kernel obtained from Hairer's polynomial-annihilating shells. -/
def hairerKernel (N : ℕ) (z : E) : ℝ := ∑' n : ℕ, annShellC N n z
end RegularityStructures.Phi43
end
