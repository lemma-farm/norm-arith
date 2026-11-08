/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Constants
public import Examples.scottnarmstrong__RegularityStructures.Dependencies.v47430825a579.Phi43.Structure.CanonicalKernelHairer
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-!
# The truncated-kernel versions of `C₁` and `C₂`

This file fixes the convention used for the comparison of the constants in Section 7 of the
statement.  Hairer's causal kernel is first periodised in the spatial
variables, and then mollified with the same periodised parabolic mollifier as the massive
kernel.  We use the causal `annShellC` construction, which is the kernel used by the abstract
fixed-point layer; the separate noncausal `annShell` construction is not identified
with it.  Thus the definitions below are literal torus versions of Hairer (10.33) and (10.41).

The support convention of the statement is that the support of `K` has parabolic radius
less than `1/4`; under that convention its spatial periodisation is the kernel used below.
The present file records the definitions and algebraic identities.  The uniform estimates needed
for the comparison are proved in the later `ConstantsComparison*` modules.
-/
@[expose] public noncomputable section
open MeasureTheory
namespace RegularityStructures.Phi43
/-- Spatial periodisation of Hairer's Euclidean singular kernel. -/
def hairerKernelTorus (N : ℕ) (z : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ,
    hairerKernel N (z.1, torusRep z.2 + fun i => (k i : ℝ))
/-- The mollification of `hairerKernelTorus N` by `ρ_ε^♯`. -/
def hairerMollifiedKernel (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (z : SpaceTime) : ℝ :=
  ∫ w, hairerKernelTorus N (z - w) * periodise ρ ε w
/-- The covariance formed from the mollified Hairer kernel. -/
def hairerCovariance (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ)
    (z : SpaceTime) : ℝ :=
  ∫ w, hairerMollifiedKernel N ρ ε (z + w) * hairerMollifiedKernel N ρ ε w
/-- Hairer's first renormalisation constant, (10.33), with the torus-periodised `K`. -/
def hairerWickConstant (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ∫ z, hairerMollifiedKernel N ρ ε z ^ 2
end RegularityStructures.Phi43
end
