-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Section3.JMNRegularity
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Section3.CorrectorBounds
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Infra.Cutoff.DerivativeBounds
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section3.KMat
public import Examples.scottnarmstrong__AVAnomalousDiffusion.Dependencies.v3ba1c53355bd.AVenhance.Statements.Section3.JHat
public import Mathlib
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
set_option autoImplicit false
set_option linter.deprecated true
set_option linter.unnecessarySimpa true
set_option linter.unusedSectionVars true
set_option linter.unusedSimpArgs true
set_option linter.unusedVariables true
set_option relaxedAutoImplicit false
/-! Explicit cutoff factors in the Section 3 coefficient estimates.

The cutoff derivative budget is `Nstar β`; derivative estimates of a product
containing `∂ⁿζ` therefore require `n + ℓ ≤ Nstar β`. Constants are displayed
rather than hidden in a β-dependent `C`. The memory integrals are differentiated
on a fixed half-line after translation, with an integrable exponential
majorant for every derivative. The matrix estimates include order zero and
all orders through `Nstar β`; the physical diffusivity comparison is conditional
on the internal-index κ bounds from the diffusivity-recursion estimates.
-/
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section3
open AVenhance
end AVenhance.Infra.Section3
