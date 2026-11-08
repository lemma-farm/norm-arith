-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Sobolev.Ambient.Basis
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Sobolev.Measure.RestrictedVolume
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option autoImplicit false
set_option warningAsError true
/-!
# The Leibniz rule for the spatial Laplacian, in weak form

The paper's identity `eq:leibniz-lap`,
`Δ(η T) = η Δ T + 2 ∂_j η ∂_j T + T Δ η`,
is stated there for a scalar distribution `T` and a smooth `η`.  This file
proves the underlying pointwise second-order product rule for smooth functions
on `Vec3 := Fin 3 → ℝ`, and then integrates it against a locally integrable
weight to obtain the weak (test-function) form used in the paper.

Spatial partial derivatives are ordinary partial derivatives, expressed as the
Fréchet derivative applied to a coordinate basis vector, matching the
convention of `CKN.spatialPartial`.
-/
open MeasureTheory Set
open CKN.Foundation.Parabolic
namespace CKN
noncomputable section
/-! ## Spatial partial derivatives and their product rules -/
end
end CKN
