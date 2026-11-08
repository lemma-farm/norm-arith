-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Parabolic.Basic
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Sobolev.Ambient.Basis
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Foundation.Sobolev.Measure.RestrictedVolume
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
/-- The `i`th spatial partial derivative `∂_i f`, as the Fréchet derivative applied
to the `i`th coordinate basis vector. -/
def spatialDeriv (f : Vec3 → ℝ) (i : Fin 3) : Vec3 → ℝ :=
  fun x => (fderiv ℝ f x) (basisVec i)
/-- The spatial Laplacian `Δ f = ∑_i ∂_i ∂_i f`. -/
def spatialLaplacian (f : Vec3 → ℝ) : Vec3 → ℝ :=
  fun x => ∑ i : Fin 3, spatialDeriv (spatialDeriv f i) i x
/-- The Euclidean gradient pairing `∇f · ∇g = ∑_i ∂_i f ∂_i g`. -/
def spatialGradDot (f g : Vec3 → ℝ) : Vec3 → ℝ :=
  fun x => ∑ i : Fin 3, spatialDeriv f i x * spatialDeriv g i x
/-- The mixed second derivative `∂_i ∂_j f`. -/
def mixedSecond (f : Vec3 → ℝ) (i j : Fin 3) : Vec3 → ℝ :=
  fun x => spatialDeriv (spatialDeriv f j) i x
end
end CKN
