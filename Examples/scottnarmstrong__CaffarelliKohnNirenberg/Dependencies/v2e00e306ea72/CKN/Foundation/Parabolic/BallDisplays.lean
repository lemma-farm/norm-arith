-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v2e00e306ea72.CKN.Foundation.Parabolic.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
set_option autoImplicit false
set_option warningAsError true
/-!
# The parabolic ball and its volume

This file records the literal displays of `paper/ckn.tex` that describe the
open parabolic ball `𝔅_r(z)` of the metric `dpar` (equation
`eq:parabolic-ball` and Lemma `lem:parabolic-metric`):

* `𝔅_r(z) = B_r(x) × (t - r², t + r²)` for `z = (x, t)`;
* `C_r(z) ⊆ 𝔅_r(z)` and `𝔅_r(z) ⊆ C_{2r}(x, t + r²)`, where `C_r(z)` is the
  parabolic cylinder `B_r(x) × (t - r², t]`;
* `|𝔅_r(z)| = (8π/3) r⁵`.

The spatial ball `vec3Ball x r` uses the Euclidean norm on `Fin 3 → ℝ`
(`vec3EuclideanNorm`), so its volume is computed by transporting Mathlib's
volume of the Euclidean ball in `EuclideanSpace ℝ (Fin 3)` along the
measure-preserving equivalence `WithLp.toLp 2`.
-/
open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Parabolic
end CKN.Foundation.Parabolic
