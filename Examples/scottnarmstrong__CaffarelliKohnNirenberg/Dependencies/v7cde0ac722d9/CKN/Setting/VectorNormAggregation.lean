-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v7cde0ac722d9.CKN.Setting.VectorInequalities
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# Aggregation of componentwise vector inequalities to the Euclidean norm

The Poincare and `H¹` interpolation inequalities of `CKN.Setting.VectorInequalities` are
stated componentwise: each coordinate `u_i` of a velocity field `u : Vec3 → Vec3` is
controlled by the scalar theorems.  The estimates of `paper/ckn.tex` instead use the
Euclidean norm `|u|` and the Frobenius norm of the spatial gradient,
`|∇u|² = spatialGradientSq`.  This file supplies the finite-dimensional norm comparisons
that turn the componentwise statements into their Euclidean counterparts.

The two elementary inequalities on `ℝ³` are

* `|u|^p ≤ 3^{max(0,p/2-1)} Σ_i |u_i|^p` (the sharp comparison of the Euclidean norm
  with the component `ℓᵖ` mass), and
* `Σ_i |u_i|^p ≤ 3 |u|^p`.

Both are proved pointwise and then integrated, first on the `ℝ≥0∞` side (the form in which
the scale quantities `γ`, `α`, `β` store their local `Lᵖ` masses) and then for the
spatial balls used by the Poincare and Sobolev statements.
-/
/-! ### Pointwise comparison on `ℝ³` -/
end CKN
