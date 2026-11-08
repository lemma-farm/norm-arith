-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Core.Caccioppoli.Conversions
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Setting.Finiteness
import Mathlib.MeasureTheory.Function.L1Space.Integrable
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# Slice norm bounds

This module formalizes paper equation `eq:slice-norm-bounds` of `paper/ckn.tex`.
The five dimensionless scale quantities `alpha`, `beta`, `gamma`, `delta` and
`lambda` are defined in `CKN/Statements/*.lean` by normalizing a nonnegative
space-time integral by a power of the radius; `eq:slice-norm-bounds` is the
inverse reading of those definitions, expressing the unnormalized slice
integrals directly in terms of the scale quantities:

* the time-slice energy essential supremum of `u` is `r * α(z,r)²`,
* the Dirichlet energy `∬_{Q_r} |∇u|²` is `r * β(z,r)²`,
* the pressure integral `∬_{Q_r} |p|^{3/2}` is `r² * δ(z,r)³`,
* the force integral `∬_{Q_r} |f|^q` is `(r^{5/q-3} λ(z,r))^q`, where
  `σ = 3 - 5/q` is the exponent of `paper/ckn.tex` equation `eq:lambda`.

The definitions pass the underlying `ℝ≥0∞` integral to `ℝ≥0` with
`ENNReal.toReal`, so each identity requires the relevant integral at radius `r`
to be finite; this is the `hfin` hypothesis below, discharged for suitable weak
solutions by the finiteness lemmas of `CKN/Setting/Finiteness.lean`.

Each identity is stated twice: as an identity of `ℝ≥0∞` integrals, and as an
identity of Bochner set integrals for the (nonnegative) real density, using the
conversion `setIntegral_eq_toReal_setLIntegral_of_nonneg` of
`CKN/Core/Caccioppoli/Conversions.lean`.
-/
/-! ### Nonnegativity of the densities -/
end CKN
