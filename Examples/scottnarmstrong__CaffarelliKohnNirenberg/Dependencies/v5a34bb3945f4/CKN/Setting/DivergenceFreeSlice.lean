-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Statements.SuitableWeakSolutionIntegrable
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v5a34bb3945f4.CKN.Foundation.Parabolic.Topology
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable
set_option autoImplicit false
set_option warningAsError true
/-!
# The divergence-free condition on time slices

This file formalizes the Fubini reduction behind `lem:divfree-slice` and `eq:divfree-ae`
of `paper/ckn.tex`.  Clause (S2) of `def:sws` pairs the solution against the space-time
test functions `∫ Σᵢ uᵢ ∂ᵢψ`.  Testing with a product `ψ₀(x)θ(t)` of a spatial test
function `ψ₀ ∈ C_c^∞(Ω)` and a time cutoff `θ ∈ C_c^∞(I)`, then applying Fubini,
separates the time variable and shows that

  `∫_Ω Σᵢ uᵢ(x,s) ∂ᵢψ₀(x) dx = 0`

for almost every `s ∈ I`.  The null set a priori depends on `ψ₀`; obtaining one common
null set requires a countable `C¹`-dense family of test functions and is not formalized
here.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
/-! ## The product test function -/
end CKN
