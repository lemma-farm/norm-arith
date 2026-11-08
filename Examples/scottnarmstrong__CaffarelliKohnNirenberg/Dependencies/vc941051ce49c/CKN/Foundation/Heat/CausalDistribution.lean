-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Heat.Integrability
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Topology
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.Support
set_option autoImplicit false
set_option warningAsError true
/-!
# The causal heat kernel as a distribution

External Input `ext:heat-kernel` of `paper/ckn.tex` states that
`W₊(t,x) = 1_{t>0}(4πt)^{-3/2}e^{-|x|²/(4t)}` is locally integrable on
`ℝ³ × ℝ`, is supported in `{t ≥ 0}`, and satisfies `(∂_t - Δ)W₊ = δ_{(0,0)}`
in `𝒟'(ℝ³ × ℝ)`.  Writing that identity requires a distribution carrier for
`W₊`.  This file supplies it: the established local integrability of
`heatKernelPlus`, stated for the ordinary product topology on `Vec3 × ℝ` rather
than the parabolic one, the induced distribution, its action on every test
function, and its causal support.

The fundamental-solution identity itself is the content of the external input
and is not proved here.
-/
open scoped BigOperators Distributions
open Set MeasureTheory
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Heat
open CKN.Foundation.Parabolic
end CKN.Foundation.Heat
