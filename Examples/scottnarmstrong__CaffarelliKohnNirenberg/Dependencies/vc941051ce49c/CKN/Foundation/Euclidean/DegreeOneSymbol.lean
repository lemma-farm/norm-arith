-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.vc941051ce49c.CKN.Foundation.Parabolic.Vec3Norm
set_option autoImplicit false
set_option warningAsError true
/-!
# Symbols homogeneous of degree one

External Input `ext:heat-kernel` of `paper/ckn.tex` quantifies over every Fourier
multiplier `ς(D)` whose symbol `ς` is smooth on `ℝ³ ∖ {0}` and homogeneous of
degree one, and the manuscript's pressure-multiplier discussion uses the concrete symbols
`ς_{jl}(ξ) = i ξ ξ_j ξ_l / |ξ|²` of that class.  This file records the
homogeneity predicate for such a symbol and proves the linear growth bound
`‖ς ξ‖ ≤ C |ξ|` that makes the associated Fourier integrals absolutely
convergent.  Symbols are complex valued, as `ς_{jl}` is.
-/
open scoped BigOperators
open Set
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN.Foundation.Parabolic
end CKN.Foundation.Euclidean
