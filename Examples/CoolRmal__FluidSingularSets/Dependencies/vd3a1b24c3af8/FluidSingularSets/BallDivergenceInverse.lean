-- Copyright (c) 2026 FluidSingularSets contributors.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.FluidSingularSets.DenseHilbertLifts
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.FluidSingularSets.PolynomialBallMeanDensity
public import Examples.CoolRmal__FluidSingularSets.Dependencies.vd3a1b24c3af8.FluidSingularSets.PolynomialBallRellich
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
/-!
# The actual bounded ball divergence inverse

Mean-zero coordinate polynomials are dense in the actual mean-zero ball L²
space. Their genuine zero-boundary energy inverses satisfy a degree-independent
bound. Kernel-orthogonal linear extension therefore constructs a bounded
right inverse on all mean-zero square-integrable ball data.
-/
@[expose] public section
open MeasureTheory Set CKN
open CKN.Foundation.Parabolic
open scoped ENNReal Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FluidSingularSets
end FluidSingularSets
