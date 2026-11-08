-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.DecompositionPotentials
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# Support and integrability of the eight cut-off pressure sources

The paper's pressure representation `prop:pressure-decomposition` writes the
localized pressure `η p` as a remainder `p₁` plus the eight source potentials
`p₂, …, p₈` (`eq:p1-bound`, `eq:p234-bound`, `eq:p56-bound`, `eq:p78-bound`).
Each of those potentials is a Newtonian or Newtonian-derivative potential of an
integrand built from the cut-off `η`, the velocity `u`, the pressure `p` and the
force `f`, evaluated on the time slice `t = s`.

This file records the bookkeeping needed to feed those potentials into the
potential calculus: that the spatial derivatives and the spatial Laplacian of a
cut-off are again supported in the cut-off's support (and hence compactly
supported), a general criterion turning an integrability hypothesis on a set
`K` into global integrability of a product with a smooth function supported in
`K`, and the resulting integrability and compact-support statements for the
eight source integrands.

The eight source integrands are, in the order used below,

* `η · p` (remainder/`p₁` slot, `eq:p1-bound`),
* `∂ᵢ∂ⱼη · Uᵢⱼ`, `Uᵢⱼ · ∂ᵢη`, `Uᵢⱼ · ∂ⱼη` (`p₂`, `p₃`, `p₄`, `eq:p234-bound`),
* `p · Δη`, `∂ⱼη · p` (`p₅`, `p₆`, `eq:p56-bound`),
* `η · fⱼ`, `∂ⱼη · fⱼ` (`p₇`, `p₈`, `eq:p78-bound`),

where `Uᵢⱼ = pressureUTensor u c (·, s) i j`.
-/
/-! ## Support of the spatial derivatives of a cut-off -/
end CKN
end
