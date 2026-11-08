-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLpKernel
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLpExponents
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Euclidean.PotentialLocalLpMeasure
set_option autoImplicit false
set_option warningAsError true
/-!
# Local `L^{3/2}` bounds for Newtonian potentials of compactly supported data

The Newtonian representation `ext:newtonian` of the paper writes the local pressure as a sum of
Newtonian potentials `N * g` and first-derivative potentials `∂ⱼN * g` of compactly supported
data `g`.  The Liouville step needs each of these to be `L^{3/2}` on every ball of
three-dimensional space.

This file supplies the *near-field* half of that statement: Young's inequality on a ball, with
the kernel truncated at the radius `R + ρ` beyond which it cannot be seen by data supported in
the closed ball of radius `R`.

## Exponent arithmetic

Young's inequality `1 + 1/r = 1/q + 1/s` with target `r = 3/2` reads `1/q + 1/s = 5/3`.
The kernel `N` has the size `‖z‖⁻¹`, so its truncation lies in `L^s` exactly for `s < 3`; this
allows every `q ≥ 1`.  The kernel `∂ⱼN` has the size `‖z‖⁻²`, so its truncation lies in `L^s`
exactly for `s < 3/2`; this allows exactly `q > 1`.  Both ranges contain the symmetric choice
`q = s = 6/5`, which is the Young instance available as
`eLpNorm_scalarConvolution_six_fifths_three_halves`.  Since the data is compactly supported,
`L^q ⊆ L^{6/5}` for every `q ≥ 6/5`, so all the estimates below are routed through `q = 6/5`
and therefore cover every exponent `q ≥ 6/5`; in particular `q = 3/2` and the exponents
`q > 5/2` of `def:sws`.
-/
open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat
set_option autoImplicit false
noncomputable section
namespace CKN.Foundation.Euclidean
open CKN
/-! ### A measurable representative supported in the same ball

The force datum of a suitable weak solution is only almost everywhere strongly measurable, while
Young's inequality is stated for measurable data.  Replacing the datum by the indicator of the
support ball of a strongly measurable representative changes neither its `L^p` sizes nor any of
its Newtonian potentials. -/
end CKN.Foundation.Euclidean
