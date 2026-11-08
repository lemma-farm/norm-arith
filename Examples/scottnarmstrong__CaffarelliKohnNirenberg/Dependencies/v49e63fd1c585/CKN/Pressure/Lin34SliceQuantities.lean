-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceForceCylinder
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceFubini
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SliceMeanFree
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Pressure.Lin34SlicePointwise
set_option autoImplicit false
set_option warningAsError true
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration
set_option autoImplicit false
noncomputable section
namespace CKN
/-!
# The four time-slice quantities of `prop:lin34`

The integrated estimate `eq:lin35-force` of `paper/ckn.tex` is obtained by
integrating `eq:lin34-pointwise` over `J_ρ = (t₀ - ρ², t₀)`.  This file names
the four functions of time that appear in that integration, proves that they
are integrable on `J_ρ`, and identifies their integrals with the cylinder
quantities `D(z₀, r)` and `D(z₀, ρ)` of `eq:ABCDE`, and `Ĉ(z₀, ρ)` of `eq:Chat`.
-/
end CKN
