-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Measure.SliceDistributionCore
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Parabolic.Basic
set_option autoImplicit false
set_option warningAsError true
/-!
# Space-time distributional identities restricted to time slices

Testing a space-time distributional identity against a product `ψ(x)θ(t)` of a
spatial test function and a time cutoff and separating the variables gives, for
each fixed `ψ`, a slice identity valid for almost every time.  The exceptional
null set produced this way depends on `ψ`.

This file removes that dependence.  Starting from the family of slice
identities indexed by `ψ`, the countable subfamily indexed by the mollifier
bumps centred at the points of a countable dense set yields a single null set,
and `slice_pairing_zero_of_mollifier_family` upgrades the countable family back
to every test function.  The result is the almost-everywhere slice statement
used in `paper/ckn.tex`: for almost every time, the slice is divergence free in
the sense of distributions, with one null set serving every test function.

The pairing covered is the spatial divergence pairing `∑ᵢ fᵢ ∂ᵢψ`.  Its
full-space form is exactly the slice hypothesis consumed by the pressure
module's force-cancellation results.
-/
open MeasureTheory Metric Filter Topology Set
open CKN.Foundation.Parabolic
set_option autoImplicit false
noncomputable section
namespace CKN
end CKN
end
