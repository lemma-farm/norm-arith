-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
import Examples.scottnarmstrong__CaffarelliKohnNirenberg.Dependencies.v49e63fd1c585.CKN.Foundation.Sobolev.Mollify.Basic
import Mathlib.Topology.MetricSpace.Thickening
set_option autoImplicit false
set_option warningAsError true
/-!
# Pointwise bounds and support for normalized mollifications

Elementary stability properties of the normalized `ContDiffBump` mollification used
throughout the Caffarelli–Kohn–Nirenberg argument.

* `abs_mollify_le`: a uniform pointwise bound is preserved by mollification.
* `support_mollify_subset`: mollification does not spread the support of a function
  beyond the closed `ε`-neighbourhood of its topological support.
-/
open MeasureTheory Metric
namespace CKN
set_option autoImplicit false
noncomputable section
end
end CKN
